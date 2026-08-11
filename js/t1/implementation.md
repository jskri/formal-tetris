# implementation.md — ImplementationInstructions for T1

Per-model instructions for the transformation

```
FormalModel (T1.v)  ×  ImplementationInstructions (this file)
      ── rocq-to-js skill ──▶  Code (model.js, view.js, controller.js, instance.js, index.html)
                             ×  Proofs (proofs.md)  ×  Tests (tests/)
```

`rocq-to-js.md` is the **generic process**; this file is the **T1-specific source of
truth**. Generated artifacts are never hand-edited: to change an artifact, change
this file or `T1.v` and regenerate. All references to `T1.v` are **by definition
name**, so renaming/reordering in the model is caught by the coverage check (§10),
not silently mismatched line numbers.

## 0. Inputs, outputs, and what is frozen

Codegen-time inputs (this transformation):
- `T1.v` — the abstract model (parameters left abstract). Grids are boxed: a `Grid`
  carries its own `HW`/`YX` (height/width, origin), and `⊆`/`∩`/`∪`/`⊕`/`Full`/`∅`
  are the algebra over them (§4).
- this file.
- `rocq-to-js.md` — generic rules (cited as "skill §x").
- `T1JsBounds.v` — the machine-checked ℤ-side bounds/envelope facts (referenced by
  `proofs.md` §6; not consumed by codegen, but its lemma names are cited).

Runtime input (NOT codegen-time, NOT derived from `T1.v`):
- `instance.js` — the concrete instantiation of the abstract parameters (§13).

Outputs: `model.js`, `view.js`, `controller.js`, `instance.js`, `index.html`, `proofs.md`,
`tests/` (§9). A generation is **correct** iff `model.js` refines `T1.v` (established by
`proofs.md`); the acceptance oracle (§10) is the operational check that provides evidence
for this, it is not itself the definition. **Byte-identity is not required**, behavioural
equivalence up to the fixed naming map is.

## 1. Frozen decisions (decision register)

| id  | decision | rationale |
|-----|----------|-----------|
| D1  | Grids are `boolean[][]`, row-major, `g[y][x]`, `H g = g.length`, `W g = g[0].length`. **Exception:** `mg` and `RotGrid`'s output are `(false \| Piece)[][]`, not plain `boolean[][]` — `false` is the sole empty sentinel; any occupied cell carries the piece id occupying it, so fixed blocks render in their own color instead of collapsing to a flag. `occ(c) = c !== false` is the one predicate every cell-truth test in `model.js` goes through, so this widening changes no boolean-grid semantics (`ForbiddenGrid` and idiom (4)'s `Full`/`∅` stay plain `boolean[][]`, unaffected). | skill table; renderable; colored-blocks decision |
| D2  | `FilterFullLines` is **not** emitted; `ClearFullLines` is translated as a unit (filter non-full rows, pad empties on top), always at the array's own index `0` (justified by D-invariant below, not assumed). | skill N10; `T1.v`'s `Y g = 0` invariant, see D-reach below |
| D-reach | Every grid `ClearFullLines`/`FullLineCount`/`IsFullLineb` is called on at runtime (`this.mg`, and `FixPiece`'s `u`/`mg2`) has Rocq origin `Y = X = 0`: `TypeOK` pins `YX(mg) = YX(InitialMainGrid) = (0,0)`, and `BoxUnionClamp`/`ClearFullLinesBox` (`T1Proofs.v`) show the clamp and the clearing step each preserve `YX`. This is what lets every loop below stay `0`-based despite `T1.v`'s `FilterFullLines`/`FullLineCountImpl` taking an abstract starting coordinate. | `T1Proofs.v`: `BoxUnionClamp`, `ClearFullLinesBox` |
| D3  | Orientation: `y = 0` is the **bottom**; gravity decreases `y` (`MovePiece (-1,0)`). Renderer flips; engine does not. | `FallStep` |
| D4  | Rocq math `mod` → `mod(a,n)` helper; never `%`. Only site: `RotatePiece`. | skill §4a |
| D5  | Non-determinism is an **explicit method argument** (`fixPiece(pNew)`, `fallStep(pNew)`), mirroring `FixPiece`/`FallStep`'s `p_new : Piece`. No callback. | skill N9; faithful to spec |
| D6  | First piece is a **constructor argument**: `new Machine(p0)`. | matches `Init p` |
| D7  | Invariant re-checks run under `CHECK_INVARIANTS` (module const, default `false`). `typeOK` is the highest-value one. | skill N4/§4c |
| D8  | Set-parameter elements (`Piece`) must be **value-`===`** (primitives), disjoint from `false` (the sole `occ()` sentinel, since `mg` stores `Piece` ids directly as cell contents — D1), and the array a **complete, finite** enumeration; `RotGrid`/`InitialY`/`InitialX` pure. Asserted in `checkAxioms`. | skill N2/N6 |
| D9  | Guard-before-index everywhere; bounds conjuncts first; `negb→!`, `implb a b→!a||b`. | skill N1 |
| D10 | Integer-range safety via bound `B = max(HM,WM)+PW−1 ≤ MAX_SAFE_INTEGER`, asserted in `checkAxioms`; justified in `proofs.md §6` against `T1JsBounds.v`. | skill N5; `T1JsBounds.v` |
| D11 | Only safety/invariants are claimed to transfer; no liveness. | skill N8 |
| D12 | `W` is derived from `g[0].length`; sound because `typeOK ⇒ H>0`. Do not special-case empty grids. | skill N7 (`AxiomsInitialMainGrid` gives `H>0`) |
| D13 | **Fusion is mandatory.** Every occurrence of `⊆`, `∩`, `∪`, `⊕`, `Full`, `∅` in `T1.v` appears only inside one of four fixed idioms (§4). Each idiom is translated as a single location/content/emptiness test with no grid ever materialized for `Full`, `∅`, or an intermediate union-before-clamp; `⊕` is absorbed into the offset arithmetic of whichever idiom it sits inside. A literal, per-operator transliteration (build a `Full` array, build a union array, then compare) is never attempted — it would be slower and would reopen exactly the masking question D-Contained (below) closes for free. | skill N10-style fusion; `proofs.md` §3 |
| D14 | `Grid.YX`, `State.pyx`, `Move`'s `dyx`, and the parameter `InitialYX` are Rocq-level pairs, used only to state `⊕` uniformly. None surface as JS tuples: position/offset data is always two scalars (`py,px` / `dy,dx` / `InitialY(p),InitialX(p)`) at every JS boundary. | keeps `Machine`'s field shape and every call site unchanged from a flat-coordinate design |
| D15 | `ForbiddenGrid` is the only instantiated grid with non-`(0,0)` Rocq origin (`YX ForbiddenGrid = (FY,FX)`). It is represented in JS as an array *plus* two separate scalar exports `FY`, `FX` from `instance.js` — not bundled into one object — matching D1's array-only convention for grid *content*. Every other materialized grid (`InitialMainGrid`, `RotGrid p r`, and every reachable `mg`) has Rocq origin `(0,0)` by axiom or invariant (D-reach), so no other grid carries position scalars. | `AxiomsInitialMainGrid`'s `YX = (0,0)`; `AxiomsRotGrid`'s `YX gr = (0,0)` |
| D-Contained | `Contained` (`T1.v`) holds automatically for the α-image of any grid array (`boolean[][]` or the widened `(false\|Piece)[][]`, D1): the coercion `⟦g⟧` (`proofs.md` §2) *defines* `L` to be `false` outside `g`'s box, by construction of the coercion, not by inspecting `g`'s content. No runtime check is emitted for any `Contained` clause (`AxiomsRotGrid`, `AxiomsInitialMainGrid`, `AxiomsForbiddenGrid` each have one) — none can fail, for any well-shaped array. | `proofs.md` §2 |

## 2. File layout & module shape

```
instance.js            # concrete Tetris parameters (§13)
model.js               # T1 engine (generated from T1.v)
view.js                # renderer (§14)
controller.js           # controller / entry point (§15)
index.html             # shell: canvas + module bootstrap (§15)
proofs.md
tests/
  testInstance.js      # test fixture (not the runtime instance.js)
  model.unit.test.js
  model.properties.test.js
  model.fuzz.test.js
  oracle.js            # executable Rocq reference (see §9.4)
```

`lib/utils.js` (one level up, shared with T2) exports (alphabetical, pure, no closure over parameters):
- `mod(a, n)` — `((a % n) + n) % n`.
- `copyGrid(g)` — `g.map(r => r.slice())`.
- `emptyRow(w)` — `Array(w).fill(false)`.
- `emptyRows(n, w)` — `Array.from({length: n}, () => emptyRow(w))`.

`model.js` exports exactly one function:

```js
export function T(
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX,
  MAX_SAFE_INTEGER = Number.MAX_SAFE_INTEGER,      // D10
) { … return { /* see §5, §6 */ }; }
```

Parameter order tracks `T1.v`'s `Parameter` order (`Piece, InitialMainGrid,
ForbiddenGrid, RotGrid, InitialYX, PW`), decomposed at the boundary per D14/D15:
`InitialYX` → `InitialY, InitialX`; `ForbiddenGrid`'s Rocq-internal `YX` → the trailing
`FY, FX` scalars; then the bound (D10). The returned object exposes (in this order):
the free functions of §5, `checkAxioms`, `typeOK`, `checkInvariants`, `Machine`,
`snapshot`. `stutter` and `step` are **not generated** — they are Rocq proof
artifacts with no implementation obligation (the caller simply refrains from
calling any method).

Module-level in `model.js`: `const CHECK_INVARIANTS = false;` (D7) and the abbreviations
`const HM = InitialMainGrid.length, WM = InitialMainGrid[0].length, B = Math.max(HM,WM)+PW-1;`.
`MAX_SAFE_INTEGER` is the parameter (default `Number.MAX_SAFE_INTEGER`); used only in `checkAxioms` (D10).

## 3. Naming map (Rocq → JS), frozen

Rule: camelCase; keep a trailing `b` only on the boolean decider `isFullLineb`.
Props that exist only inside `Axiom`s become boolean checkers with the same name.
Grid-algebra operators (`⊆`,`∩`,`∪`,`⊕`,`Full`,`∅`,`Constant`,`InBox`,`OutsideBox`,
`Contained`) are never emitted as standalone functions (D13/D-Contained); they are
covered collectively by the fusion rule in §4, not individually below.

| Rocq | JS |
|------|----|
| `Grid`, `L`, `HW`/`YX`, `H`/`W`/`Y`/`X` | not emitted as such; realized as `boolean[][]` (D1) plus, for `ForbiddenGrid` only, the scalars `FY`/`FX` (D15) |
| `InBox`, `OutsideBox`, `Contained` | not emitted (D-Contained; fusion §4) |
| `GridInclude` (`⊆`), used bare (RHS not `Full _`) | `fullyContainedIn` (returns `boolean`) |
| `GridInclude` (`⊆`), used as `_ ⊆ Full _` | `occupiedInside` |
| `GridInclude` (`⊆`), used as `Full _ ⊆ Full _` | `bboxInsideBBox` |
| `GridIntersect` (`∩`), used as `_ ∩ _ ⊆/⊈ ∅` | `intersect` (returns `boolean`; the `∩⊆∅` idiom is what `intersect`'s negation computes, §4) |
| `GridUnion` (`∪`), used as `(_ ∪ _) ∩ Full _` | `union` (the clamp is free, §4) |
| `GridTranslate` (`⊕`) | not emitted standalone; absorbed into the offset arithmetic (`oy,ox`) of whichever idiom above it appears inside |
| `Full`, `Empty`/`EmptyGrid`, `Constant` | not emitted; no idiom above ever materializes them (D13) |
| `NewPieceGrid` | not emitted; its one use site (`AxiomsRotGrid`'s spawn clause) is the bare-`⊆` idiom, i.e. `fullyContainedIn` |
| `IsFullLine` (Prop) | not emitted; row test is `isFullRow(row)` |
| `IsFullLineb` | `isFullLineb(g, y)` |
| `RotGrid` (parameter) | `rotGrid(p, r)` — thin pass-through to the `RotGrid` closure param |
| `Valid` | `valid(g, p, py, px, pr)` |
| `CanMovePiece` | `canMovePiece(dy, dx, s)` — free function, `dirOK(dy,dx) && valid(s.mg, s.p, s.py+dy, s.px+dx, s.pr)`; `movePiece` and `fixPiece` both call it directly rather than inlining the guard, so each reads as a direct transcription of `T1.v`'s own `MovePiece`/`FixPiece` guards |
| `Resize` | `resize(g, newGh, fill)` |
| `ClearFullLines` | `clearFullLines(g)` |
| `PieceGrid` | not emitted; inlined as `rotGrid(this.p, this.pr)` at its one use site (`FixPiece`'s `u`) |
| `FullLineCount` / `FullLineCountImpl` | `fullLineCount(g)` (count of full rows in `[0,H)`, per D-reach) |
| `NewPieceState` | `newPieceState(pNew, s)` — returns a state-shaped plain object, not a grid/boolean/number (used by wrapping models, e.g. T3's `HoldPiece`; no call site inside T1 itself) |
| `NewPieceYXState` | `newPieceYXState(pyNew, pxNew, s)` — same return shape as `NewPieceState`; overrides both `py` and `px` unconditionally (D14: the Rocq pair `pyxNew` decomposes to two scalar arguments), distinct purpose (used by T5's `DropPiece`, T6's kick relocation; no call site inside T1 itself). A caller that wants one coordinate preserved passes its current value explicitly for that argument. |
| — (no `T1.v` counterpart) | `canRotatePiece(cw, s)` — implementation-freedom helper (§4): factors `T1.RotatePiece`'s own guard into a named, side-effect-free predicate, so a wrapping model (T6's `RotateKickPiece`) can check "would rotation succeed" without performing it. Not a translation of any `T1.v` definition — added directly in `t1/model.js` because the guard it needs already lives here, not because `T1.v` defines it. |
| `FilterFullLines` | — (D2, D-reach) |
| `Init` | `Machine` constructor |
| `MovePiece` | `Machine.movePiece(dy, dx)` (D14: `dyx` decomposed) |
| `RotatePiece` | `Machine.rotatePiece(cw)` |
| `FixPiece` | `Machine.fixPiece(pNew)` |
| `FallStep` | `Machine.fallStep(pNew)` |
| `mg,p,py,px,pr,gameover,clearedLines` | identical field names (D14: `pyx` decomposed to `py,px`) |
| `AxiomsPW` | — (not emitted; checked by `checkAxioms`) |
| `AxiomsInitialYX` | — (not emitted; checked by `checkAxioms`) |

Emit free functions in `T1.v` source order (as filtered through the fusion rule);
methods in source order. No functions beyond this table (except `step`, `stutter`,
`snapshot`, `checkAxioms`, `typeOK`, `checkInvariants`). No refactors, no helpers not
listed here or in §2.

## 4. Translation rules specific to T1

`T1.v`'s grid algebra (`⊆`,`∩`,`∪`,`⊕`,`Full`,`∅`) is used in exactly four idioms,
never bare-composed any other way. Each is translated as a single JS function,
never by materializing an intermediate grid:

1. **`gp ⊆ Full g`** (location only — `Full`'s content is `true` everywhere in its
   box, so the content conjunct of `⊆` is vacuous, leaving only box membership):
   `occupiedInside(g1,y1,x1,g2,y2,x2)` — `∀ (y,x) ∈ box(g1), L g1 y x → InBox g2 (y+y1-y2) (x+x1-x2)`.
2. **`gp ∩ g ⊆ ∅`** (equivalently `¬∃` shared occupied cell — `⊆ ∅` says every
   occupied cell of the intersection is, vacuously, nowhere, i.e. there is none):
   `!intersect(g1,y1,x1,g2,y2,x2)` — `intersect` is `∃ (y,x) ∈ box(g1), L g1 y x ∧ InBox g2 (…) ∧ L g2 (…)`.
3. **`(g1 ∪ g2) ∩ Full g1`** (union clamped back onto `g1`'s own box — `BoxUnionClamp`,
   `T1Proofs.v`, shows the clamp is exactly `g1`'s box, so the result's content on
   that box is `L g1 y x ∨ (InBox g2 (…) ∧ L g2 (…))` with no further intersection
   needed): `union(g1,y1,x1,g2,y2,x2)`, producing a fresh `g1`-shaped array.
4. **bare `g1 ⊆ g2`** (genuine subset — content of `g2` matters, used once, in
   `AxiomsRotGrid`'s spawn clause): `fullyContainedIn(g1,y1,x1,g2,y2,x2)` — as (1)
   but with `L g2 (…) = true` required, not merely `InBox`.

`Full g1 ⊆ Full g2` (used once, in `AxiomsForbiddenGrid`) is idiom (4) specialized —
both sides' content is trivially `true`, so it degenerates to a pure box-containment
check, `bboxInsideBBox(g1,y1,x1,g2,y2,x2)`.

- **Offsets** (`oy = y+y1-y2`, `ox = x+x1-x2`): plain integer subtraction (no `mod`),
  then **guard before index** (D9): bounds conjuncts first, `g1[y][x]`/`g2[oy][ox]`
  read only once guarded.
- **`rotGrid(p, r)`**: `RotGrid` is an opaque **parameter** of the model (the per-piece
  SRS rotation grids live in `instance.js`, §13.4), not a derived definition. The engine's
  `rotGrid` is a thin pass-through: `return RotGrid(p, r);`. It performs no
  transformation and no copy (every caller is read-only; non-aliasing note, §6.x /
  `proofs.md` §4).
- **`clearFullLines(g)`** (D2, D-reach):
  ```js
  const kept = g.filter(row => !isFullRow(row));            // non-full, order preserved (y asc, bottom-up)
  return kept.concat(emptyRows(g.length - kept.length, g[0].length));  // pad empties on top
  ```
  with `isFullRow(row) => row.every(c => c === true)`. Equivalence to
  `ClearFullLines` is `proofs.md` §3 `L-clearFullLines`.
- **`union`/`resize`/`rotGrid`** construct fresh arrays (copy-safe by construction,
  skill N3); `filter` shares row objects — never mutate a row in place (proofs.md
  non-aliasing lemma).

## 5. Free functions — signatures (all pure; return `boolean` unless noted)

```
occ             (c)                      : boolean   // c !== false — the one cell-truth test (D1)
fullyContainedIn(g1, y1, x1, g2, y2, x2) : boolean   // idiom (4); used by checkAxioms
bboxInsideBBox  (g1, y1, x1, g2, y2, x2) : boolean   // idiom (4) specialized to Full/Full
isFullRow       (row)                    : boolean
isFullLineb     (g, y)                   : boolean
intersect       (g1, y1, x1, g2, y2, x2) : boolean   // idiom (2), negated at call sites
occupiedInside  (g1, y1, x1, g2, y2, x2) : boolean   // idiom (1)
rotGrid         (p, r)                   : (false|Piece)[][]  // colorized at the instance.js boundary (D1)
valid           (g, p, py, px, pr)       : boolean
canMovePiece    (dy, dx, s)              : boolean   // dirOK(dy,dx) && valid(...); spec: CanMovePiece
resize          (g, newGh, fill)         : boolean[][]
clearFullLines  (g)                      : (false|Piece)[][]
union           (g1, y1, x1, g2, y2, x2) : (false|Piece)[][]  // idiom (3); returns the occupying cell's
                                                               // own value, not a collapsed `true` (D1)
fullLineCount   (g)                      : number      // full rows in [0,H); sets clearedLines
newPieceState   (pNew, s)                : {mg, p, py, px, pr, gameover, clearedLines}
newPieceYXState (pyNew, pxNew, s)        : {mg, p, py, px, pr, gameover, clearedLines}
canRotatePiece  (cw, s)                  : boolean  // implementation-freedom helper, no T1.v counterpart
```

## 6. `Machine` — fields, constructor, methods

Fields: `mg, p, py, px, pr, gameover, clearedLines`. `clearedLines : number` records
how many lines the **last** fix cleared (`0` at `Init`); `movePiece`/`rotatePiece` carry it
through unchanged, `fixPiece` overwrites it. It is exposed in `snapshot` and consumed by T2.

Constructor `constructor(p)` ≙ `Init p` (argument name matches `Init`'s own).
Sets `mg` to a fresh copy of `InitialMainGrid` (D1, N3 — never alias the constant), `p`,
`py := InitialY(p)`, `px := InitialX(p)`, `pr := 0`,
`gameover := intersect(ForbiddenGrid, FY, FX, mg, 0, 0)` (idiom (2), negated form of
`(ForbiddenGrid ∩ InitialMainGrid) ⊈ ∅`), `clearedLines := 0`. Runs `checkAxioms()`
first, gated by `CHECK_AXIOMS` (§7) — a debug-time convenience, not a proof
precondition (see §7's note). `CHECK_INVARIANTS`-gated `typeOK` assertion at the end,
as in every method below.

Methods return `boolean` (`true` = action fired, `false` = guard failed = stutter).

`movePiece(dy, dx)` ≙ `MovePiece (dy,dx)`. Guard: `!gameover && canMovePiece(dy, dx, this)`
(req-piece-move-dir — `canMovePiece` is the direction-restriction-to-`{(0,-1),(0,1),(-1,0)}`
conjunct **and** `valid(mg, p, py+dy, px+dx, pr)`, called directly rather than inlined,
textually matching `T1.v`'s own `! gameover s && CanMovePiece dyx s`); on failure, return
`false`, no field touched. On success: `py += dy`, `px += dx`
(req-piece-move-def); return `true`.

`rotatePiece(cw)` ≙ `RotatePiece cw`. New rotation `pr2 := mod(pr + (cw ? -1 : 1), 4)` (D4).
Guard: `!gameover && valid(mg, p, py, px, pr2)` (req-piece-rot); on failure, return
`false`. On success: `pr := pr2`; return `true`.

`fixPiece(pNew)` ≙ `FixPiece p_new`. Guard: `!gameover && !canMovePiece(-1, 0, this)`,
textually matching `T1.v`'s own `! gameover s && ! CanMovePiece (-1, 0) s`. Since
`canMovePiece`'s direction conjunct is unconditionally true for `(-1,0)`, this reduces to
`!gameover && !valid(mg, p, py-1, px, pr)`, i.e. the piece is blocked below — but the guard
is written as the `canMovePiece` call, not the reduced form, so it stays a direct
transcription of the spec rather than a hand-simplified equivalent.
**Simultaneous→sequential order is mandatory** (skill §4b; `proofs.md` §9.3 must
reproduce this dependency argument). The union grid `u` (post-union, pre-clear) is
bound once so `clearedLines` can be counted on it **before** clearing — `u` is the
grid where transient full lines are visible (`mg2` has none):
```js
if (!(!this.gameover && !valid(this.mg, this.p, this.py - 1, this.px, this.pr))) return false;  // real guard
if (CHECK_INVARIANTS) console.assert(Piece.includes(pNew), 'pNew∈Piece');                       // D5
const u   = union(this.mg, 0, 0, rotGrid(this.p, this.pr), this.py, this.px);  // 1: reads pre-state; idiom (3)
const cl  = fullLineCount(u);                     // clearedLines on pre-clear grid (spec: FullLineCount u)
const mg2 = clearFullLines(u);                    // req-grid-clear
this.mg           = mg2;
this.p            = pNew;                          // 2
this.py           = InitialY(pNew);               // 3: read post-state p
this.px           = InitialX(pNew);               // 3
this.pr           = 0;                            // 4
this.gameover     = intersect(ForbiddenGrid, FY, FX, mg2, 0, 0);   // 5: reads post-state mg // req-piece-fix-gameover
this.clearedLines = cl;                           // 6: spec: clearedLines := FullLineCount u
if (CHECK_INVARIANTS) console.assert(typeOK(this), 'typeOK@fix');
return true;
```

`fallStep(pNew)` ≙ `FallStep p_new`:
```js
if (this.movePiece(-1, 0)) return true;            // req-piece-fall
return this.fixPiece(pNew);                        // req-piece-fix
```

## 7. `checkAxioms`, `typeOK`, `checkInvariants`

`checkAxioms()` — one `console.assert` per conjunct of each `Axiom` block (skill §5),
**except** every `Contained` conjunct (`AxiomsRotGrid`, `AxiomsInitialMainGrid`,
`AxiomsForbiddenGrid` each state one): per D-Contained, these hold unconditionally for
any grid array (`boolean[][]` or `(false|Piece)[][]`, D1) and are not asserted. Gated by `CHECK_AXIOMS` (default `true`). This
is a debug-time convenience — it surfaces a clear diagnostic if the caller-supplied
instance parameters violate a model axiom, instead of failing later with an unrelated
error, or not failing at all. **It is not required by the refinement proof**:
`proofs.md` is a conditional statement ("if the axioms hold for this instance, then
`model.js` refines `T1.v`"), true independent of whether `checkAxioms` is ever invoked
at runtime. Unlike `CHECK_INVARIANTS` (below), which guards a claim deductively
implied by the proof and can safely default off, `CHECK_AXIOMS` gates a hypothesis of
the proof and should default on, so that a malformed instance fails loudly rather than
producing unspecified behaviour.

- `AxiomsPW`: `Number.isInteger(PW) && PW > 0`.
- `AxiomsInitialYX` (∀ `p ∈ Piece`): `1 - PW <= InitialY(p) && InitialY(p) < HM`
  and `1 - PW <= InitialX(p) && InitialX(p) < WM`.
- `AxiomsRotGrid` (∀ `p ∈ Piece`):
  - **∀ `r ∈ {0,1,2,3}`**: `rotGrid(p,r)` is a `PW×PW` grid of `false | Piece` cells
    (D1/D8 shape) **and** has ≥1 occupied cell in `[0,PW)²` (via `occ`, not `=== true`).
    (7 pieces × 4 rotations = 28 shape+occupied checks.)
    (The `Contained` clause of this same conjunction is not checked — D-Contained.)
  - **`r = 0` only**: `fullyContainedIn(rotGrid(p,0), InitialY(p), InitialX(p), ForbiddenGrid, FY, FX)`
    — the JS realization of `NewPieceGrid p ⊆ ForbiddenGrid` (idiom (4)).
    (7 containment checks; spawn always uses `pr = 0`, so only `r=0` must fit the zone.)
- `AxiomsInitialMainGrid`: `HM>0`, `WM>0`, no full line
  (`InitialMainGrid.every((_,y)=>!isFullLineb(InitialMainGrid,y))`).
  (`Contained` and `YX InitialMainGrid = (0,0)` are not separately checked: the former
  by D-Contained, the latter because `InitialMainGrid` is realized as a plain
  `boolean[][]` with no position scalars at all — D15 — so it *is* origin `(0,0)` by
  representation, not by an assertable fact.)
- `AxiomsForbiddenGrid`: `H,W>0`, `bboxInsideBBox(ForbiddenGrid,FY,FX,InitialMainGrid,0,0)`
  — the JS realization of `Full ForbiddenGrid ⊆ Full InitialMainGrid`. `FY>=0` and
  `FX>=0` are additionally asserted for a clearer failure message, though they are now
  implied by `bboxInsideBBox`'s own first/third conjuncts (`y2 ≤ y1`/`x2 ≤ x1` with
  `y2=x2=0`) rather than independently required by `T1.v` — redundant, not extraneous:
  they can only fire when the aggregate check would fire anyway. (`Contained` is not
  checked — D-Contained.)
- D8 extras: `Array.isArray(Piece) && Piece.length>0`; every element a primitive
  (`['string','number','symbol'].includes(typeof p)`).
- D10 headroom: `Number.isInteger(MAX_SAFE_INTEGER)` and `B <= MAX_SAFE_INTEGER`,
  and each integer parameter/dimension (`HM,WM,PW,FY,FX`, `InitialY(p)`,`InitialX(p)`)
  is `<= MAX_SAFE_INTEGER` in magnitude.

`typeOK(s, isOccupied = c => Piece.includes(c))` (skill N4) — rectangular `HM×WM`
`mg`, each cell `false` or `isOccupied`-accepted (default: a `Piece` id — D1/D8);
integral `py,px`; integral `pr ∈ [0,3]`; boolean `gameover`; integral non-negative
`clearedLines`; `Piece.includes(s.p)`.

`checkInvariants(s)` (D7) — the pulled-back invariants as asserts, mirroring `Correct`'s
five conjuncts exactly: `TypeOK` (calls `typeOK(s)`, not a re-implementation — avoids
drift between the two), `Gameover` (`gameover === intersect(ForbiddenGrid,FY,FX,mg,0,0)`),
`PieceOccupiedInsideBounds` (`occupiedInside(rotGrid(p,pr), py, px, mg, 0, 0)` —
unconditional, holds even when `gameover`), `PieceOnFreeBlocks` (guarded by `!gameover`),
`NoFullLine` (`mg.every((_,y)=>!isFullLineb(mg,y))`). Deductively redundant (skill N4)
given the refinement proof — diagnostic only, safe to default `CHECK_INVARIANTS = false`.

`snapshot(machine)` — read-only view, not a deep copy: `{mg: wrapGrid(machine.mg), p,
py, px, pr, gameover, clearedLines}`, where `wrapGrid(g) = {height: g.length, width:
g[0].length, cell: (y,x) => g[y][x]}` exposes no array reference an observer could
reach in and mutate — only height/width and a per-cell getter. `p, py, px, pr,
gameover, clearedLines` are already primitives, immutable in the sense that matters
(reassigning a returned value never affects the live `Machine`), so only `mg` needs
this treatment; `view.js`'s `drawGrid` reads it via `mg.height`/`mg.width`/
`mg.cell(y,x)`, never as a raw 2D array.

## 8. `proofs.md` — required structure (frozen order)

1. **Scope** — safety only (D11).
2. **α + box-determinism + Contained-for-free** — the coercion `⟦g⟧` from a
   `boolean[][]` to a boxed `Grid`; the argument that any such coercion is
   automatically `Contained` (D-Contained), and that every reachable `mg` is
   box-determined at origin `(0,0)` (D-reach, skill §6.1/N4).
3. **Fusion-idiom lemmas** — one per idiom in §4 (`L-occupiedInside`, `L-intersect`,
   `L-union`, `L-fullyContainedIn`, `L-bboxInsideBBox`), each stating the JS boolean/
   array equals the corresponding `T1.v` idiom evaluated under α; plus the
   unaffected free-function lemmas (`L-rotGrid`, `L-resize`, `L-isFullRow`,
   `L-isFullLineb`, `L-mod`, `L-fullLineCount`, `L-newPieceState`,
   `L-newPieceYXState`, `L-canRotatePiece`) and **`L-clearFullLines`** flagged
   *non-structural* with the D-reach-dependent extensional obligation and the
   in-box proof sketch (D2 / skill N10).
4. **Non-aliasing lemma** (skill N3) — concrete-only, no Rocq image.
5. **`typeOK` = sub-lemma (2a)** (skill N4) — base from `checkAxioms`, step per method;
   every action lemma in §6 runs under `typeOK`.
6. **Integer-range safety §6.8** — bound `B`, quantified over all arithmetic subterms;
   cite `T1JsBounds.v` lemmas (`InJSRange_of_absB`, `StateBounded`, `NoOverflow_of_StateBounded`,
   `Overflow_safe_reachable`).
7. **State-bound invariant** — link `StateBounded` / `StateBounded_of_Correct`
   (`T1JsBounds.v`) as the coupling between `Correct` and the position envelope.
8. **Init** — constructor ≙ `Init p0`, field-by-field.
9. **Each action** — guard-fail→stutter; guard-hold→field match; for `fixPiece`
   reproduce the §6 dependency-order argument.
10. **`fallStep`** — disjoint-guard sequencing (skill §6.6).

## 9. Tests — required suites

Oracle principle: **expected values come from the model, never from the generator.**
Prefer the executable Rocq reference (§9.4) as the oracle; where unavailable, golden
vectors must be derived from `T1.v` by extraction/hand-evaluation and committed.

### 9.1 Unit (`model.unit.test.js`) — deterministic golden vectors
- `rotGrid`: all 4 rotations of a fixed asymmetric piece; `rotGrid(p,r)` applied 4× ≡ identity on occupied set.
- `clearFullLines`: empty/one full at bottom/middle/top, several full, all full, none; assert exact resulting grid, dimension preserved, empties on top.
- `intersect`/`occupiedInside`/`valid`: cells straddling each boundary (negative offset, `=H`, `=W`); confirms guard-before-index (D9) — must not throw.
- `mod`: `mod(-1,4)===3`, `mod(4,4)===0`, full `{-1..4}` table (skill `L-mod`).
- `movePiece`: each legal/illegal direction; gameover blocks; out-of-grid blocked.
- `rotatePiece`: cw and ccw; all 4 pr values cycle back; gameover blocks; invalid rotation (would intersect) blocked.
- `fixPiece`: full lock→clear→respawn→gameover sequence on a crafted board.
- `fallStep`: falls when space below; triggers `fixPiece` when blocked below (mutual exclusion of guards).

### 9.2 Property-based (`model.properties.test.js`, e.g. fast-check)
Generators produce valid instances (§11 shape, within `B`) and random event sequences.
Properties checked after **every** step:
- `typeOK(snapshot)` holds; `mg` stays `HM×WM`.
- `checkInvariants` passes (`Gameover`, `PieceOnFreeBlocks`, `NoFullLine`).
- no exception thrown (D9 guard-before-index).
- every integer field within `±MAX_SAFE_INTEGER` (D10); stronger: within `±B`.
- **gameover monotonicity**: once `true`, stays `true` (all guards require `¬gameover`).
- algebraic: `clearFullLines` idempotent & dimension-preserving; `union` dims = `g1` dims.

### 9.3 Fuzz (`model.fuzz.test.js`)
- Long random traces (10³–10⁵ steps) over random in-`B` instances; assert no throw +
  `typeOK` + bounds + gameover-monotone after each step.
- Adversarial `checkAxioms`: malformed params (ragged grid, non-primitive piece,
  `B > MAX_SAFE_INTEGER`, negative `FY`) must trip an assertion, not pass silently.

### 9.4 Differential refinement oracle (`oracle.js`) — strongest, recommended
Extract `T1.v` (`MovePiece`,`RotatePiece`,`FixPiece`,`FallStep`) to OCaml/JS
via Rocq extraction, or hand-write a literal interpreter of `T1.v` whose grids are
functions materialized on `[Y g, Y g + H g) × [X g, X g + W g)`. For each step of a
random trace, assert `snapshot(jsMachine) ≡ materialize(rocqNext(event, rocqState))`.
This makes the model itself the test oracle and turns the whole pipeline
self-checking. Mark optional only if extraction is unavailable.

## 10. Acceptance oracle (operational check, not the definition of correctness)

Correctness is refinement (`model.js ⊨ T1.v`, `proofs.md`); this section is the checklist
used to gain confidence that a given generation achieves it. A regeneration passes iff all
hold:
1. `model.js` parses; no use of `localStorage`/forbidden APIs (skill).
2. Coverage check: every `Definition`/`Fixpoint`/`Axiom`/`Record` name in `T1.v` is
   either in the §3 map, explicitly listed as not-emitted with reason (D2, D13,
   D-Contained), or covered collectively by the fusion rule (§4) — `GridInclude`,
   `GridIntersect`, `GridUnion`, `GridTranslate`, `Full`, `Empty`, `EmptyGrid`,
   `Constant`, `InBox`, `OutsideBox`, `Contained`, `NewPieceGrid` all fall in this last
   bucket. Fail on any unhandled name (guards against silent drift when `T1.v` changes).
3. All §9 suites pass; §9.4 passes if present.
4. `proofs.md` contains every §8 item (checklist review — it is a *hand* proof, the
   weakest link; see comment).
5. Regeneration diff vs the committed golden snapshot is empty **up to the §3 naming
   map and comment text** (behavioural, not byte, determinism — D-preamble).

## 11. Instantiation (`instance.js`, runtime input)

Not generated by the T1 codegen pipeline; generated separately (§13).
Must export the abstract parameters with the §7 shapes and satisfy the four
`Axiom` blocks (`AxiomsPW`, `AxiomsInitialYX`, `AxiomsRotGrid`,
`AxiomsInitialMainGrid`, `AxiomsForbiddenGrid` — minus their `Contained` clauses,
D-Contained) and `B ≤ MAX_SAFE_INTEGER`.
`Piece` is a finite primitive array (D8). `checkAxioms` validates at `new Machine(...)`.

## 12. Generator determinism rules

- Temperature 0 (or lowest available). **Caveat:** does not guarantee bit-identical
  output across runs (floating-point non-associativity, MoE routing, etc.).
  Determinism here means refinement-preserving equivalence across regenerations
  (§10), not textual identity — see §0's note that byte-identity is not required.
- Single pass; no speculative alternatives.
- Reference `T1.v` by name (§0); emit functions/methods/lemmas in the frozen orders
  (§3, §8). No commentary beyond requirement tags (`// req-…`) and the §6 ordering note.
- Do not invent behaviour, optimisations, error handling, or APIs absent from this file.
- On any ambiguity not resolved here: stop and surface it as a TODO comment rather than
  guessing.
- **Closure scope (§15).** Any table, handler, or callback that references mutable
  per-game state (e.g. `machine`, reassigned by `startGame`) must be **declared inside
  the scope that owns that state** (`main()`), never at module level. Concretely:
  `ACTIONS` (whose effects call `machine.*`) lives inside `main()`; only the pure maps
  `KEYMAP` and `GAMEPAD_MAP`, which close over nothing mutable, may sit at module level.

---

## 13. `instance.js` — concrete Tetris parameters

### 13.1 Scalar parameters

| parameter | value |
|-----------|-------|
| `PW` | `4` |
| `HM` (derived) | `22` |
| `WM` (derived) | `10` |
| `FY` (D15: `Y ForbiddenGrid`) | `20` |
| `FX` (D15: `X ForbiddenGrid`) | `0` |
| `InitialY(p)` (D14: `fst (InitialYX p)`) | `19` for every piece (spawn cells sit in grid rows {1,2}, mapping to main rows {20,21} = the forbidden zone) |
| `InitialX(p)` (D14: `snd (InitialYX p)`) | `3` for every piece |

### 13.2 Piece set

```js
export const Piece = ['I', 'O', 'T', 'S', 'Z', 'J', 'L'];
```

Elements are strings (primitive, value-`===`-comparable, D8).

### 13.3 Grid constants

```js
export const InitialMainGrid = /* 22×10 all-false */ ;
export const ForbiddenGrid   = /* 2×10 all-true  */ ;
```

`InitialMainGrid` has `H=22`, `W=10`, all cells `false`, Rocq origin `(0,0)` by
representation (D15 — it carries no position scalars).
`ForbiddenGrid` has `H=2`, `W=10`, all cells `true`, Rocq origin `(FY,FX)=(20,0)`,
represented as this array plus the `FY`,`FX` scalars above.

### 13.4 `RotGrid` — exact rotated piece grids (all 28)

`RotGrid(p, r)` returns a fresh `4×4` `(false | Piece)[][]` for `r ∈ {0,1,2,3}` (pure,
D8) — occupied cells carry `p` itself, not bare `true` (D1) — Rocq origin `(0,0)`
(`AxiomsRotGrid`'s `YX gr = (0,0)`, D15 — no position scalars).
Index convention: `g[0]` = bottom row, `g[3]` = top row; `x` increases rightward.
`r` counts **counter-clockwise** quarter-turns (matches `RotatePiece`: `cw=false` → `pr+1`).

**Rotation centers (SRS, per the reference image).** Each piece rotates about a fixed
point so that the four orientations all fit inside `[0,PW)² = [0,4)²` and the piece
spins in place:

| piece | center (row, col) | note |
|-------|-------------------|------|
| T, S, Z, L, J | `(1, 1)` | on the middle cell of the 3-wide bar |
| O | `(1.5, 1.5)` | between the 4 cells — rotation-invariant |
| I | `(1.5, 1.5)` | between the 2nd/3rd cells, on the lower edge |

A cell at offset `(dy, dx)` from the center maps under one CCW quarter-turn to
`(dx, -dy)`. All centers are at row ≥ 1, giving row 0 as headroom for blocks that swing
downward; without this the rotated grids would need negative row indices, which a
`4×4` grid cannot represent.

**Why `InitialY = 19` (not 20).** The spawn orientations place each piece's extra
cell *above* its bar, and the center sits on the bar at grid row 1, so the `r=0`
occupied cells fall in grid rows `{1, 2}` (the I-piece in row `{2}` alone). The spawn
axiom (`NewPieceGrid p ⊆ ForbiddenGrid`, realized as `fullyContainedIn(rotGrid(p,0),
InitialY(p), InitialX(p), ForbiddenGrid, FY, FX)`) maps grid cell `(y,x)` → main row
`InitialY + y`; with cells in rows `{1,2}` and the forbidden zone at main rows
`{20,21}`, we need `InitialY + 1 = 20`, i.e. `InitialY = 19`. Column check:
`InitialX = 3` is exact center (`(WM−PW)/2 = (10−4)/2 = 3`); it puts 3-wide pieces at
main cols `{3,4,5}`, I at `{3,4,5,6}`, O at `{4,5}` — all `⊂ [0,10)`, all inside the
all-true zone.

```
F = false, T = true. Rows listed bottom→top (g[0] first, g[3] last).
```

**I** — center `(1.5, 1.5)`. Horizontal on row 2 (r0) / row 1 (r2); vertical in col 1 (r1) / col 2 (r3).
```
r=0                 r=1                 r=2                 r=3
g[0]=[F,F,F,F]      g[0]=[F,T,F,F]      g[0]=[F,F,F,F]      g[0]=[F,F,T,F]
g[1]=[F,F,F,F]      g[1]=[F,T,F,F]      g[1]=[T,T,T,T]      g[1]=[F,F,T,F]
g[2]=[T,T,T,T]      g[2]=[F,T,F,F]      g[2]=[F,F,F,F]      g[2]=[F,F,T,F]
g[3]=[F,F,F,F]      g[3]=[F,T,F,F]      g[3]=[F,F,F,F]      g[3]=[F,F,T,F]
```

**O** — center `(1.5, 1.5)`, rotation-invariant: all four `r` identical.
```
r ∈ {0,1,2,3}
g[0]=[F,F,F,F]
g[1]=[F,T,T,F]
g[2]=[F,T,T,F]
g[3]=[F,F,F,F]
```

**T** — center `(1, 1)`. r0 nub up; r1 nub left; r2 nub down; r3 nub right.
```
r=0                 r=1                 r=2                 r=3
g[0]=[F,F,F,F]      g[0]=[F,T,F,F]      g[0]=[F,T,F,F]      g[0]=[F,T,F,F]
g[1]=[T,T,T,F]      g[1]=[T,T,F,F]      g[1]=[T,T,T,F]      g[1]=[F,T,T,F]
g[2]=[F,T,F,F]      g[2]=[F,T,F,F]      g[2]=[F,F,F,F]      g[2]=[F,T,F,F]
g[3]=[F,F,F,F]      g[3]=[F,F,F,F]      g[3]=[F,F,F,F]      g[3]=[F,F,F,F]
```

**S** — center `(1, 1)`.
```
r=0                 r=1                 r=2                 r=3
g[0]=[F,F,F,F]      g[0]=[F,T,F,F]      g[0]=[T,T,F,F]      g[0]=[F,F,T,F]
g[1]=[T,T,F,F]      g[1]=[T,T,F,F]      g[1]=[F,T,T,F]      g[1]=[F,T,T,F]
g[2]=[F,T,T,F]      g[2]=[T,F,F,F]      g[2]=[F,F,F,F]      g[2]=[F,T,F,F]
g[3]=[F,F,F,F]      g[3]=[F,F,F,F]      g[3]=[F,F,F,F]      g[3]=[F,F,F,F]
```

**Z** — center `(1, 1)`.
```
r=0                 r=1                 r=2                 r=3
g[0]=[F,F,F,F]      g[0]=[T,F,F,F]      g[0]=[F,T,T,F]      g[0]=[F,T,F,F]
g[1]=[F,T,T,F]      g[1]=[T,T,F,F]      g[1]=[T,T,F,F]      g[1]=[F,T,T,F]
g[2]=[T,T,F,F]      g[2]=[F,T,F,F]      g[2]=[F,F,F,F]      g[2]=[F,F,T,F]
g[3]=[F,F,F,F]      g[3]=[F,F,F,F]      g[3]=[F,F,F,F]      g[3]=[F,F,F,F]
```

**L** — center `(1, 1)`.
```
r=0                 r=1                 r=2                 r=3
g[0]=[F,F,F,F]      g[0]=[F,T,F,F]      g[0]=[T,F,F,F]      g[0]=[F,T,T,F]
g[1]=[T,T,T,F]      g[1]=[F,T,F,F]      g[1]=[T,T,T,F]      g[1]=[F,T,F,F]
g[2]=[F,F,T,F]      g[2]=[T,T,F,F]      g[2]=[F,F,F,F]      g[2]=[F,T,F,F]
g[3]=[F,F,F,F]      g[3]=[F,F,F,F]      g[3]=[F,F,F,F]      g[3]=[F,F,F,F]
```

**J** — center `(1, 1)`.
```
r=0                 r=1                 r=2                 r=3
g[0]=[F,F,F,F]      g[0]=[T,T,F,F]      g[0]=[F,F,T,F]      g[0]=[F,T,F,F]
g[1]=[T,T,T,F]      g[1]=[F,T,F,F]      g[1]=[T,T,T,F]      g[1]=[F,T,F,F]
g[2]=[T,F,F,F]      g[2]=[F,T,F,F]      g[2]=[F,F,F,F]      g[2]=[F,T,T,F]
g[3]=[F,F,F,F]      g[3]=[F,F,F,F]      g[3]=[F,F,F,F]      g[3]=[F,F,F,F]
```

`RotGrid(p, r)` returns a **shared** array, precomputed once per `(p, r)` pair and
cached (7 pieces × 4 rotations = 28 colorized grids, built once at module load), not
a fresh copy on every call — safe because nothing anywhere ever writes to a `rotGrid`
cell, only reads it (`model.js`'s `occupiedInside`/`intersect`/`union`, `view.js`'s
`rg[y][x]` checks), matching `model.js`'s own `rotGrid` being a copy-free
pass-through (§4). For `r` outside `{0,1,2,3}` the function is never called (`TypeOK`
keeps `pr ∈ {0,1,2,3}`); a defensive default (e.g. the `r=0` grid) is harmless but not
required.

### 13.5 Piece colours

Used by `view.js`; exported from `instance.js` as a plain object.

```js
export const PieceColor = {
  I: '#83a598',   // cyan
  O: '#fabd2f',   // yellow
  T: '#d3869b',   // purple
  S: '#b8bb26',   // green
  Z: '#fb4934',   // red
  J: '#458588',   // blue
  L: '#fe8019',   // orange
};
```

### 13.6 Axiom verification (must be checked at generation time)

| Axiom | check |
|-------|-------|
| `AxiomsPW` | `PW=4>0` ✓ |
| `AxiomsInitialYX` | `1-4=-3 ≤ 19 < 22` and `-3 ≤ 3 < 10` for all pieces ✓ |
| `AxiomsRotGrid` | all 28 grids 4×4 with ≥1 occupied cell ✓ (`Contained` not checked, D-Contained); `NewPieceGrid p ⊆ ForbiddenGrid` for all 7 (spawn cells in grid rows {1,2}→main {20,21}; I in row {2}→main {21}; all within the 2×10 all-true zone) ✓ |
| `AxiomsInitialMainGrid` | 22×10, no full line (all-false) ✓ (`Contained`, `YX=(0,0)` hold by representation, D-Contained/D15) |
| `AxiomsForbiddenGrid` | 2×10 all-true; `Full ForbiddenGrid ⊆ Full InitialMainGrid`: `20+2-1=21≤21`, `0+10-1=9≤9` ✓ (implies `FY,FX≥0`; `Contained` not checked) |
| D10 | `B = max(22,10)+4-1 = 25 ≪ MAX_SAFE_INTEGER` ✓ |

---

## 14. `view.js` — renderer

### 14.1 Public API

```js
export function render(canvas, constants, snapshot, pieceColor = {}) { … }
```

`constants` is a plain struct `{ HM, WM, PW, FY, FX, FH, FW, rotGrid }` extracted by `controller.js`
from the engine (read-only; no write-back to the engine ever). `snapshot` is the value
returned by `eng.snapshot(machine)`. `view.js` never imports from `model.js` or `instance.js`.

`t1/view.js` is the canonical home for the drawing primitives shared by every layer
built on top of it (`drawBlock`, `cellOrigin`, `drawGridLines`, `drawGrid`,
`drawPiece`, `drawBackground`, `drawGameOver`) — later layers (T2 onward) import
these rather than redefining them. Each reads `constants.PANEL_PX` defensively
(`?? 0`, §14.3) so the same implementation serves T1 (no side panel) through any
layer with one or more side panels without a per-layer fork.

### 14.2 Layout / scaling

```
cellSize = Math.min(canvas.width / WM, canvas.height / HM)   // square cells
gridPixelW = WM * cellSize
gridPixelH = HM * cellSize
```

The controller (§15.x `sizeCanvas`) sets `canvas.width`/`canvas.height` to an exact whole
number of cells in the `WM:HM` aspect ratio, so the grid fills the canvas with no leftover
strip. `render` must nonetheless **clear the entire canvas** each frame (`drawBackground`
fills `ctx.canvas.width × ctx.canvas.height`, not just `gridPixelW × gridPixelH`) so that
no stale pixels survive a rounding-induced margin or a resize.

### 14.3 Coordinate transform

Logical cell `(y, x)` → canvas top-left pixel `(panelPx + x * cellSize, (HM−1−y) * cellSize)`.

```js
function cellOrigin(y, x, cellSize, HM, panelPx = 0) {
  return { cx: panelPx + x * cellSize, cy: (HM - 1 - y) * cellSize };
}
```

`panelPx` defaults to `0` and is read from `constants.PANEL_PX ?? 0` by every caller
— T1 itself has no side panel, so every call site passes the default; the parameter
exists so this same function serves any layer that adds one. This is the only
coordinate-transform function; all drawing sub-procedures call it.

### 14.4 Sub-procedures (all unexported)

```
drawBackground(ctx, canvas, constants, cellSize)
  — fills the WHOLE canvas black; then fills the forbidden zone — logical rows
    [FY, FY+FH), cols [FX, FX+FW), with FH/FW taken from constants (never hardcoded)
    — with a dark-red background (#3A0000 or similar) before grid lines are drawn.
    The zone rectangle in canvas px is positioned via cellOrigin(FY+FH-1, FX, cellSize,
    HM, panelPx), sized FW*cellSize × FH*cellSize.

drawGridLines(ctx, constants, cellSize)
  — draws WM+1 vertical and HM+1 horizontal lines in a low-contrast colour (#333),
    offset by panelPx on the x axis.

drawBlock(ctx, cx, cy, cellSize, color)
  — fills one cell: ctx.fillStyle = color; ctx.fillRect(cx+1, cy+1, cellSize-2, cellSize-2).

drawGrid(ctx, mg, constants, cellSize, pieceColor = {})
  — iterates y ∈ [0,mg.height), x ∈ [0,mg.width) via mg.cell(y,x) (the snapshot's
    read-only grid view, §6); for each occupied cell (D1: any value ≠ false) calls
    drawBlock with pieceColor[cell] ?? '#888888' — locked blocks render in their own
    piece colour, matching D1's colored-blocks representation, not a single flat
    colour; #888888 is only the fallback for an unrecognized piece id.

drawPiece(ctx, snapshot, constants, cellSize, pieceColor = {})
  — rg = constants.rotGrid(snapshot.p, snapshot.pr); iterates y,x ∈ [0,PW);
    for each occupied rg[y][x]: gy = snapshot.py + y, gx = snapshot.px + x;
    **clip**: skip if gy < 0 || gy >= HM || gx < 0 || gx >= WM;
    otherwise call drawBlock with pieceColor[snapshot.p] ?? '#FFFFFF'.

drawGameOver(ctx, canvas, constants, cellSize)
  — semi-transparent black overlay over the grid region only (from panelPx to
    canvas.width, so a side panel on a later layer stays readable); centred white
    "GAME OVER" and smaller "press any key to restart", both with a maxWidth
    (≈0.9×grid width).
```

### 14.5 Piece colour parameter

`pieceColor` (default `{}`) is threaded explicitly through `drawGrid` and `drawPiece`
— every drawing function's colour source is explicit, not read from a module-level
constant. `drawPiece` uses `pieceColor[snapshot.p] ?? '#FFFFFF'` as the fallback
colour; `drawGrid` uses `pieceColor[cell] ?? '#888888'` per locked cell (§14.4).
`controller.js` passes `PieceColor` from `instance.js`. This keeps `view.js` free of
any direct dependency on `instance.js`.

### 14.6 Call order inside `render`

```
1. drawBackground
2. drawGrid         (locked blocks)
3. drawGridLines
4. drawPiece        (active piece, clipped)
5. if snapshot.gameover: drawGameOver
```

---

## 15. `controller.js` + `index.html` — controller / entry point

### 15.1 Imports

```js
import { T }  from './model.js';
import { render } from './view.js';
import {
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX, PieceColor,
} from './instance.js';
```

### 15.2 Initialisation

```js
const eng = T(Piece, InitialMainGrid, ForbiddenGrid,
              RotGrid, InitialY, InitialX, PW, FY, FX);

const constants = {
  HM: InitialMainGrid.length,
  WM: InitialMainGrid[0].length,
  PW, FY, FX,
  FH: ForbiddenGrid.length,
  FW: ForbiddenGrid[0].length,
  rotGrid: eng.rotGrid,
};
```

### 15.3 `main(canvas)` — exported entry point

`index.html` calls `main(document.getElementById('game'))`.

State maintained inside `main` (closure variables, not module-level globals):

```js
let machine;
let lastGravityAt = 0;
let rafId = null;
let disposed = false;
let keyHeld = new Set();
let prevHeld = {};
let repeatTimers = {};
```

No separate "waiting for restart" flag: `machine.gameover` is monotone once true
(every `T1.v` transition guards on `!gameover`) and `handleGameover` is idempotent,
so `machine.gameover` alone is sufficient at every read site. `disposed` guards
against `frame` re-scheduling itself after `dispose()` (§15.6) has already fired for
an in-flight frame.

`main` registers the `keydown`/`keyup` handlers (as named functions, §15.7 — needed
so `dispose()` can remove them again) and a `resize` handler once, sizes the canvas,
calls `startGame()`, and starts the persistent `frame` loop with a single
`window.requestAnimationFrame(frame)`.

### 15.4 `startGame()`

```js
function startGame() {
  machine = new eng.Machine(randomPiece());
  keyHeld = new Set();
  prevHeld = {};
  repeatTimers = {};
  lastGravityAt = performance.now();
}
```

`randomPiece()` = `Piece[Math.floor(Math.random() * Piece.length)]`.

### 15.5 `onTick()` / `frame()` — gravity and the single render + poll loop

Gravity is driven off the same clock the render loop already uses, not a separate
timer:

```js
const GRAVITY_PERIOD = 1000; // ms between automatic falls

function onTick() {
  machine.fallStep(randomPiece());
  if (machine.gameover) handleGameover();
}

function frame(now) {
  processInput(now);
  if (!machine.gameover && now - lastGravityAt >= GRAVITY_PERIOD) {
    lastGravityAt = now;
    onTick();
  }
  render(canvas, constants, eng.snapshot(machine), PieceColor);
  if (disposed) return; // dispose() may have fired while this frame was already in flight
  rafId = window.requestAnimationFrame(frame);
}
```

The game-over overlay appears automatically whenever `snapshot.gameover` is `true`
(§14.4's `drawGameOver`, called from §14.6 step 5); no special-casing in the loop.

`main` returns a `dispose()` function:

```js
return function dispose() {
  disposed = true;
  if (rafId !== null) window.cancelAnimationFrame(rafId);
  rafId = null;
  document.removeEventListener('keydown', onKeyDown);
  document.removeEventListener('keyup', onKeyUp);
  window.removeEventListener('resize', sizeCanvas);
  keyHeld.clear();
  repeatTimers = {};
};
```
Stops the render/gravity loop and removes every listener `main` registered — makes
`main()` safe to call again, starting a fully independent game with no leftover
state or duplicate handlers from a previous call.

### 15.6a `sizeCanvas()` — fit the canvas to the viewport

```js
function sizeCanvas() {
  const margin = 0.95;
  const availW = window.innerWidth  * margin;
  const availH = window.innerHeight * margin;
  const cell   = Math.max(1, Math.floor(Math.min(availW / constants.WM,
                                                 availH / constants.HM)));
  canvas.width  = constants.WM * cell;
  canvas.height = constants.HM * cell;
}
```

### 15.7 Logical actions + keyboard/gamepad handlers

```js
const ACTIONS = {
  LEFT:  { repeat: true,  effect: () => machine.movePiece(0, -1) },
  RIGHT: { repeat: true,  effect: () => machine.movePiece(0,  1) },
  DOWN:  { repeat: true,  effect: () => machine.fallStep(randomPiece()) },
  CCW:   { repeat: false, effect: () => machine.rotatePiece(false) },
  CW:    { repeat: false, effect: () => machine.rotatePiece(true) },
};

const KEYMAP = {
  ArrowLeft: 'LEFT', ArrowRight: 'RIGHT', ArrowDown: 'DOWN',
  z: 'CCW', x: 'CW',
};

const GAMEPAD_MAP = new Map([
  [14, 'LEFT'], [15, 'RIGHT'], [13, 'DOWN'],
  [0, 'CCW'], [1, 'CW'],
]);
```

Keyboard handlers only maintain `keyHeld`; all action dispatch (including repeat)
happens in `processInput`. Declared as named functions (`onKeyDown`/`onKeyUp`), not
inline arrow functions passed directly to `addEventListener` — `dispose()` (§15.5)
needs a stable reference to pass to `removeEventListener`.

```js
function onKeyDown(e) {
  if (machine.gameover) { startGame(); return; }
  const name = KEYMAP[e.key];
  if (!name) return;
  e.preventDefault();
  keyHeld.add(name);
}

function onKeyUp(e) {
  const name = KEYMAP[e.key];
  if (name) keyHeld.delete(name);
}

document.addEventListener('keydown', onKeyDown);
document.addEventListener('keyup', onKeyUp);
```

### 15.8 `processInput(now)` — merged held-state + shared DAS engine

```js
const DAS_DELAY = 170;   // ms held before auto-repeat begins
const ARR       = 50;    // ms between repeats once shifting

function computeHeld() {
  const held = {};
  for (const name of keyHeld) held[name] = true;
  const gp = navigator.getGamepads?.()?.[0];
  if (gp) {
    for (const [idx, name] of GAMEPAD_MAP)
      if (gp.buttons[idx]?.pressed) held[name] = true;
  }
  return held;
}

function processInput(now) {
  const held = computeHeld();

  if (machine.gameover) {
    if (Object.keys(held).some(name => held[name] && !prevHeld[name])) startGame();
    prevHeld     = held;
    repeatTimers = {};
    return;
  }

  for (const name of Object.keys(ACTIONS)) {
    const act = ACTIONS[name];
    if (act.repeat) {
      if (held[name]) {
        const t = repeatTimers[name];
        if (!t) {
          act.effect();
          repeatTimers[name] = { pressedAt: now, lastFire: now };
        } else if (now - t.pressedAt >= DAS_DELAY && now - t.lastFire >= ARR) {
          act.effect();
          t.lastFire = now;
        }
      } else {
        repeatTimers[name] = null;
      }
    } else {
      if (held[name] && !prevHeld[name]) act.effect();
    }
  }

  if (machine.gameover) handleGameover();
  prevHeld = held;
}
```

### 15.9 `handleGameover()`

```js
function handleGameover() {
  keyHeld.clear();
  repeatTimers = {};
}
```

Idempotent, so both read sites can key off `machine.gameover` directly without a
separate flag. No timer to cancel — gravity is gated by `!machine.gameover` inside
`frame` (§15.5) itself, not by a separately-scheduled callback.

### 15.10 `index.html`

Minimal shell; no framework, no external CSS.

```html
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Tetris</title>
  <style>
    html, body { height: 100%; }
    body  { background: #111; display: flex; justify-content: center;
            align-items: center; margin: 0; overflow: hidden; }
    canvas { display: block; }
  </style>
</head>
<body>
  <canvas id="game" width="200" height="440"></canvas>
  <script type="module">
    import { main } from './controller.js';
    main(document.getElementById('game'));
  </script>
</body>
</html>
```

The `width`/`height` attributes are a placeholder; `sizeCanvas` overwrites them on
load and on resize, fitting the canvas to the viewport at the `WM:HM = 10:22` aspect
ratio with square cells.
