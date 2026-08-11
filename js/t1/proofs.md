# proofs.md — refinement proof, `model.js ⊨ T1.v`

This proof is conditional: **if** the parameters supplied to `T(...)` (concretely,
`instance.js`) satisfy `AxiomsPW`, `AxiomsInitialYX`, `AxiomsRotGrid`,
`AxiomsInitialMainGrid`, `AxiomsForbiddenGrid`, and `B ≤ MAX_SAFE_INTEGER`, **then**
every reachable `Machine` instance's field values, under the mapping α below, satisfy
`Correct`, and every method call corresponds to a `Next` transition (or a stuttering
step). `checkAxioms` at runtime is a diagnostic convenience for this hypothesis, not
part of the proof itself.

## 1. Scope

Only **safety** (invariant preservation) transfers: `Correct` holds at `Init` and is
preserved by every action. **Liveness** (e.g. `FallStepAlwaysSucceeds` in `T1Proofs.v`)
is *not* claimed for `model.js` (D11) — nothing here argues termination, fairness, or
that a fall eventually fixes.

## 2. State mapping α, the grid coercion, and `Contained` for free

`Machine`'s fields are named and shaped after `State`'s own fields, decomposing the
Rocq pair `pyx` into `py,px` (D14):

```
α(js) = {| mg  := ⟦js.mg, 0, 0⟧
        ;  p   := js.p
        ;  pyx := (js.py, js.px)
        ;  pr  := js.pr
        ;  gameover := js.gameover
        ;  clearedLines := js.clearedLines
        |}
```

where `⟦g, y0, x0⟧` is the coercion of an array meeting D1 (`boolean[][]` or the widened
`(false|Piece)[][]`) **plus its Rocq origin** to a boxed `Grid`:

```
⟦g, y0, x0⟧ = {| L  := λ y x, (y0 ≤? y <? y0 + g.length) && (x0 ≤? x <? x0 + g[0].length)
                              && occ(g[y - y0][x - x0])
              ;  HW := (g.length, g[0].length)
              ;  YX := (y0, x0)
              |}
```

where `occ(c) = c ≠ false` is the cell-level abstraction map (D1): `false` is the sole
empty sentinel; any other value (the literal `true` used by `RotGrid`/`ForbiddenGrid`,
or a `Piece` id stored directly in `mg`) is occupied.

Every materialized grid in `model.js` has `y0 = x0 = 0` **except** `ForbiddenGrid`,
which uses `(y0,x0) = (FY,FX)` (D15); write `⟦g⟧` for `⟦g,0,0⟧`.

**`Contained` holds for free.** For any array `g` meeting D1 (`boolean[][]` or the
widened `(false|Piece)[][]`) and any `(y0,x0)`, `L ⟦g,y0,x0⟧
y x` is `false` whenever `(y,x)` is outside the box `[y0,y0+g.length) × [x0,x0+g[0].length)`
— by the coercion's own definition (the bounds conjunct is checked *before* the array
read, and is `false` exactly outside the box), not by any assumption on `g`'s content.
So `Contained ⟦g,y0,x0⟧` holds unconditionally, for every `g`. This discharges the
`Contained` conjunct of `AxiomsRotGrid`, `AxiomsInitialMainGrid`, and
`AxiomsForbiddenGrid` for any well-shaped instance, with no runtime check
(`implementation.md` D-Contained) — the reason `model.js` never asserts it.

**Reachability and box-determinism.** `⟦_⟧` is well-defined and faithful for every
reachable `js.mg` because every reachable `mg` is **box-determined at origin `(0,0)`**:
- `Init` sets `mg := copyGrid(InitialMainGrid)`, and `InitialMainGrid` is a plain array
  with no position scalars (D15), i.e. Rocq origin `(0,0)` by representation, matching
  `AxiomsInitialMainGrid`'s `YX InitialMainGrid = (0,0)`.
- `fixPiece` sets `mg := clearFullLines(u)` where `u = union(this.mg,0,0,...)`. `union`
  is fully reconstructive (§4) and, by `BoxUnionClamp` (`T1Proofs.v`), the Rocq grid it
  realizes — `(mg s ∪ gp) ∩ Full (mg s)` — has `YX = YX (mg s)`; by induction `YX (mg s)
  = (0,0)`, so `u`'s Rocq origin is `(0,0)` too, matching `union`'s own array being
  indexed from `0`. `clearFullLines` preserves `YX` (`ClearFullLinesBox`, `T1Proofs.v`),
  so `mg2`'s origin is `(0,0)` as well.
- `movePiece`/`rotatePiece` do not touch `mg`.

Hence **every reachable `mg` has Rocq origin `(0,0)`** (D-reach, `implementation.md`),
which is what licenses treating `IsFullLineb`/`FilterFullLines`/`FullLineCountImpl`'s
abstract starting coordinate as always `0` below (§3), and is exactly `TypeOK`'s own
`YX (mg s) = YX InitialMainGrid = (0,0)` conjunct, carried along by induction rather
than re-derived at each step.

`rotGrid(p, pr)`'s result is not itself state — it is read fresh on every use and never
stored — so no α-coercion is needed for it beyond `⟦_⟧` at the call site; its
faithfulness is `L-rotGrid` below (§3), stated as a parameter precondition.

## 3. Fusion-idiom lemmas

Each idiom lemma states: the JS boolean/array equals the `T1.v` idiom (`implementation.md`
§4) evaluated under α / `⟦_⟧`. Since `Full g`/`∅` are never materialized (D13), no
lemma below needs to construct them — each idiom is proved directly against `⊆`'s /
`∩`'s own definition (`GridIncludeSpec`, `T1Proofs.v`), specialized to a `Full`/`∅`
right-hand side by observing its content is constant.

- **`L-occupiedInside`** (idiom 1, `gp ⊆ Full g`): `occupiedInside(g1,y1,x1,g2,y2,x2)`
  returns `true` iff `∀ (y,x) ∈ box ⟦g1,y1,x1⟧, L = true → InBox ⟦g2,y2,x2⟧ y x`. Since
  `Full ⟦g2,y2,x2⟧`'s content is constant `true`, `GridIncludeSpec`'s second conjunct
  (`L g2 y x = true`) is automatic, leaving exactly the membership conjunct — which is
  what `occupiedInside`'s bounds test computes. The loop ranges over `[0,g1.length) ×
  [0,g1[0].length)`, i.e. `box ⟦g1,y1,x1⟧` shifted to local indices; guard-before-index
  (D9) makes the `g2`-side test safe exactly where `InBox` would be evaluated; `implb
  (L g1 y x) (…)` is rendered as early-`return false` on a failing conjunct.
- **`L-intersect`** (idiom 2, negated: `gp ∩ g ⊆ ∅`): `intersect(g1,y1,x1,g2,y2,x2)`
  returns `true` iff `∃ (y,x), L ⟦g1,y1,x1⟧ y x ∧ L ⟦g2,y2,x2⟧ y x` — i.e. iff
  `⟦g1,y1,x1⟧ ∩ ⟦g2,y2,x2⟧` has an occupied cell, i.e. iff `¬((…) ⊆ ∅)` (`∅`'s content
  is constant `false`, so `⊆ ∅` says the intersection has none). `!intersect(...)`
  is therefore exactly `(…) ⊆ ∅`. Early-`return true` on a satisfied conjunct matches
  the existential.
- **`L-union`** (idiom 3, `(g1 ∪ g2) ∩ Full g1`): `occ(union(g1,y1,x1,g2,y2,x2)[y][x]) =
  occ(g1[y][x]) || (bounds(y,x) ∧ occ(g2[y+y1-y2][x+x1-x2]))` for every `(y,x) ∈
  box(g1)` — `union` returns whichever operand's actual cell value occupies each
  position (D1), not a collapsed `true`, but its `occ`-image is exactly this formula.
  By `BoxUnionClamp` (`T1Proofs.v`), `(⟦g1,y1,x1⟧ ∪ ⟦g2,y2,x2⟧) ∩ Full ⟦g1,y1,x1⟧` has
  exactly `⟦g1,y1,x1⟧`'s box, and on that box its content is `L g1 y x ∨ L g2 (…)` —
  `∩ Full`'s content conjunct with the constant-`true` side dropped — with `L g2 (…)`
  read only where `InBox ⟦g2,y2,x2⟧` holds (Contained, §2, makes any other read `false`
  regardless), matching the JS `bounds(y,x) ∧ occ(g2[…])` guard once both sides are
  read through `occ`/`L` (§2). `.map` is fully reconstructive (§4).
- **`L-fullyContainedIn`** (idiom 4, bare `g1 ⊆ g2`): as `L-occupiedInside`, but the
  content conjunct is *not* dropped (`g2` is a genuine grid, not `Full` of one) — the JS
  additionally requires `g2[oy][ox]`, matching `GridIncludeSpec`'s full conclusion.
- **`L-bboxInsideBBox`** (idiom 4 specialized to `Full/Full`): both sides' content
  conjuncts are constant `true`, so `⊆` degenerates to pure box containment; direct
  transcription of the four inequalities using `g.length`/`g[0].length` for `H`/`W`; no
  loop, no guard needed.
- **`L-isFullRow`**: `isFullRow(row)` returns `true` iff `∀ x, 0≤x<row.length →
  occ(row[x])`, i.e. `IsFullLine` restricted to one materialized row, cell truth read
  through `occ` (§2).
- **`L-isFullLineb`**: by D-reach, every `g` passed has Rocq `Y g = 0`; for
  `0≤y<g.length`, `isFullLineb(g,y) = isFullRow(g[y])`, which is `IsFullLineb` unfolded
  (`implb (Y g ≤? y <? Y g + H g) (…)` with `Y g = 0` and the antecedent true reduces to
  the `forallb`). For `y` outside `[0,g.length)`, the JS function returns `true`
  matching `implb false _ = true`.
- **`L-rotGrid`** (parameter precondition, not a proved lemma): `rotGrid(p,r)` is
  assumed to return exactly `RotGrid p r` materialized on `[0,PW)×[0,PW)` — a property
  of `instance.js`'s `RotGrid`, checked for shape/occupancy by `checkAxioms`
  (`AxiomsRotGrid`, minus its `Contained` conjunct — §2), not re-derived here. The
  pass-through adds no discrepancy: `rotGrid(p,r) ≡ RotGrid(p,r)` by definition.
- **`L-valid`**: `valid(g,p,py,px,pr)` returns `true` iff `Valid ⟦g⟧ p (py,px) pr =
  true`, by composing `L-occupiedInside` and `L-intersect` with `rg := rotGrid(p,pr)`
  standing for `RotGrid p pr` (`L-rotGrid`) and the offsets `(py,px)` standing for `⊕
  (py,px)` (`GridTranslate`'s `oy,ox` arithmetic is exactly the `y+y1-y2` used by both
  idioms) — `⊕` is never materialized, per D13. `&&`/`negb` match `andb`/`negb`, both
  operands strict `boolean`s.
- **`L-canMovePiece`**: `canMovePiece(dy, dx, s)` returns `true` iff `CanMovePiece
  (dy,dx) ⟦s⟧ = true` — `dirOK(dy,dx)` is exactly `CanMovePiece`'s
  direction-restriction conjunct (`{(0,-1),(0,1),(-1,0)}`, by inspection), and
  `valid(s.mg, s.p, s.py+dy, s.px+dx, s.pr)` is `L-valid` applied to the translated
  position `pyx s ⊕ (dy,dx)` (D14 decomposition, `⊕` never materialized per D13); `&&`
  matches `andb`.
- **`L-resize`**: `resize(g,newGh,fill)` builds, for `y<newGh`: `g[y].slice()` when
  `y<g.length` (fresh row copy) or `fill`-derived row otherwise — matching `Resize`'s
  `λ y, if y<?(Y g + H g) then L g y else fillValue` at `Y g = 0` (D-reach), on
  `[0,newGh)×[0,W g)`. (Not called by any T1 method under D2; retained for
  coverage/testing parity with `Resize`'s definition.)
- **`L-fullLineCount`**: `fullLineCount(g) = Σ_{y=0}^{g.length-1} [isFullLineb(g,y)]`,
  matching `FullLineCountImpl g (H g) (Y g)` unfolded to a sum over `[0,H g)` via
  `L-isFullLineb`, using `Y g = 0` (D-reach) so the abstract starting coordinate
  coincides with the JS loop's `0`. (The Rocq recursion counts down from `H g` to `0`;
  the JS loop counts up — both sum the same multiset of per-`y` booleans.)
- **`L-newPieceState`**: `newPieceState(pNew, s)` returns exactly `α`-image of
  `NewPieceState pNew ⟦s⟧`, field-by-field: `mg`/`gameover`/`clearedLines` pass through
  by identity (no aliasing concept in Rocq; JS sharing the reference is faithful since
  `s.mg` is read-only here); `p := pNew`; `py := InitialY pNew`, `px := InitialX pNew`
  (D14: the two scalar reads standing for `InitialYX pNew`'s pair); `pr := 0`. Codomain
  is a full state-shaped value, not a grid/boolean/number.
- **`L-newPieceYXState`**: `newPieceYXState(pyNew, pxNew, s)` returns exactly
  `α`-image of `NewPieceYXState (pyNew,pxNew) ⟦s⟧`, field-by-field: `mg`/`gameover`/
  `clearedLines` pass through by identity, same argument as `L-newPieceState`; `p :=
  s.p`, `pr := s.pr` (read, not derived, from the input); `py := pyNew`, `px := pxNew`
  (D14: two scalars standing for the pair `pyxNew`).
- **`L-canRotatePiece`** (implementation-freedom helper, no `T1.v` counterpart —
  a definitional-equivalence lemma, not a translation one): `canRotatePiece(cw, s)`
  returns `true` iff `!s.gameover && valid(s.mg, s.p, s.py, s.px, pr2)` where
  `pr2 = mod(s.pr + (cw?-1:1), 4)` — by inspection, this is exactly `t1/model.js`'s own
  `rotatePiece` guard expression, extracted verbatim. Consequently `canRotatePiece(cw,
  s)` is true iff `rotatePiece(cw)` called on a machine in state `s` would return
  `true` — used by T6's `RotateKickPiece` to check this without performing the
  rotation.
- **`L-clearFullLines`** (non-structural, D2 / skill N10): the obligation is the
  extensional equality `clearFullLines(g) ≡ Resize (FilterFullLines g (H g) (Y g) (Y g))
  (H g) (λ_,false)` on `[Y g, Y g + H g)×[X g, X g + W g)`, at `Y g = X g = 0`
  (D-reach) so the box coincides with `g`'s own array indices. Proof sketch, by the
  in-box characterization of both sides:
  - *Height*: `FilterFullLines g (H g) 0 0` (fuel = `H g`, one unit of fuel per row of
    `g`, `i` incrementing only on a non-full row) produces height = the count of
    non-full rows of `g`. `kept.length` in JS is exactly that count by definition of
    `Array.filter`. `Resize (…) (H g) _` pads to height `H g`; `kept.concat(emptyRows(g
    .length - kept.length, …))` pads to `g.length = H g`.
  - *Contents at `[0,count)`*: `FilterFullLines` writes the non-full rows of `g`, in
    ascending-`y` order, at output indices `[0,count)` (structural induction:
    `FilterFullLinesSpec`, `T1Proofs.v`, states this correspondence generically —
    the row at output index `j` is `L g y'` for some non-full `y'`). JS's
    `g.filter(row => !isFullRow(row))` yields exactly the non-full rows of `g` in
    their original order, by `Array.filter`'s order-preservation.
  - *Contents at `[count,H g)`*: both sides are the fill value `false`.
  - Neither side is evaluated outside `[0,H g)×[0,W g)`, so the equality holds
    precisely where `⟦_⟧` is observable.

## 4. Non-aliasing lemma (concrete-only, no Rocq image)

- `union`, `resize`, and `clearFullLines` (via `emptyRows`) each construct **fully
  reconstructive** fresh arrays. These are alias-free unconditionally.
- `rotGrid` is different: `instance.js`'s `RotGrid` returns a **shared** array,
  precomputed once per `(p, r)` and cached, not a fresh copy per call. This is safe
  by a direct argument, not by freshness: every caller of `rotGrid` (`valid`,
  `occupiedInside`/`intersect`/`union` inside it, `view.js`'s `drawPiece`) only reads
  cells, never assigns into the returned array — confirmed by inspection of every
  call site. So the shared instance is never mutated, which is all non-aliasing
  actually requires here; no copy is needed to make it safe.
- `clearFullLines`'s `g.filter(...)` half is **selecting**: `kept` shares row-array
  references with `g`. Safe only because the engine never mutates a row in-place
  anywhere — every field write replaces `this.mg` wholesale (`union`/`clearFullLines`/
  `copyGrid`), never `this.mg[y][x] = …`. **Non-aliasing lemma**: for every reachable
  `js`, no two live references to a row of `js.mg` (or to a cached `rotGrid` result)
  are ever used to mutate that row differently, because no mutation of a row — nor of
  a `rotGrid` output — ever occurs.
- The constructor's `copyGrid(InitialMainGrid)` is fully reconstructive, so `this.mg`
  never aliases the shared `InitialMainGrid` constant.

## 5. `typeOK` = sub-lemma (2a)

Proved inductively in JS, natively (never imported from `TypeOK`, which would be
circular — `typeOK` is itself part of what makes α a homomorphism):

- **Base** (`Init`): `this.mg = copyGrid(InitialMainGrid)` is `HM×WM` all-boolean
  because `InitialMainGrid` is (asserted by `checkAxioms`'s `AxiomsInitialMainGrid`
  check) and `copyGrid` preserves shape. `py,px` are `Number.isInteger` values of
  `InitialY(p)`/`InitialX(p)`, asserted integral by `AxiomsInitialYX`'s range check.
  `pr = 0 ∈ [0,3]`. `gameover` is the `boolean` result of `intersect`. `clearedLines =
  0`. `p` is drawn from the constructor argument, assumed drawn from `Piece` (D6).
- **Step**, one clause per method:
  - `movePiece`: only `py,px` change, to `py+dy`/`px+dx` where `dy,dx ∈ {-1,0,1}`
    (guard-restricted) and `py,px` were integers.
  - `rotatePiece`: only `pr` changes, to `mod(pr + ±1, 4) ∈ [0,4) ∩ ℤ` — satisfies
    `0≤pr≤3`.
  - `fixPiece`: `mg2 = clearFullLines(u)` where `u = union(this.mg, …)` is `HM×WM`,
    each cell `false | Piece` (D1/D8; both `union` and `clearFullLines` preserve the
    input's `H×W` and per-cell domain, §3); `p := pNew` is a `Piece` element (D5,
    asserted under `CHECK_INVARIANTS`); `py,px :=
    InitialY(pNew), InitialX(pNew)`, integers by `AxiomsInitialYX`; `pr := 0`;
    `gameover := boolean` result of `intersect`; `clearedLines := cl =
    fullLineCount(u)`, a non-negative integer count. Additionally, `mg2`'s Rocq origin
    is `(0,0)` (D-reach §2), needed for the *next* step's `typeOK`, not this one's.
  - `fallStep`: delegates entirely to `movePiece`/`fixPiece`; no new field writes.
- Hence `typeOK(js)` holds at every reachable state, discharging (2a). Every lemma in
  §9 assumes `typeOK` as a hypothesis, established once here rather than re-argued per
  action.

## 6. Integer-range safety (§6.8)

Bound: `B = max(HM,WM) + PW - 1`, instantiated (§13.6) to `max(22,10)+4-1 = 25 ≪
Number.MAX_SAFE_INTEGER`. `checkAxioms` asserts `B ≤ MAX_SAFE_INTEGER` and that every
scalar parameter/dimension (`HM,WM,PW,FY,FX`, `InitialY(p)`,`InitialX(p)` for all `p`)
is within `MAX_SAFE_INTEGER` in magnitude (D10).

Every integer-valued subterm reachable in `model.js`'s translated definitions is one
of: a parameter/dimension (bounded above); `py,px` (confined by
`PieceOccupiedInsideBounds` to the main-grid box extended by at most `PW-1` — the
`T1JsBounds.v` lemma `StateBounded`/`StateBounded_of_Correct` reads this envelope off
`Correct`); `pr ∈ [0,3]`; an offset `oy = y+y1-y2`/`ox = x+x1-x2` inside
`fullyContainedIn`/`intersect`/`occupiedInside`/`union`, each operand bounded by the
same envelope, so the difference stays within `±B`; and `clearedLines`, bounded above
by `HM`. Every one of these lies in `(−2^53,2^53)` given `B ≪ 2^53`, by
`T1JsBounds.v`'s `InJSRange_of_absB`. `NoOverflow_of_StateBounded` and
`Overflow_safe_reachable` (`T1JsBounds.v`) extend this pointwise bound to every
reachable state along every trace, closing the `number ≡ ℤ` assumption underlying
every simulation lemma in §9.

## 7. State-bound invariant

`StateBounded` (`T1JsBounds.v`) is the coupling invariant linking `Correct` to the
numeric envelope used in §6: under `Correct`, `PieceOccupiedInsideBounds` confines
`(py,px)` to within `PW-1` of `[0,HM)×[0,WM)`, and `TypeOK` pins `HM,WM`. Since
`Correct` is preserved by every action (§9, transferred via α from `T1Proofs.v`'s own
invariant-preservation theorem), `StateBounded` is preserved along every reachable
trace, and with it the integer-range hypothesis of §6.

## 8. `Init`

`constructor(p)` ≙ `Init p`, field-by-field:

| field | JS | Rocq (`Init p`) | match |
|---|---|---|---|
| `mg` | `copyGrid(InitialMainGrid)` | `InitialMainGrid` | `⟦copyGrid(InitialMainGrid)⟧ = ⟦InitialMainGrid⟧` since `copyGrid` is value-preserving (§4) |
| `p` | constructor arg `p` | `p` | identical |
| `py,px` | `InitialY(p), InitialX(p)` | `InitialYX p` | identical by `L-…` (parameter reads, D14 decomposition) |
| `pr` | `0` | `0` | identical |
| `gameover` | `intersect(ForbiddenGrid,FY,FX,this.mg,0,0)` | `(ForbiddenGrid ∩ InitialMainGrid) ⊈ ∅` | by `L-intersect` (idiom 2, negated) and `mg = InitialMainGrid` as values |
| `clearedLines` | `0` | `0` | identical |

`CHECK_AXIOMS`-gated `checkAxioms()` validates the hypothesis this whole proof is
conditional on (§0); it is not itself part of the field-by-field correspondence.

## 9. Each action

Every lemma below assumes `typeOK(this)` (§5) as a hypothesis.

- **`movePiece(dy,dx)` ≙ `MovePiece (dy,dx)`.**
  - Guard: `!this.gameover && canMovePiece(dy, dx, this)` — textually
    `! gameover s && CanMovePiece dyx s` (`L-canMovePiece`, §3).
  - *Guard fails* → `return false`, no field touched → stuttering step, permitted by
    `Next`'s `Stutter` arm.
  - *Guard holds* → `this.py = py2; this.px = px2;` where `py2 = py+dy, px2 = px+dx`
    match the Rocq `let`-bindings exactly (D14: `pyx2 := (py s + dy, px s + dx)`
    decomposed); `mg,p,pr,gameover,clearedLines` are read but not written.
- **`rotatePiece(cw)` ≙ `RotatePiece cw`.**
  - `pr2 = mod(this.pr + (cw ? -1 : 1), 4)` matches the Rocq `let pr2 := (pr s +
    (if clockwise then -1 else 1)) mod 4` via `L-mod`.
  - *Guard fails* → `return false`, stutter, as above.
  - *Guard holds* → `this.pr = pr2`; all other fields unchanged.
- **`fixPiece(pNew)` ≙ `FixPiece p_new`.**
  - *Guard fails* — `!gameover s && !CanMovePiece (-1,0) s`, matching
    `!(!this.gameover && !canMovePiece(-1, 0, this))`'s negation **exactly**
    (`L-canMovePiece`, §3; textually identical to the Rocq guard, not merely
    equivalent to it) → `return false`, stutter.
  - *Guard holds* → **simultaneous→sequential order** (skill §4b): the Rocq definition
    binds `u := (mg s ∪ (PieceGrid s ⊕ pyx s)) ∩ Full (mg s)` once (idiom 3, `L-union`,
    with `PieceGrid s = RotGrid (p s) (pr s)`), then assigns all seven new-state fields
    simultaneously from `s` and `u`. The JS sequence:
    1. `u = union(this.mg, 0, 0, rotGrid(this.p, this.pr), this.py, this.px)` — reads
       `this.mg, this.p, this.pr, this.py, this.px`, none yet overwritten.
    2. `cl = fullLineCount(u)` — reads only `u` (step 1's result); this is
       `clearedLines := FullLineCount u`, computed *before* `this.mg` is overwritten,
       matching `u` being pre-clear.
    3. `mg2 = clearFullLines(u)` — reads only `u`.
    4. `this.mg = mg2` — writes the new `mg`.
    5. `this.p = pNew` — writes the new `p`; independent of steps 1–4.
    6. `this.py = InitialY(pNew); this.px = InitialX(pNew);` — read the *post*-state
       `p` (`pNew`, written at step 5), matching Rocq's `pyx := InitialYX p_new`
       reading the binder `p_new`, not `s`'s old `p` (D14 decomposition) — no ordering
       hazard.
    7. `this.pr = 0`.
    8. `this.gameover = intersect(ForbiddenGrid, FY, FX, mg2, 0, 0)` — reads the
       *post*-state `mg` (`mg2`, written at step 4), matching `ForbiddenGrid ∩ mg2 ⊈ ∅`
       (idiom 2, negated; req-piece-fix-gameover).
    9. `this.clearedLines = cl` — the value computed at step 2.

    No step reads a field after it has been overwritten with a different value than
    the Rocq definition's corresponding read would see: every read in steps 1–3 is
    against `this`'s pre-state, every later read against a fixed local (`u`, `mg2`,
    `cl`) or the just-written `pNew`/`mg2`. This reproduces `FixPiece`'s simultaneous
    assignment.
- **`fallStep(pNew)` ≙ `FallStep p_new`** — see §10.

## 10. `fallStep` — disjoint-guard sequencing (skill §6.6)

```
Definition FallStep (p_new : Piece) (s : State) : option State :=
  match MovePiece (-1, 0) s with
  | Some s' => Some s'
  | None    => FixPiece p_new s
  end.
```

`MovePiece (-1,0)`'s guard and `FixPiece`'s guard are mutually exclusive: the former
requires `Valid (mg s) (p s) (py s - 1, px s) (pr s)` (downward move is clear), the
latter requires the literal negation — both additionally requiring `¬gameover`.
`fallStep`'s JS body,
```js
if (this.movePiece(-1, 0)) return true;
return this.fixPiece(pNew);
```
tries `movePiece(-1,0)` first: if its guard holds, `movePiece` fires and `fallStep`
returns `true`, matching the `Some s'` branch. If `movePiece`'s guard fails — which,
given `¬gameover` (checked identically by both), happens exactly when `¬Valid(...)` —
`movePiece` returns `false` with no field touched, and `fixPiece(pNew)` is then called
against the *same*, untouched `this`; by the guard-exclusivity above, `fixPiece`'s
guard now holds under the same conditions `FixPiece p_new s` would fire. If
`gameover`, both guards fail: `movePiece` stutters, `fixPiece` also stutters,
`fallStep` returns `false` — a stuttering step, matching neither Rocq branch firing
(both `MovePiece` and `FixPiece` return `None` when `gameover`, so `FallStep`'s `match`
reduces to `FixPiece p_new s = None`, the stutter case of `Next`'s `Fall` arm having no
successor).
