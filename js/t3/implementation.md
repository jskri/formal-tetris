# implementation.md — ImplementationInstructions for T3

Per-model instructions for the transformation

```
FormalModel (T3.v)  ×  ImplementationInstructions (this file)
      ── rocq-to-js skill ──▶  Code (model.js, view.js, controller.js, instance.js, index.html)
                             ×  Proofs (proofs.md)  ×  Tests (tests/)
```

`rocq-to-js.md` is the **generic process**; this file is the **T3-specific source of
truth**. T3 refines T2 partially (§1); `t2/implementation.md` fixes rules that apply
here too and this file states only what is specific to T3. Generated artifacts are
never hand-edited: to change one, change this file or `T3.v` and regenerate. All
references to `T3.v`/`T1.v` are **by definition name**.

## 0. Inputs, outputs, and what is frozen

Codegen-time inputs:
- `T3.v` — the abstract model (refines `T2.v` for `Event2` events only — see §1).
- `T2.v`/`t2/implementation.md` and `T1.v`/`t1/implementation.md` — reused.
- this file.
- `rocq-to-js.md` — generic rules (cited as "skill §x").

Runtime input (NOT codegen-time): `instance.js` — re-exports T2's unchanged (§11).

Outputs: `model.js`, `view.js`, `controller.js`, `instance.js`, `index.html`,
`proofs.md`, `tests/` (§9).

### 0.1 Files reused from T1/T2 unchanged

| file | role in T3 |
|------|-----------|
| `lib/utils.js` | shared primitives — imported transitively by `t2/model.js` |
| `t1/model.js` | the T1 engine (patched, §0.2) — reached as `T2Eng.T1Eng` |
| `t2/model.js` | the T2 engine — imported as `T2` (alias for `T`); called as `T2(...)` |
| `t2/instance.js` | re-exported by T3's own `instance.js` (§11) |

### 0.2 Prerequisite: `t1/model.js` patch (must land before T3 codegen)

`T1.v` gained a new `Definition`:
```
Definition NewPieceState (p_new : Piece) (s : State) : State :=
  {| mg := mg s
  ;  p  := p_new
  ;  py := InitialY p_new
  ;  px := InitialX p_new
  ;  pr := 0
  ;  gameover := gameover s
  ;  clearedLines := clearedLines s
  |}.
```
`T3.v`'s `HoldPiece` calls it directly (`T1.NewPieceState p2 (s1 s2_)`, T3.v's
`HoldPiece` definition),
skipping T2 entirely for this one piece of logic. Per "reuse over restatement"
(`t2/implementation.md` §12): this logic is *owned* by `T1.v`, so its JS image belongs
in `t1/model.js`, not duplicated inside `t3/model.js` — even though T3's own outer
function already has direct closure access to `InitialY`/`InitialX` and could
technically inline it. Reuse here is not just style: if `T1.v`'s spawn rule ever
changes, only `t1/model.js` should need updating, and every wrapper (T3, and any future
one) inherits the fix — the same rationale `t2/implementation.md` §4-T2a already gives
for reusing `T1Eng.fullLineCount` instead of re-deriving `clearedLines`.

**Required, additive-only changes** (nothing else in `t1/model.js` changes — `Init` and
`FixPiece`'s bodies are untouched, since `T1.v`'s `Init`/`FixPiece` were not refactored
to call `NewPieceState`, only `T3.v` calls it):

- `t1/model.js`: add one free function, returned alongside the existing §5 list:
  ```js
  // spec: NewPieceState p_new s
  function newPieceState(pNew, s) {
    return {
      mg: s.mg,
      p: pNew,
      py: InitialY(pNew),
      px: InitialX(pNew),
      pr: 0,
      gameover: s.gameover,
      clearedLines: s.clearedLines,
    };
  }
  ```
  Its return type is a full state-shaped plain object (mirroring `NewPieceState :
  State`), not a grid/boolean/number — noted so it isn't mistaken for a bug when
  read next to `rotGrid`/`valid`/`union`.
- `t1/implementation.md` §3 naming map: add `NewPieceState | newPieceState(pNew, s)`.
- `t1/implementation.md` §5: add the signature above.
- `t1/proofs.md`: needs one new lemma, `L-newPieceState` (JS field-by-field match to
  the Rocq record), in the same slot as the other §3 free-function lemmas. Not written
  here — that addendum belongs to `t1/proofs.md`, flagged as a required follow-up, not
  silently skipped.

This patch is a prerequisite for T3 codegen but is not itself part of T3's output.

## 1. The refinement, and what it buys — and what it doesn't

`T3.State` embeds `T2.State` as `s2` and adds `hold : option Piece`, `swapped : bool`.

Refinement mapping (T3.v's `Refinement` section): `fₑ = id : T2.Event →
T2.Event`, `fₛ = s2 : T3.State → T2.State`. **The refinement holds only for `Event2`
events** (T3.v's own `T3RefinesT2` definition quantifies only over `T2.Event`,
wrapped by `Event2`) — `Hold` has no T2/T1
refinement claim at all. Consequence, per skill §7.1's three cases:

- **`movePiece`, `rotatePiece` — full uses.** `T3.MovePiece`/`RotatePiece` are
  `option_map (UnchangedT3Part s)` over the corresponding `T2` call, nothing else —
  `hold`/`swapped` are left alone, not even re-copied to the same value with new logic.
  T2's own action proof (`t2/proofs.md`) transfers unchanged.
- **`fixPiece` — partial use.** `T3.FixPiece` delegates to `T2.FixPiece` *and* writes
  `swapped := false` (req-hold-limit) — `hold` is left alone. Only the `swapped` write
  is new; `t2/proofs.md`'s `fixPiece` argument transfers for the `s2` part.
- **`holdPiece` — no use.** No `T2` or `T1` *action* is invoked at all (`newPieceState`
  is a free function, not an action — using it doesn't make this a "use" in the skill's
  sense). `T1.Correct`/`T2.Correct`/`LevelCorrect` preservation across `Hold` must be
  argued fresh (§8.5), not inherited.

## 2. File layout

```
instance.js            # re-exports t2/instance.js; adds nothing model-level (§11)
model.js               # T3 engine: wraps T2, adds hold/swapped (§5–§7)
view.js                # renderer: hold box (new) + T2's panel/banners (shifted) + grid (§14)
controller.js           # controller / entry point; hold/swap action, space/button 3 (§15)
index.html              # unchanged in structure from T2's (§15.10)
proofs.md               # refinement proof, delta over t2/proofs.md (§8)
tests/
  testInstance.js       # re-exports t2/tests/testInstance.js verbatim (T3 has no new params)
  model.unit.test.js
  model.properties.test.js
  model.fuzz.test.js
  oracle.js              # executable T3.v reference (reuses T2's oracle for s2)
```

## 3. Naming map (T3.v → JS)

Only T3-introduced names; T1/T2 names keep their own maps, reached through nested
inner engines.

| T3.v | JS |
|------|----|
| `State` (record) | the `T3.Machine` instance; fields below |
| `s2` | `this.s2` (a `T2.Machine`) |
| `hold` | `this.hold` (`Piece \| null`) |
| `swapped` | `this.swapped` |
| `gameover` (helper) | `get gameover()` → `this.s2.gameover` |
| `p` (helper) | not emitted as a method — single internal call site, inlined (`this.s2.s1.p`), §4-T3f |
| `Init` | `new eng.Machine(p0)` |
| `Event` | implicit (controller dispatch + method args) |
| `UnchangedT3Part` | not emitted — realized by delegating then leaving `hold`/`swapped` untouched |
| `MovePiece` | `Machine.movePiece(dy, dx)` |
| `RotatePiece` | `Machine.rotatePiece(cw)` |
| `FixPiece` | `Machine.fixPiece(pNew)` |
| `FallStep` | `Machine.fallStep(pNew)` |
| `HoldPiece` | `Machine.holdPiece(pNew)` |
| `NextT2Event`, `Next` | not emitted — JS dispatch already maps controller event → method |
| `fₑ`, `fₛ` | not emitted |
| `score`, `level`, `clearedLines` (T3-level read-through helpers) | proofs.md only; not emitted as functions — JS reads the underlying fields directly (`this.s2.score` etc.) at their few call sites |
| `SwappedImplyHoldSome`, `GameoverImplyNotSwapped`, `Correct`, `NonDecreasingScore`, `NonDecreasingLevel`, `ScoreRisesOnClear`, `HoldMonotone`, `CorrectStep` | proofs.md only; not emitted |

## 4. Per-definition translation rules (T3-specific)

Carry over every T1/T2 rule (guard-before-index, `negb`→`!`, deep-copy, simultaneous→
sequential ordering, D5 non-determinism as explicit args, etc.). New T3 points:

- **§4-T3a.** `newPieceState` is reached as `T2Eng.T1Eng.newPieceState` — not
  redefined (§0.2).
- **§4-T3b.** `movePiece`/`rotatePiece` are one-line delegations to `this.s2`; `hold`/
  `swapped` untouched (full use, §1).
- **§4-T3c.** `fixPiece` delegates to `this.s2.fixPiece(pNew)`, then sets
  `this.swapped = false` from the post-call state (req-hold-limit: holding is allowed
  again after fixing); `hold` untouched (partial use, §1).
- **§4-T3d.** `fallStep` — same disjoint-guard sequencing as T1/T2 (skill §6.6): try
  `movePiece(-1,0)`, else `fixPiece(pNew)`.
- **§4-T3e.** `holdPiece` — the only non-trivial T3 logic, kept at code level (same
  rationale `t2/implementation.md` §6.4 gives for `fixPiece`: the exact ordering is the
  content, not just prose):
  ```js
  holdPiece(pNew) {
    if (!(!this.gameover && !this.swapped)) return false;      // real guard (req-hold-limit)
    const p2 = (this.hold !== null) ? this.hold : pNew;        // req-hold-swap / req-hold-empty
    const oldP = this.s2.s1.p;                                  // 1: read BEFORE overwritten
    const newS1 = T2Eng.T1Eng.newPieceState(p2, this.s2.s1);    // spec: NewPieceState p2 (s1 s2_)
    this.s2.s1.mg           = newS1.mg;                         // 2: written for uniformity (unchanged value)
    this.s2.s1.p            = newS1.p;
    this.s2.s1.py           = newS1.py;
    this.s2.s1.px           = newS1.px;
    this.s2.s1.pr           = newS1.pr;
    this.s2.s1.gameover     = newS1.gameover;
    this.s2.s1.clearedLines = newS1.clearedLines;
    this.hold    = oldP;                                        // 3: req-hold
    this.swapped = true;                                        // 4: req-hold-limit
    if (CHECK_INVARIANTS) checkInvariants(this, 'holdPiece');
    return true;
  }
  ```
  **Ordering note (skill §4b):** step 1 reads `this.s2.s1.p` before step 2 overwrites
  it — the one hazard, mirroring `T3.v`'s `hold := Some (p s)` reading the pre-state
  `p s`, not the value `NewPieceState` just wrote. `score`/`level`/`combo`/
  `perfectClear`/`totalClearedLines` (on `this.s2`) are not touched at all, matching
  T3.v's own `T2.UnchangedT2Part` use inside `HoldPiece` — no field of `this.s2`
  other than `s1` is written.
- **§4-T3f.** `p` (the T3.v helper) has one call site (§4-T3e step 1) and is
  inlined there, not emitted as a named function — not worth a wrapper for a single
  internal read (contrast with `gameover`, which the controller also needs — §6.7).

## 5. Free functions emitted by `model.js` (T3.v source order)

None. `T3.v` defines no non-state free function of its own (`UnchangedT3Part` is a
state-constructor helper, not emitted — same "not emitted, realized by delegating"
treatment `t2/implementation.md` gives `UpdateS1`/`UnchangedT2Part`). `model.js`
reaches `newPieceState` via `T2Eng.T1Eng.newPieceState` (§4-T3a) — not redefined.

## 6. `T3.Machine`

Constructed by `T(...)` (§7). Wraps a `T2.Machine`. Fields mirror `T3.State`.

### 6.1 Constructor — `Init p` (T3.v)

```
this.s2      = new T2Eng.Machine(p)   // T2.Init p
this.hold    = null                    // None
this.swapped = false
```

### 6.2 `movePiece(dy, dx)` — `MovePiece` (T3.v)

```
return this.s2.movePiece(dy, dx);
```

### 6.3 `rotatePiece(cw)` — `RotatePiece` (T3.v)

```
return this.s2.rotatePiece(cw);
```

### 6.4 `fixPiece(pNew)` — `FixPiece` (T3.v)

```
const fired = this.s2.fixPiece(pNew);
if (!fired) return false;
this.swapped = false;   // req-hold-limit
if (CHECK_INVARIANTS) checkInvariants(this, 'fixPiece');
return true;
```

### 6.5 `fallStep(pNew)` — `FallStep` (T3.v)

```
if (this.movePiece(-1, 0)) return true;
return this.fixPiece(pNew);
```

### 6.6 `holdPiece(pNew)` — `HoldPiece` (T3.v) — see §4-T3e for the frozen body.

### 6.7 Read-through getters

Beyond `gameover`, the controller (§15) needs to read every T2-level field it acts on
directly (not only via `snapshot()`, which is per-frame/read-only-observer, not meant
for control-flow branching). Scoped precisely to what `controller.js` actually reads —
not a blanket re-export of all of `T2.State`:

```js
get gameover()          { return this.s2.gameover; }          // T3.v's own `gameover` helper
get level()              { return this.s2.level; }             // fall-speed rescheduling (§15.5)
get totalClearedLines()  { return this.s2.totalClearedLines; } // level-change / banner-capture detection (§15.5)
get combo()               { return this.s2.combo; }             // banner capture (§15.5)
get perfectClear()        { return this.s2.perfectClear; }      // banner capture (§15.5)
get score()                { return this.s2.score; }             // read by view.js via snapshot(), and exposed here for symmetry with the other T2-level getters
get s1()                  { return this.s2.s1; }                // flattened access, §6.10
```

### 6.8 `snapshot(machine)` — extends T2's inline

```
{ ...T2Eng.snapshot(machine.s2), hold: machine.hold, swapped: machine.swapped }
```

### 6.9 `checkInvariants` (D7, default off)

`checkInvariants(s, message, isOccupied = c => Piece.includes(c))` — `isOccupied`
exists purely to be forwarded: T3 itself never needs a non-default value (only `T7`
ever overrides it, to admit its `'garbage'` cell sentinel), but every layer between
`T1` and any `Ti` that does must pass it through untouched, or a descendant's
override never reaches `T1Eng.typeOK` where it's actually checked. If
`CHECK_INVARIANTS`: delegate to `T2Eng.checkInvariants(this.s2, message, isOccupied)`
(not reimplemented — avoids drift), plus the two new T3 conjuncts and one
representational (`typeOK`-style) check:
```js
console.assert(!s.swapped || s.hold !== null, `SwappedImplyHoldSome failed @ ${message}`);
console.assert(!s.gameover || !s.swapped, `GameoverImplyNotSwapped failed @ ${message}`);
console.assert(s.hold === null || Piece.includes(s.hold), `hold ∈ Piece ∪ {null} failed @ ${message}`);
```

### 6.10 Flattened access: `get s1()` and `T1Eng`

`this.s2.s1` already works (T2.Machine's own field is literally named `s1`), but every
model stacked on top of this one would otherwise need one more hop to reach it than
the model below. `get s1()` above, and `T1Eng: T2Eng.T1Eng` in the returned object
(§7), flatten both to a constant one-hop depth regardless of how many models are
stacked — a model built on `t3/model.js` reaches the innermost `T1.Machine` via
`this.s1` (not `this.s2.s1`) and `T1Eng` via `eng.T1Eng` (not `eng.T2Eng.T1Eng`).

## 7. `model.js` exported function

```js
export function T(
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX,
  MAX_SAFE_INTEGER = Number.MAX_SAFE_INTEGER,
) {
  const T2Eng = T2(Piece, InitialMainGrid, ForbiddenGrid, RotGrid, InitialY, InitialX,
                    PW, FY, FX, MAX_SAFE_INTEGER);
  const T1Eng = T2Eng.T1Eng; // flattened, §6.10
  …
}
```
Parameter order identical to T1/T2 — T3 adds no abstract parameters (T3.v's own
"No new parameter" comment). `checkAxioms` is `T2Eng.checkAxioms` (= T1's). Returned object,
in order: (§5: no free functions), `T2Eng`, `T1Eng` (flattened, §6.10), `checkAxioms`,
`checkInvariants`, `Machine`, `snapshot`.

## 8. `proofs.md` (scope)

1. **Scope.** Safety only (no liveness). Additionally, structurally (not
   just "out of controller-scope" the way fall-speed/banners are): `Hold` has *no*
   refinement claim in `T3.v` itself (§1) — this isn't a codegen choice to argue
   around, it's what the model states.
2. **α.** `α_T3(js) = { s2 := α_T2(js.s2); hold := js.hold; swapped := js.swapped }`
   — apply `t2/proofs.md`'s `α_T2` to the embedded inner machine; `hold`/`swapped` map
   directly (nullable primitive / boolean, no coercion).
3. **`movePiece`/`rotatePiece` — full-use transfer**, one line each (§1).
4. **`fixPiece` — partial-use transfer** for the `s2` part; `swapped := false` is the
   only new field write (§4-T3c), trivially matches `T3.FixPiece`'s explicit field.
5. **`holdPiece` — no-use, full fresh argument:**
   - Guard: `!this.gameover && !this.swapped` — both native T3 reads (`gameover` via
     the getter, which is definitionally `T3.v`'s own `gameover` helper; `swapped` a
     plain field), matching T3.v's own `HoldPiece` guard, `! (gameover s) && !
     (swapped s)`.
   - **`T1.Correct (s1 (s2 s))` preservation across `Hold`.** Checking `T1.v`'s five
     `Correct` conjuncts against what `NewPieceState` actually
     touches (`p, py, px, pr` only — confirmed by its definition, §0.2): `TypeOK`,
     `Gameover`, `NoFullLine` are **trivial** (`mg`/`gameover` pass through
     unchanged). `PieceOccupiedInsideBounds`/`PieceOnFreeBlocks` are the only two
     that need `AxiomsRotGrid`'s `FullyContainedIn (RotGrid p 0) (InitialY p)
     (InitialX p) ForbiddenGrid FY FX` (stated `∀ p : Piece` — so it
     applies to `p2` regardless of which piece that turns out to be) combined with
     `AxiomsForbiddenGrid`'s `BBoxInsideBBox` — the *same* lemma
     `T1Proofs.v` already uses for `Init`'s and `FixPiece`'s spawn, re-invoked here,
     not re-derived.
   - **`LevelCorrect (s2 s)` preservation** — trivial: `score`/`level`/`combo`/
     `perfectClear`/`totalClearedLines` are untouched (T3.v's own `HoldPiece` builds
     the new `s2` via `T2.UnchangedT2Part`), so both sides of `LevelCorrect`'s
     equation are literally unchanged.
   - **`SwappedImplyHoldSome`/`GameoverImplyNotSwapped` preservation** — case
     analysis over all five T3 transitions: `Hold` sets `hold := Some(oldP)` and
     `swapped := true` in the same step, satisfying `SwappedImplyHoldSome` directly;
     `Hold`'s guard `!gameover` combined with `gameover` being untouched by
     `NewPieceState` keeps `GameoverImplyNotSwapped` vacuous on this branch (`gameover`
     can't newly become `true` here). `Move`/`Rotate` leave both fields untouched.
     `Fix` sets `swapped := false`, satisfying both implications vacuously regardless
     of `hold`/`gameover`.
   - **`HoldMonotone`** — `hold` is written only by `holdPiece`, always to `Some(...)`
     (never `None`); every other action leaves it untouched. Trivial induction.
   - **Ordering** — §4-T3e's numbered comment is the content of this obligation;
     reproduce it directly (read `this.s2.s1.p` before it's overwritten).
6. **Cap soundness — not applicable.** `Hold` introduces no new arithmetic and
   touches none of the three capped accumulators (`score`, `combo`,
   `totalClearedLines`) — no new cap obligation beyond `t2/proofs.md` §5, which
   already covers every path that *does* touch them (`fixPiece`, unaffected by T3).
7. **`Init`.** `constructor(p)` ≙ `Init p` (`T3.v`), field-by-field: `s2 = new
   T2Eng.Machine(p)` ≙ `T2.Init p`; `hold = null` ≙ `None`; `swapped = false` ≙
   `false`.
8. **Each action — summary.** `movePiece`/`rotatePiece`: one-line delegation, full
   use (§3 above). `fixPiece`: partial use (§4 above). `fallStep`: disjoint-guard
   sequencing, as T1/T2. `holdPiece`: no-use, full argument (§5 above).

## 9. Tests (`tests/`)

Mirror T2's suite (`t2/implementation.md` §9) on the same small fixture, plus T3-
specific coverage.

- **`testInstance.js`** — `export * from '../../t2/tests/testInstance.js';` (T3 has
  no new params; T2's re-export chain already reaches T1's actual fixture).
- **`oracle.js`** — reuses T2's oracle (`t2/tests/oracle.js`) for the `s2` component;
  adds `hold`/`swapped`. Implements `holdPiece`'s field-update independently (its own
  small `newPieceState`-equivalent, hand-rolled — **not** importing
  `T2Eng.T1Eng.newPieceState`, for the same independence reason T2's oracle hand-rolls
  `capAdd`/`natSub`/`natDiv` instead of importing `lib/utils.js`: a bug shared between
  the translation and a helper it reuses should still surface as a mismatch here).
  Exposes `initState3`, `movePiece3`, `rotatePiece3`, `fixPiece3`, `fallStep3`,
  `holdPiece3`, `snapshotOf3`.
- **`model.unit.test.js`** — golden vectors for `holdPiece`:
  - hold when `hold === null` uses `pNew` (req-hold-empty): new current piece is
    `pNew`, `hold` becomes the old current piece, `swapped` becomes `true`.
  - hold when `hold = Some(x)` swaps (req-hold-swap): new current piece is `x`,
    `hold` becomes the old current piece.
  - a second hold attempt before an intervening fix fails (req-hold-limit): stutter,
    no field changes.
  - a fix resets `swapped`, re-enabling hold (req-hold-limit "after fixing").
  - hold is blocked when `gameover`.
  - **narrow-blast-radius check**: a firing hold changes only `p, py, px, pr` (of the
    inner `s1`) and `hold, swapped` (of T3) — `mg`, `s1.gameover`, `s1.clearedLines`,
    `score`, `level`, `combo`, `perfectClear`, `totalClearedLines` are byte-identical
    before/after.
  - spawn position: `py/px/pr` after a hold equal `InitialY(p2)/InitialX(p2)/0`,
    exactly as a fix's respawn — but without a grid change or score/level update.
- **`model.properties.test.js`** — fast-check: `SwappedImplyHoldSome`,
  `GameoverImplyNotSwapped`, `HoldMonotone` hold after every step; `T2.Correct`'s
  conjuncts (delegated) hold after every step including `Hold`; the narrow-blast-
  radius property above, generalized; differential oracle over every snapshot field.
- **`model.fuzz.test.js`** — same shape as T1/T2's: N seeds × M steps, structural +
  the three new invariants + oracle differential, dependency-free.

## 10. Acceptance oracle

A regeneration is correct iff:
1. Every `T3.v` definition with a §3 mapping is realised; every "not emitted" entry
   is absent.
2. `model.js` constructs the T2 engine via `T2(...)` and never reimplements a T1/T2
   free function or duplicates `t1/model.js`/`t2/model.js` — in particular,
   `newPieceState` is reached via `T2Eng.T1Eng.newPieceState`, not reimplemented
   (§0.2, §4-T3a).
3. `tests/` passes on the small fixture: unit + fuzz fully; properties under
   `fast-check` when installed.
4. The differential oracle agrees with `model.js` on every snapshot field over every
   generated trace.
5. `holdPiece` reads `this.s2.s1.p` before overwriting any field of `this.s2.s1`
   (§4-T3e ordering).
6. `checkInvariants` asserts both new T3 conjuncts (§6.9), delegating to
   `T2Eng.checkInvariants` rather than reimplementing it.
7. The `t1/model.js` patch (§0.2) is present and additive-only — `Init`/`FixPiece`
   in `t1/model.js` are byte-unchanged.

## 11. Instantiation (`instance.js`)

```js
export * from '../t2/instance.js';
```
Pure re-export of `t2/instance.js` (itself a re-export of `t1/instance.js`). T3
introduces no abstract parameters. `model.js`'s `checkAxioms` (= T1's) validates it at
`new eng.Machine(...)`.

## 12. Generator determinism rules

Inherit `t1/implementation.md` §12 and `t2/implementation.md` §12's "reuse over
restatement" verbatim. T3 addition: the §0.2 `t1/model.js` patch is a prerequisite of
T3 codegen, not part of T3's own output — do not fold it into `t3/model.js` as a
workaround if the patch is missing; surface it as a blocking TODO instead (skill §12's
own rule: unresolved gaps are surfaced, not guessed around).

## 13. `instance.js` parameters

None beyond T1's. See §11.

## 14. `view.js` — renderer (hold box + shifted panel + T2's grid/banners)

`cellOrigin`/`drawBackground`/`drawGridLines`/`drawBlock`/`drawGrid`/`drawPiece`/
`drawGameOver` are imported from `t1/view.js`, which implements them generally enough
(a `PANEL_PX ?? 0` default) to serve every layer from T1 (no panel) through T5 (two
panels). T3's own `view.js` supplies what's new at this layer: `labelGeometry`,
`holdBoxGeometry`, `drawHoldBox`, and `drawPanel`/`drawBanners`. `t4/view.js` imports
all five of these from `t3` unchanged.

### 14.1 Public API

```js
export function render(canvas, constants, snapshot, pieceColor = {}, banners = null) { … }
```
Same signature as T2's — `hold`/`swapped` arrive through `snapshot` (§6.8); the hold
box's piece rendering reuses `constants.rotGrid` (already present, threaded from
`eng.T2Eng.T1Eng.rotGrid` — §15.2; returns `false | Piece` per cell, `t1/implementation.md`
D1 — the hold box needs no extra handling for this, since it looks up color once via
`pieceColor[snapshot.hold]`, not per grid cell).

### 14.2 Hold-box geometry — labeled, computed once, shared

A `labelGeometry` helper reserves space above the box for a "Hold" caption (the same
convention `drawPreview`'s "Next" label uses at T4), and `holdBoxGeometry` builds on
it —
```js
function labelGeometry(constants) {
  const margin = constants.PANEL_PX * 0.08;
  const labelFont = Math.max(10, Math.floor(constants.PANEL_PX * 0.11));
  return { margin, labelFont, labelHeight: labelFont * 1.2 };
}
function holdBoxGeometry(constants, cellSize) {
  const { margin, labelFont, labelHeight } = labelGeometry(constants);
  const valueFont = Math.max(12, Math.floor(constants.PANEL_PX * 0.17));
  const bannerFont = Math.max(10, Math.floor(constants.PANEL_PX * 0.10));
  const hbSize = Math.min(constants.PW * cellSize, constants.PANEL_PX - 2 * margin);
  const labelY = margin;
  const boxY = labelY + labelHeight;
  const panelTopY = boxY + hbSize + margin; // shared with drawPanel/drawBanners (§14.4)
  return { margin, labelFont, valueFont, bannerFont, labelY, hbSize,
           hbCellSize: hbSize / constants.PW, boxY, panelTopY };
}
```
`valueFont`/`bannerFont` are computed here, alongside `labelFont`, rather than in a
third geometry function — `drawPanel`/`drawBanners` both need them and both already
receive this same `geom` object, so no separate font-geometry pass is needed.
The hold box sits **at the same per-cell scale as the main grid** (`cellSize`, not an
independent scale), clamped against the panel width (`hbSize = min(PW*cellSize,
PANEL_PX - 2*margin)`) — flagged deviation: on a narrow viewport, `PANEL_PX` can be
smaller than `PW * cellSize`, since `PANEL_PX` and `cellSize` are computed
independently (`t2/implementation.md` §15.6a). Computed **once** in `render` and
threaded into `drawHoldBox`/`drawPanel`/`drawBanners` — one shared geometry object,
not three independent recomputations.

### 14.3 `drawHoldBox(ctx, constants, snapshot, geom, pieceColor)`

```
- fillText 'Hold' at (geom.margin, geom.labelY), font geom.labelFont, colour #AAAAAA.
- stroke a square border at (geom.margin, geom.boxY), side geom.hbSize.
  Colour '#555' normally; when snapshot.swapped, dim (ctx.globalAlpha = 0.4) for
  both the border and the piece fill below, restoring alpha = 1 afterward.
- if snapshot.hold !== null:
    rg = constants.rotGrid(snapshot.hold, 0)   // always rotation 0 in the HB
    for y, x in [0, PW):
      if rg[y][x] === false: continue          // exact-sentinel test (D1), not truthiness
      cx = geom.margin + x * geom.hbCellSize
      cy = geom.boxY + (PW - 1 - y) * geom.hbCellSize   // same bottom-up flip as drawPiece
      drawBlock(ctx, cx, cy, geom.hbCellSize, pieceColor[snapshot.hold] ?? '#FFFFFF')
```
`pieceColor` is a required parameter, threaded explicitly since every drawing
function's color source is explicit (D1's colored-blocks representation).

### 14.4 `drawPanel`/`drawBanners` — shifted down

Same structure as T2's (start at `geom.panelTopY` instead of `margin`; same
SCORE/LEVEL/banner-slot layout). Font-size constants: `labelFont: 0.11·PANEL_PX`,
`valueFont: 0.17·PANEL_PX`, `bannerFont: 0.10·PANEL_PX` — the same fractions T4 uses,
so T4 can import these functions directly rather than redefining them.

### 14.5 Piece colour parameter

`pieceColor` (fallback `#FFFFFF`) is threaded explicitly through every drawing
function that needs a piece's fill colour, as in §14.3; `controller.js` passes
`PieceColor`.

### 14.6 Call order inside `render`

```
1. drawBackground
2. drawHoldBox          (label + box, top of panel)
3. drawPanel             (score / level, shifted down by geom.panelTopY)
4. drawBanners            (combo / perfect-clear, shifted down by geom.panelTopY)
5. drawGrid               (locked blocks — colored per-cell, D1)
6. drawGridLines
7. drawPiece              (active piece, clipped)
8. if snapshot.gameover: drawGameOver
```

## 15. `controller.js` — controller / entry point

Extends T2's `controller.js` (`t2/implementation.md` §15). Same input model
(keyboard + gamepad, shared DAS engine, single rAF loop) reused verbatim except where
noted below.

### 15.1 Imports

```js
import { T }       from './model.js';
import { render }  from './view.js';
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
  rotGrid: eng.T2Eng.T1Eng.rotGrid,   // one level deeper than T2's controller (eng.T1Eng.rotGrid)
  PANEL_PX: 0,
};
```

### 15.3 Closure state

```js
let machine;
let lastGravityAt = 0;
let currentGravityPeriod = fallPeriod(1);
let rafId = null;
let disposed = false;
let keyHeld = new Set();
let prevHeld = {};
let repeatTimers = {};
let prevLevel = 1;
let banner = null;
let prevTotalClearedLines = 0;
```
A single `requestAnimationFrame` loop (`frame`, driven by `rafId`) handles both input
polling and gravity: `lastGravityAt`/`currentGravityPeriod` track when the next
automatic fall step is due, in place of a separate `setInterval` timer. `disposed`
guards against `frame` re-scheduling itself after `dispose()` has already fired for
an in-flight frame. No closure state is specific to hold — the hold box has no
separate cooldown timer, it reads `snapshot.swapped` every frame.

### 15.4 Fall speed

```js
const BASE_PERIOD = 1000;
const MIN_PERIOD = 16;
const EPS = 1e-6;

// time-per-cell (seconds) = (0.8 − (level−1)·0.007)^(level−1); ms, rounded, floored.
function fallPeriod(level) {
  const base = Math.max(EPS, 0.8 - (level - 1) * 0.007);
  const secs = Math.pow(base, level - 1);
  return Math.max(MIN_PERIOD, Math.round(BASE_PERIOD * secs));
}
```
`afterAction` (§15.5) recomputes `currentGravityPeriod = fallPeriod(machine.level)`
whenever `machine.level` (now a getter, §6.7) changes, and `frame` fires `onTick`
whenever `now - lastGravityAt >= currentGravityPeriod`.

### 15.5 `afterAction(now)`

```js
function afterAction(now) {
  if (machine.level !== prevLevel) {
    currentGravityPeriod = fallPeriod(machine.level);
    prevLevel = machine.level;
    lastGravityAt = now;
  }

  if (machine.totalClearedLines > prevTotalClearedLines) {
    banner = { combo: machine.combo, perfectClear: machine.perfectClear, t: now };
  }
  prevTotalClearedLines = machine.totalClearedLines;

  if (machine.gameover) handleGameover();
}
```
Every read (`machine.level`, `machine.totalClearedLines`, `machine.combo`,
`machine.perfectClear`, `machine.gameover`) resolves through §6.7's getters. Takes
the current tick's `now` so a level change can restart the gravity accumulator fresh,
off the same clock `frame` already uses for input, rather than a second independent
timer. `holdPiece`'s effect (§15.7) calls `afterAction(now)` too, for uniformity,
even though a hold changes none of the fields `afterAction` inspects — cheap, and
keeps every action path going through the one hook.

### 15.6 `sizeCanvas`

**Unchanged from T2 — no controller-level change.** The hold box is carved out of
the existing `PANEL_PX` budget entirely inside `view.js` (§14.2); it needs no new
viewport-sizing logic here.

### 15.7 Logical actions + keyboard/gamepad handlers

```js
const ACTIONS = {
  LEFT:  { repeat: true,  effect: (now) => { machine.movePiece(0, -1); afterAction(now); } },
  RIGHT: { repeat: true,  effect: (now) => { machine.movePiece(0, 1); afterAction(now); } },
  DOWN:  { repeat: true,  effect: (now) => { machine.fallStep(randomPiece()); afterAction(now); } },
  CCW:   { repeat: false, effect: (now) => { machine.rotatePiece(false); afterAction(now); } },
  CW:    { repeat: false, effect: (now) => { machine.rotatePiece(true); afterAction(now); } },
  HOLD:  { repeat: false, effect: (now) => { machine.holdPiece(randomPiece()); afterAction(now); } },
};

const KEYMAP = new Map([
  ['ArrowLeft', 'LEFT'], ['ArrowRight', 'RIGHT'], ['ArrowDown', 'DOWN'],
  ['z', 'CCW'], ['x', 'CW'], [' ', 'HOLD'],
]);

const GAMEPAD_MAP = new Map([
  [14, 'LEFT'], [15, 'RIGHT'], [13, 'DOWN'],
  [0, 'CCW'], [1, 'CW'], [3, 'HOLD'],
]);
```
Each effect takes the tick's `now` and forwards it to `afterAction` (§15.5). `HOLD`
is `repeat: false` (tap-only, same class as `CCW`/`CW`) — no repetition, per
instruction. `' '` (space) is `KeyboardEvent.key`'s standard value for the space bar;
the existing generic guard (`if (!name) return; e.preventDefault();`) already
suppresses the browser's default page-scroll-on-space behaviour for any recognized
`KEYMAP` entry — no special-casing needed beyond adding the map entry itself.

### 15.8 `processInput(now)` / DAS engine

`HOLD` is just one more entry in the `for (const name of Object.keys(ACTIONS))` loop,
tap-edge branch — same repeat/tap-edge dispatch as every other action.

### 15.9 `handleGameover`

```js
function handleGameover() {
  keyHeld.clear();
  repeatTimers = {};
}
```
Clears held-key and DAS state so no action carries over into the next game once
`startGame()` resets `machine`.

### 15.10 `index.html`

Structurally the same as T2's — only the script's relative import path differs. The
hold box is purely a canvas-drawing concern (§14), not an HTML-structure one.
