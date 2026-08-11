# implementation.md — ImplementationInstructions for T6

Per-model instructions for the transformation

```
FormalModel (T6.v)  ×  ImplementationInstructions (this file)
      ── rocq-to-js skill ──▶  Code (model.js, view.js, controller.js, instance.js, index.html)
                             ×  Proofs (proofs.md)  ×  Tests (tests/)
```

`rocq-to-js.md` is the **generic process**; this file is the **T6-specific source of
truth**. It is a *delta* over `t5/implementation.md`. Generated artifacts are never
hand-edited: to change one, change this file or `T6.v` and regenerate. All references
to `T6.v`/`T1.v`/`T5.v` are **by definition name**.

## 0. Inputs, outputs, and what is frozen

Codegen-time inputs:
- `T6.v` — the abstract model (refines `T5.v` for `Event5` events only — see §1).
- `T5.v`/`t5/implementation.md` and predecessors — reused.
- this file.
- `rocq-to-js.md` — generic rules (cited as "skill §x").

Runtime input (NOT codegen-time): `instance.js` — re-exports T5's unchanged (§11:
`T6.v` introduces no new abstract parameter).

Outputs: `model.js`, `view.js`, `controller.js`, `instance.js`, `index.html`,
`proofs.md`, `tests/` (§9).

### 0.1 Files reused from T1-T5 unchanged

| file | role in T6 |
|------|-----------|
| `lib/utils.js` | shared primitives |
| `t1/model.js` | the T1 engine (patched, §0.2) — reached as `T5Eng.T1Eng` (flattened) |
| `t5/model.js` | the T5 engine — imported as `T5` (alias for `T`); called as `T5(...)` |
| `t5/instance.js` | re-exported by T6's own `instance.js` (§11) |
| `t5/view.js` | re-exported by T6's own `view.js` (§14) — no new visual state |

### 0.2 Prerequisite: `t1/model.js` patch (must land before T6 codegen)

Two additions to `t1/model.js`'s free-function list, needed for different reasons:
`newPieceYXState` for T5's `DropPiece`, `canRotatePiece` for T6's kick logic.

`T1.v` defines:
```
Definition NewPieceYXState (pyNew pxNew : Z) (s : State) : State :=
  {| py := pyNew
  ;  px := pxNew
     (* rest is unchanged *)
  ;  mg := mg s; p := p s; pr := pr s; gameover := gameover s;
     clearedLines := clearedLines s
  |}.
```
`t1/model.js`:
```js
function newPieceYXState(pyNew, pxNew, s) {
  return {
    mg: s.mg,
    p: s.p,
    py: pyNew,
    px: pxNew,
    pr: s.pr,
    gameover: s.gameover,
    clearedLines: s.clearedLines,
  };
}
```
Both coordinates are overridden unconditionally — a caller that wants one preserved
must pass its current value explicitly. `T5.v`'s `DropPiece` does exactly this
(`NewPieceYXState (gy s) (px s) s` — `px s`, not a literal, to keep the column
unchanged while relocating only the row); `t5/model.js`'s `dropPiece` matches:
```js
const r = T1Eng.newPieceYXState(this.gy, s1.px, s1);
```
(`T1Eng` here is the flattened reference, §0.3 of `t5/implementation.md`.)

`canRotatePiece` is implementation freedom, with no `T1.v` counterpart. `T1.v` itself
needs no such definition (`T1.RotatePiece` computes its own guard inline, once); only
this implementation, wrapping T6's kick logic around it, needs to query "would
rotation succeed" without performing it:
```js
function canRotatePiece(cw, s) {
  const pr2 = mod(s.pr + (cw ? -1 : 1), 4);
  return !s.gameover && valid(s.mg, s.p, s.py, s.px, pr2);
}
```
This factors `T1.RotatePiece`'s own guard expression into a named, side-effect-free
predicate — the same expression, not a re-derivation, so `canRotatePiece(cw, s)` is
true iff `rotatePiece(cw)` would fire on a machine in state `s`.

Required, all landing together in the same patch:
- `t1/model.js`'s free-function list includes `newPieceYXState` and
  `canRotatePiece`.
- `t1/implementation.md` §3, §5: a naming-map row and signature for each.
- `t1/proofs.md`: `L-newPieceYXState` (field-by-field, same shape as
  `L-newPieceState`) and `L-canRotatePiece` (a definitional-equivalence lemma, not
  a translation lemma — it has no Rocq statement to be equivalent to beyond the
  guard expression it's extracted from).
- `t5/model.js`'s `dropPiece` calls `newPieceYXState(this.gy, s1.px, s1)` — three
  arguments, explicit `px`.
- `t5/implementation.md`, `t5/proofs.md`: describe `dropPiece` accordingly.
- `t5/tests/oracle.js`'s independent hand-roll takes an explicit `pxNew` parameter,
  called with `s1.px` at `dropPiece5`'s one call site.

### 0.3 Retrofit: flattened `T1Eng` and `get s1()`, across T2-T5

`t5/implementation.md` §0.3 already specifies this (T3 and T4 gain `get s1()` and a
flattened `T1Eng`; T5 gains the same, plus its `dropPiece`/`shadowY` call sites are
updated to use the flattened `T1Eng` instead of the deep chain). T6 needs nothing
further here — subclassing `T5Eng.Machine` (§1) inherits `get s1()` automatically,
and `T5Eng.T1Eng` is already one hop by construction.

This patch (§0.2 and this retrofit) is a prerequisite for T6 codegen but is not
itself part of T6's own output.

## 1. The refinement, and what it buys — and the structural departure

`T6.State = T5.State` (`T6.v`'s `Definition State := T5.State`) — a type alias, not a new record. This is the
first model in the chain with no new state field to embed. Consequence for the JS
translation: `T6.Machine` subclasses `T5Eng.Machine`, it does not wrap it as a field.
Every prior wrapper (T2-T5) existed because there was a new field (`hold`, `bag_`,
`gy`, etc.) needing a home; here there is nothing to wrap, so subclassing is the
faithful image of `Definition State := T5.State` — literally the same type, not a
new record embedding it. `new T6Eng.Machine(...)` is therefore a genuinely standalone
object: `movePiece`, `rotatePiece`, `fixPiece`, `fallStep`, `holdPiece`, `dropPiece`,
every read-through getter, are directly callable on the instance — no `.s5.`
indirection, because there is no `.s5` field.

Refinement mapping: `fₑ = id : T5.Event -> T5.Event`, `fₛ = id : T6.State ->
T6.State` — both trivial, since there is no state to project away. The refinement
holds only for `Event5` events; `RotateKick` is excluded, the same shape as T3/T5
excluding `Hold`/`Drop`. Per skill §7.1:

- `movePiece`, `rotatePiece`, `fixPiece`, `fallStep`, `holdPiece`, `dropPiece` are
  full uses, realized by inheritance, not by delegating calls. T6.Machine writes
  none of these; they are `T5Eng.Machine`'s own methods, inherited unchanged.
- `rotateKickPiece` is a no-use. No `T5`/`T4`/... action is invoked as a subterm
  before the exclusivity check; the kick attempts do call `this.rotatePiece(cw)`
  (a genuine reuse), but only after establishing, via a pure check, that the plain
  call would otherwise not have fired — see §4-T6a.

Rejected alternative, and why: a composite method (e.g. `rotateWithKick(cw)` trying
both in sequence, exposed as the "main" rotate entry point) was considered and
rejected. `T6.v` defines no event combining `Rotate` and `RotateKick` — that
combination is a caller's sequencing decision, not a model definition. Adding it to
`model.js` would encode behavior `T6.v` itself doesn't specify, the same class of
thing `t1/implementation.md` §12 already rules out for controller-only concerns (DAS
timing, gamepad polling). The sequencing belongs in `controller.js` (§15.2), which
already owns orchestration the model doesn't speak to.

## 2. File layout

```
instance.js            # re-exports t5/instance.js; adds nothing (§11)
view.js                # re-exports t5/view.js; adds nothing (§14) — no new visual state
model.js               # T6 engine: subclasses T5.Machine, adds rotateKickPiece (§5-§7)
controller.js           # controller / entry point; CCW/CW now try a kick on failure (§15)
index.html              # unchanged in structure from T5's
proofs.md               # refinement proof, delta over t5/proofs.md
tests/
  testInstance.js       # re-exports t5/tests/testInstance.js verbatim (T6 has no new params)
  model.unit.test.js
  model.properties.test.js
  model.fuzz.test.js
  oracle.js              # executable T6.v reference (reuses T5's oracle — same state shape)
```

## 3. Naming map (T6.v -> JS)

Only T6-introduced names.

| T6.v | JS |
|------|----|
| `State` (`= T5.State`) | the `T6.Machine` instance — a subclass of `T5Eng.Machine`, not a new shape |
| `RotateKickPiece` | `Machine.rotateKickPiece(cw)` |
| `Event`, `Next` | implicit (controller dispatch + method args); `Event5` case is inheritance, not a forward call |
| `fₑ`, `fₛ` | not emitted (both `id`) |
| `Correct` (`= T5.Correct`) | not emitted — no new invariant, `checkInvariants` is `T5Eng.checkInvariants` unchanged |

## 4. Per-definition translation rules (T6-specific)

§4-T6a. `rotateKickPiece(cw)`:
```js
rotateKickPiece(cw) {
  const s1 = this.s1;                    // flattened getter, inherited from T5.Machine
  let fired = false;
  if (!T1Eng.canRotatePiece(cw, s1)) {    // plainRotFires — pure, no mutation
    const origPx = s1.px;
    s1.px = origPx - 1;                  // left
    fired = this.rotatePiece(cw);        // reuse T5's own method
    if (!fired) {
      s1.px = origPx + 1;                // right, w.r.t. the ORIGINAL position
      fired = this.rotatePiece(cw);
    }
    if (!fired) s1.px = origPx;          // both kicks failed: restore
  }
  if (CHECK_INVARIANTS) T5Eng.checkInvariants(this, 'rotateKickPiece');
  return fired;
}
```
`canRotatePiece` is the one place a pure, side-effect-free check is unavoidable:
unlike a rejected `rotatePiece()` call (which by construction touches nothing),
there is no way to "try a real rotation and undo it" without first knowing whether
it would fire — probing with `valid(...)` a second time inside the loop is
redundant, since `rotatePiece()` already re-checks validity as part of its own
guard. Mutating `s1.px` before calling `rotatePiece` is safe here specifically
because `px` is a trivially-restorable scalar with no side effect beyond itself —
unlike T4's `fixPiece`, where "undoing a draw" isn't a clean no-op. `checkInvariants`
is `T5Eng.checkInvariants` — not redefined, since `T6.Correct = T5.Correct`.

## 5. Free functions emitted by `model.js` (T6.v source order)

None. `T6.v` defines no free function of its own; `canRotatePiece` is reached via
`T1Eng.canRotatePiece` (§0.2) — not redefined here.

## 6. `T6.Machine`

```js
class Machine extends T5Eng.Machine {
  rotateKickPiece(cw) { ... }   // §4-T6a
}
```
No constructor override — `T6.v` defines no new `Init` and there is no new field to
initialize (§0). Every T5 method, getter, and field is inherited verbatim.

## 7. `model.js` exported function

```js
export function T(
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX,
  NextLen,
  MAX_SAFE_INTEGER = Number.MAX_SAFE_INTEGER,
) {
  const T5Eng = T5(Piece, InitialMainGrid, ForbiddenGrid, RotGrid, InitialY, InitialX,
                    PW, FY, FX, NextLen, MAX_SAFE_INTEGER);
  const T1Eng = T5Eng.T1Eng; // flattened, already one hop from T5

  class Machine extends T5Eng.Machine { ... }  // §6

  return {
    ...T5Eng, // free functions, T4Eng, T1Eng, checkAxioms, checkInvariants, snapshot — all unchanged
    Machine,  // overrides T5Eng.Machine with the subclass
  };
}
```
Parameter order identical to T5's — T6 adds no abstract parameters (`T6.v`
declares no `Parameter` of its own at all). `checkAxioms` is `T5Eng.checkAxioms`, `checkInvariants` is
`T5Eng.checkInvariants`, `snapshot` is `T5Eng.snapshot` — none redefined, all reached
via the `...T5Eng` spread. `Machine` is the only key that overrides the spread.

## 8. `proofs.md` (scope)

Delta over `t5/proofs.md`.

1. Scope: safety only. `RotateKick`'s exclusion is structural, per `T6.v` itself.
2. State mapping alpha: `alpha_T6 = alpha_T5`, unchanged — no new field. `T6.Machine`'s
   methods other than `rotateKickPiece` need no per-method argument: they are
   `T5Eng.Machine`'s own, inherited by JS subclassing, not delegating calls that
   need a transfer lemma.
3. `rotateKickPiece` is a no-use, full fresh argument. Guard/exclusivity via
   `canRotatePiece` (cite `t1/proofs.md`'s `L-canRotatePiece` as an imported fact:
   `canRotatePiece(cw, s)` iff `rotatePiece(cw)` would fire). Kick attempts relative
   to the original `px` (both computed from `origPx`, not chained). Mutate-then-
   restore is sound because `px` has no accumulated side effect to undo — contrast
   `t4/proofs.md` §4's `fixPiece`, where it wasn't. `gy`-refresh is inherited from
   the reused `this.rotatePiece(cw)` call, not re-derived.
4. Cap soundness: not applicable.
5. `Init` and every other action: `T5.v`'s own, unchanged; `T6.Machine`'s
   constructor is `T5Eng.Machine`'s, inherited verbatim.

## 9. Tests (`tests/`)

Mirror T5's suite on the same small fixture, plus:

- `testInstance.js` — `export * from '../../t5/tests/testInstance.js';`.
- `oracle.js` — reuses T5's oracle directly, not wrapped: since `T6.State =
  T5.State`, the oracle's state shape is identical, so `initState6`/`movePiece6`/
  `rotatePiece6`/`fixPiece6`/`fallStep6`/`holdPiece6`/`dropPiece6`/`snapshotOf6` are
  all literally `oracle5`'s corresponding functions, re-exported under T6-suffixed
  names for call-site clarity, not reimplemented. `rotateKickPiece6` is the one
  function with real new logic: hand-rolled independently (own `canRotatePiece`,
  own `mod`, not importing `t1/model.js`'s), reconstructing the nested oracle state
  with a modified inner `s1` to try each kick via `oracle5.rotatePiece5`.
- `model.unit.test.js` — golden vectors:
  - `rotateKickPiece` does not fire when plain rotation would (exclusivity),
    leaving the state unchanged.
  - `rotateKickPiece` fires via a left kick when available; via a right kick,
    relative to the original column, when only that one is available.
  - a successful kick moves `px` by exactly +/-1 from where it started — not from
    an intermediate value.
  - `Machine` is standalone: every inherited T5 method is directly callable, no
    wrapping field exists (`'s4' in m`, not `'s5' in m`).
- `model.properties.test.js` — fast-check: `rotateKickPiece` and `rotatePiece` are
  mutually exclusive for every input (never both fire); differential oracle over
  every snapshot field, across all seven event kinds.
- `model.fuzz.test.js` — long random traces including `rotateKickPiece`, `gy`
  invariant checked every step (inherited from T5), differential oracle,
  adversarial `checkAxioms` (delegated, no new axioms).

## 10. Acceptance oracle

A regeneration is correct iff:
1. Every `T6.v` definition with a §3 mapping is realised; every "not emitted" entry
   is absent.
2. `T6.Machine` is a JS subclass of `T5Eng.Machine`, not a wrapper with a new field.
3. `rotateKickPiece` never fires when `canRotatePiece` holds (exclusivity), and
   never mutates anything when it doesn't fire.
4. A successful kick's `px` differs from the original by exactly `+/-1`, never more,
   and the right attempt is relative to the original position, not the failed left
   one.
5. `rotateKickPiece` reuses `this.rotatePiece(cw)` for the actual mutation — it does
   not reimplement rotation validity/mutation/`gy`-refresh itself.
6. The `t1/model.js` patch (§0.2) is present and additive-only; `t5/model.js`'s
   `dropPiece` update (§0.2) is applied.

## 11. Instantiation (`instance.js`)

```js
export * from '../t5/instance.js';
```
Pure re-export. `T6.v` declares no `Parameter` of its own — no abstract parameters to add.

## 12. Generator determinism rules

Inherit predecessors' "reuse over restatement" verbatim. The §0.2/§0.3 patches are
prerequisites of T6 codegen, not part of T6's own output.

## 13. `instance.js` parameters

None beyond T5's. See §11.

## 14. `view.js`

```js
export * from '../t5/view.js';
```
Pure re-export — `T6.v` adds no new state to render, and `rotateKickPiece`'s effect
on the piece (`px`, `pr`) is already drawn by the existing `drawPiece`/`drawGhost`,
which read those fields generically, not by a rotation-specific code path.

## 15. `controller.js` — controller / entry point

Extends T5's `controller.js`. Same input model reused verbatim except where noted.

### 15.1 Initialisation

```js
const eng = T(Piece, InitialMainGrid, ForbiddenGrid,
               RotGrid, InitialY, InitialX, PW, FY, FX, NextLen);

const constants = {
  HM: InitialMainGrid.length,
  WM: InitialMainGrid[0].length,
  PW, FY, FX, NextLen,
  Piece,
  FH: ForbiddenGrid.length,
  FW: ForbiddenGrid[0].length,
  rotGrid: eng.T1Eng.rotGrid,   // flattened one-hop access, made available by T5Eng
                                 // (t5/implementation.md §0.3) — t6/controller.js is
                                 // the first controller in the tower to actually use
                                 // it; t5/controller.js's own rotGrid line still reads
                                 // through the deep chain (eng.T4Eng.T3Eng.T2Eng.T1Eng.rotGrid)
  PANEL_PX: 0,
};
```

### 15.2 `CCW`/`CW` — try plain rotation, then a kick, same keys

```js
function rotate(machine, cw) {
  if (machine.rotatePiece(cw)) return true;
  return machine.rotateKickPiece(cw);
}
```
Bound to the same `z`/`x` keys and gamepad buttons `0`/`1` as T1-T5 — `req-piece-kick`
extends what rotation does, it isn't a separate action the player triggers
differently. This two-call sequencing is a controller-level orchestration decision,
not a `T6.v` definition (§1's rejected alternative) — the model defines two mutually
exclusive events; nothing in `T6.v` says a caller must try both, in this order, on
every rotate input. That decision belongs here for the same reason DAS timing does:
it's a concern the abstract model doesn't speak to at all.

No new keybinding is introduced — `ArrowLeft`/`Right`/`Down`/`Up`, `z`/`x`, `space`,
and the gamepad map are all unchanged from T5's.

### 15.3 Everything else

Unchanged from T5 (§15 there) — `afterAction`, `onTick`, `startGame`,
`handleGameover`, `computeHeld`, `processInput`, `frame`, `sizeCanvas`, `shuffleBag`/
`makeBagsFn`, the keyboard/gamepad event wiring.

### 15.4 `index.html`

Unchanged in structure from T5's.
