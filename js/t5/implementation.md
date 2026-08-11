# implementation.md — ImplementationInstructions for T5

Per-model instructions for the transformation

```
FormalModel (T5.v)  ×  ImplementationInstructions (this file)
      ── rocq-to-js skill ──▶  Code (model.js, view.js, controller.js, instance.js, index.html)
                             ×  Proofs (proofs.md)  ×  Tests (tests/)
```

`rocq-to-js.md` is the **generic process**; this file is the **T5-specific source of
truth**. It is a *delta* over `t4/implementation.md`: T5 refines T4 (partially — see
§1), so everything T4 already fixed is reused unless this file overrides it. Generated
artifacts are never hand-edited: to change one, change this file or `T5.v` and
regenerate. All references to `T5.v`/`T1.v` are **by definition name**.

## 0. Inputs, outputs, and what is frozen

Codegen-time inputs:
- `T5.v` — the abstract model (refines `T4.v` for `Event4` events only — see §1).
- `T4.v`/`t4/implementation.md`, `T3.v`/`t3/implementation.md`, etc. — reused.
- this file.
- `rocq-to-js.md` — generic rules (cited as "skill §x").

Runtime input (NOT codegen-time): `instance.js` — re-exports T4's unchanged (§11:
`T5.v` introduces no new abstract parameter).

Outputs: `model.js`, `view.js`, `controller.js`, `instance.js`, `index.html`,
`proofs.md`, `tests/` (§9).

### 0.1 Files reused from T1–T4 unchanged

| file | role in T5 |
|------|-----------|
| `lib/utils.js` | shared primitives — imported transitively |
| `t1/model.js` | the T1 engine (patched, §0.2) — reached as `T4Eng.T1Eng` (flattened, §0.3) |
| `t4/model.js` | the T4 engine — imported as `T4` (alias for `T`); called as `T4(...)` |
| `t4/instance.js` | re-exported by T5's own `instance.js` (§11) |

### 0.2 Prerequisite: `t1/model.js` patch (must land before T5 codegen)

`T1.v` gains a new `Definition`:
```
Definition NewPieceYXState (pyNew pxNew : ℤ) (s : State) : State :=
  {| py := pyNew
  ;  px := pxNew
     (* rest is unchanged *)
  ;  mg := mg s; p := p s; pr := pr s; gameover := gameover s;
     clearedLines := clearedLines s
  |}.
```
`T5.v`'s `NewPieceYXState` (T5-level) calls it directly (`T1.NewPieceYXState pyNew
pxNew s1`), skipping T2–T4 entirely for this one piece of logic — same pattern as
`T3.v`'s `HoldPiece` reaching `T1.NewPieceState`. Per "reuse over restatement"
(`t2/implementation.md` §12): this logic is owned by `T1.v`, so its JS image belongs
in `t1/model.js`.

**Required, additive-only changes** (nothing else in `t1/model.js` changes):

- `t1/model.js`: add one free function, returned alongside the existing list:
  ```js
  // spec: NewPieceYXState pyNew pxNew s
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
  Both `py` and `px` are overridden unconditionally; every other field is copied
  through by reference or value. A caller that wants one coordinate unchanged must
  pass its current value explicitly (`T5.v`'s `DropPiece` does exactly this — `px s`,
  not a literal, to keep the column unchanged while relocating only the row).
  Distinct from `newPieceState` (§0.2 of `t3/implementation.md`), which instead
  overrides `p`/`py`/`px`/`pr` for a freshly-spawned piece — the two functions serve
  different callers (`HoldPiece` spawns a different piece type; `DropPiece` relocates
  the same piece) and neither subsumes the other.
- `t1/implementation.md` §3 naming map: add
  `NewPieceYXState | newPieceYXState(pyNew, pxNew, s)`.
- `t1/implementation.md` §5: add the signature above, alongside `newPieceState`'s
  entry, with the same note about its return type being a full state-shaped object.
- `t1/proofs.md`: needs one new lemma, `L-newPieceYXState`, in the same slot as
  `L-newPieceState` — a required follow-up to that file, not written here.

Also add, in the same patch, an implementation-freedom helper with no `T1.v`
counterpart — needed by T6, not by T5, but landing alongside `newPieceYXState` since
both touch `t1/model.js`'s free-function list at the same time:
```js
function canRotatePiece(cw, s) {
  const pr2 = mod(s.pr + (cw ? -1 : 1), 4);
  return !s.gameover && valid(s.mg, s.p, s.py, s.px, pr2);
}
```
This factors `T1.RotatePiece`'s own guard into a named, side-effect-free predicate —
not a translation of any `T1.v` definition, an addition made because the guard
expression it needs already lives in `t1/model.js`.

This patch is a prerequisite for T5 codegen but is not itself part of T5's output.

### 0.3 Retrofit: flattened `T1Eng` and `get s1()`, across T2–T5

Every `model.js` from T2 on nests one level deeper than the last to reach `T1Eng`
(`eng.T1Eng` for T2, `eng.T2Eng.T1Eng` for T3, …), and `Machine` instances nest the
same way to reach the innermost `T1.Machine` (`this.s1` for T2, `this.s2.s1` for T3,
…). Both chains get one hop longer with every new model in the tower, with no bound
— a real, worsening coupling problem, not a style preference. Fixed by retrofitting
T2–T5's `model.js`:

- Each model's returned object gains `T1Eng: <parent>Eng.T1Eng` (T2's own `T1Eng` is
  already direct — no change there). E.g. `t3/model.js`: `T1Eng: T2Eng.T1Eng`.
- Each model's `Machine` class gains `get s1() { return this.<parent-field>.s1; }`
  (T2.Machine needs nothing — its own field is already literally named `s1`). E.g.
  `t3/model.js`: `get s1() { return this.s2.s1; }`.

Both compose automatically: a model built on `t5/model.js` (T6, subclassing
`T5Eng.Machine` — see §1) inherits `get s1()` for free, and reaches `T1Eng` in one
hop (`T5Eng.T1Eng`) without any T6-specific plumbing. This is purely additive to
T2–T5 — every existing `.T4Eng.T3Eng...` access path and `.s4.s3.s2.s1` access path
still resolves exactly as before; nothing is removed.

## 1. The refinement, and what it buys

`T5.State` embeds `T4.State` as `s4` and adds `gy : ℤ`, the y-coordinate of the
current piece's shadow (`x`/rotation are shared with the active piece, so only `y`
is new state — `T5.v`'s own header comment).

Refinement mapping (`T5.v`'s `Definition fₑ : T4.Event → T4.Event := id.` and
`Definition fₛ: T5.State → T4.State := s4.`): `fₑ = id : T4.Event → T4.Event`,
`fₛ = s4 : T5.State → T4.State`. **The refinement holds only for `Event4` events**
(`T5.v`'s own comment: "The refinement holds only when excluding Drop, i.e. it
holds on T4 events.") — `Drop` has no T4/T3/T2/T1 refinement claim at all, the same
shape as T3's exclusion of `Hold`. Per skill §7.1's three cases:

- **`movePiece`, `rotatePiece`, `fixPiece`, `holdPiece` — full uses.** Each is
  `option_map (UpdateShadowY s) (T4.<Action> ... (s4 s))` — the underlying T4 call
  is untouched; the only addition is recomputing `gy` from the post-action state,
  which is itself a pure function of that state, not new guard logic.
- **`fallStep`** delegates to `movePiece`/`fixPiece`, both already covered.
- **`dropPiece` — no use.** No T4 (or lower) *action* is invoked before the piece is
  relocated — `NewPieceYXState` is a state constructor, not an action. `dropPiece`
  then calls `fixPiece` (a genuine T5 action), so it is a **partial** no-use: the
  relocation step has no T4 counterpart, but the trailing fix does.

## 2. File layout

```
instance.js            # re-exports t4/instance.js; adds nothing (§11)
model.js               # T5 engine: wraps T4, adds gy (§5–§7)
view.js                # renderer: ghost piece (new) + T4's grid/panels/preview (§14)
controller.js           # controller / entry point; drop action, Up/D-pad-up (§15)
index.html              # unchanged in structure from T4's (§15.6)
proofs.md               # refinement proof, delta over t4/proofs.md (§8)
tests/
  testInstance.js       # re-exports t4/tests/testInstance.js verbatim (T5 has no new params)
  model.unit.test.js
  model.properties.test.js
  model.fuzz.test.js
  oracle.js              # executable T5.v reference (reuses T4's oracle for s4)
```

## 3. Naming map (T5.v → JS)

Only T5-introduced names; T1–T4 names keep their own maps, reached through nested
inner engines.

| T5.v | JS |
|------|----|
| `State` (record) | the `T5.Machine` instance; fields below |
| `s4` | `this.s4` (a `T4.Machine`) |
| `gy` | `this.gy` (`number`) — plain field, no getter (T5's own, not nested) |
| `ShadowYImpl` / `ShadowY` | `shadowY(s1)` — combined into one function (JS has no
  `nat`/`ℤ` distinction to keep them separate for), iterative rather than recursive
  (skill: a `Fixpoint` on a strictly-decreasing measure becomes a loop — here the
  measure is an explicit fuel count, not `py` itself, since `py` can legitimately go
  negative, down to `-(PW-1)`) |
| `Init` | `new eng.Machine(bagsFn)` |
| `Event` | implicit (controller dispatch + method args) |
| `UnchangedT5Part` | not emitted as a standalone export — used only inside the
  `dropPiece` relocation step (§4-T5d), where `gy` is left at whatever value it had
  before relocation, since the very next call (`fixPiece`) recomputes it via
  `UpdateShadowY` regardless |
| `UpdateShadowY` | `updateShadowY()` — a method, called only when the delegated
  action fired (§4-T5b) |
| `MovePiece` | `Machine.movePiece(dy, dx)` |
| `RotatePiece` | `Machine.rotatePiece(cw)` |
| `FixPiece` | `Machine.fixPiece(bagNew)` |
| `FallStep` | `Machine.fallStep(bagNew)` |
| `HoldPiece` | `Machine.holdPiece(bagNew)` |
| `NewPieceYXState` (T5-level) | not emitted as a standalone function — its body
  (unwrap to `s1`, call `T1.NewPieceYXState`, rewrap) is realized inline at
  `dropPiece`'s one call site (§4-T5d), the same treatment T3 gave its own single-use
  `p` helper |
| `DropPiece` | `Machine.dropPiece(bagNew)` |
| `NextT4Event`, `Next` | not emitted |
| `fₑ`, `fₛ` | not emitted |
| `mg`, `p`, `py`, `px`, `pr`, `gameover` (T5-level accessors) | proofs.md only; not emitted — each is `T4.<name>(s4 s)`, with no runtime consumer beyond what `T5.Machine`'s own read-through getters (§6.8) already expose for `gameover` |
| `ValidPieceCannotGoDown`, `LowestShadowY`, `Correct` | proofs.md only; not emitted |

## 4. Per-definition translation rules (T5-specific)

Carry over every T1–T4 rule. New T5 points:

- **§4-T5a. `shadowY(s1)` — iterative, combining `ShadowYImpl`+`ShadowY`, fuel-bounded.**
  ```js
  function shadowY(s1) {
    const valid = T1Eng.valid; // flattened (§0.3)
    let py = s1.py;
    let fuel = py + PW - 1;
    while (fuel > 0) {
      if (!valid(s1.mg, s1.p, py - 1, s1.px, s1.pr)) break;
      py -= 1;
      fuel -= 1;
    }
    return py;
  }
  ```
  Takes a T1-state-shaped object (duck-typed — any object with `mg`/`p`/`py`/`px`/
  `pr`; in practice always `this.s1` — the flattened getter, §0.3 — a real
  `T1.Machine`). The recursion
  measure is **fuel, not `py` itself** — `py` can legitimately go negative, down to
  `-(PW-1)`: a piece is anchored in a fixed `PW×PW` rotation grid specifically so
  that rotating doesn't offset `py`/`px`, and `AxiomsRotGrid` only guarantees *some*
  occupied cell exists (`T1.v`), not that it sits at local row 0 — a piece whose
  only occupied cells sit near the top of its own bounding box can have its anchor
  go correspondingly negative while every occupied cell stays inside the main grid.
  Capping the search at `py > 0` (treating row 0 as an absolute floor) stops too
  early for such pieces/rotations: `Valid(0)`/`Valid(-1)`/etc. can genuinely hold,
  and `T1.MovePiece`/`T1.FixPiece` (unbounded, `ℤ`-typed) correctly permit descending
  further — so a `py > 0`-bounded shadow would under-report how far the piece can
  actually fall, disagreeing with where a real drop or fall-to-floor sequence lands.
  `AxiomsRotGrid`'s guarantee (≥1 occupied cell, at local row ≤ `PW-1`) forces
  `Valid(py)` false once `py ≤ -PW`, so `fuel = py + PW - 1` is an exact bound: it
  is consumed by one unit per row descended, and the invariant `fuel = py_current +
  PW - 1` holds throughout, so by the time `fuel` reaches 0, `py` has reached
  exactly `-(PW-1)` — the true floor, forced invalid one row further regardless of
  which piece/rotation this is — without needing to check that row explicitly.
- **§4-T5b. `movePiece`/`rotatePiece`/`fixPiece`/`holdPiece` — full uses, each
  recomputing `gy` only on success.**
  ```js
  movePiece(dy, dx) {
    const fired = this.s4.movePiece(dy, dx);
    if (fired) this.updateShadowY();
    if (CHECK_INVARIANTS) checkInvariants(this, 'movePiece');
    return fired;
  }
  ```
  (`rotatePiece`, `fixPiece`, `holdPiece` follow the identical shape, delegating to
  `this.s4.rotatePiece`/`fixPiece`/`holdPiece` respectively.) `updateShadowY()`
  recomputes `this.gy` from the post-action `this.s1` (flattened, §0.3) — a plain field
  write, not a guard. Guard failure (`fired === false`) leaves `gy` untouched,
  extending "guard fails ⟹ zero mutation" to T5's own field: `option_map`'s `None`
  case in `T5.v` never reaches `UpdateShadowY` either, so this is not a new
  obligation, just the existing one carried one level deeper.
  Recomputing on a pure vertical move (`dy=-1, dx=0`, `fallStep`'s own use) is
  redundant but not wrong — `shadowY` doesn't depend on `py`, only on `mg`/`p`/`px`/
  `pr` (visible from §4-T5a: the loop's *result* depends on where `Valid` first
  fails while descending from the start point, not on which valid start point was
  used) — so recomputing unconditionally is simpler than special-casing by
  direction, and always correct.
- **§4-T5c. `fallStep(bagNew)`.** Unchanged shape from T1–T4:
  ```js
  fallStep(bagNew) {
    if (this.movePiece(-1, 0)) return true;
    return this.fixPiece(bagNew);
  }
  ```
- **§4-T5d. `dropPiece(bagNew)` — single upfront guard, no peek-then-commit.**
  ```js
  dropPiece(bagNew) {
    T4Eng.assertPieceSet(bagNew);
    if (this.gameover) return false;
    const s1 = this.s1;                              // flattened getter (§0.3)
    const r = T1Eng.newPieceYXState(this.gy, s1.px, s1); // px s, not a literal — see below
    s1.mg = r.mg; s1.p = r.p; s1.py = r.py; s1.px = r.px; s1.pr = r.pr;
    s1.gameover = r.gameover; s1.clearedLines = r.clearedLines;
    return this.fixPiece(bagNew);   // guaranteed to fire — see below
  }
  ```
  This is unlike `t4/model.js`'s `fixPiece`, which needed to defer its mutation
  until success was confirmed because no invariant guaranteed the underlying
  `T3.FixPiece` guard would hold at the point it was called. Here, a single
  upfront check suffices: `LowestShadowY` (`T5.v`) states
  `gameover(s4 s) = false → gy s ≤ py(s4 s) ∧ ValidPieceCannotGoDown s (gy s) ∧ ...`
  — i.e., whenever `¬gameover` holds *before* the drop, `Valid(gy)` and `¬Valid(gy-1)`
  both hold for the *current* `px`/`pr`/`mg`. Relocating `py` to `gy` therefore
  preserves `T1.Correct`'s `PieceOccupiedInsideBounds`/`PieceOnFreeBlocks` (via
  `Valid(gy)`), and `T1.FixPiece`'s guard (`¬gameover ∧ ¬Valid(py-1,...)`) is
  exactly `¬Valid(gy-1)`, already established. The one check this method makes —
  `this.gameover` — is the only way `FixPiece` could otherwise reject, so no
  post-relocation rejection is reachable, and no peek-then-commit restructuring is
  needed. `newPieceYXState` overrides *both* coordinates unconditionally, so
  `dropPiece` must pass `s1.px` explicitly to keep the column unchanged — passing a
  literal here would reset the piece's column on every hard drop. `s1.mg` is
  reassigned to `r.mg` for uniformity even though the two are the same reference
  (`newPieceYXState` doesn't touch `mg`) — same treatment `t3/model.js`'s
  `holdPiece` gives the analogous field in `T1.NewPieceState`'s result.
- **§4-T5e. `checkInvariants` recomputes `shadowY` and compares, only when
  `¬gameover`** (mirroring `LowestShadowY`'s own guard) — see §6.9.

## 5. Free functions emitted by `model.js` (T5.v source order)

- `shadowY(s1)` — §4-T5a.

## 6. `T5.Machine`

### 6.1 Constructor — `Init bags H` (T5.v)

```js
constructor(bagsFn) {
  this.s4 = new T4Eng.Machine(bagsFn);   // spec: T4.Init bags H
  this.gy = shadowY(this.s1);   // spec: ShadowY s4 (this.s1 flattened, §0.3)
}
```

### 6.2–6.5 `movePiece`/`rotatePiece`/`fixPiece`/`holdPiece` — see §4-T5b.

### 6.6 `fallStep(bagNew)` — see §4-T5c.

### 6.7 `dropPiece(bagNew)` — see §4-T5d.

### 6.8 Read-through getters

Same five as T4's (`gameover`, `level`, `totalClearedLines`, `combo`,
`perfectClear`), each one level deeper (`this.s4.<field>`) — every field
`controller.js` reads directly outside `snapshot()`.

### 6.9 `checkInvariants` (D7, default off)

```js
const CHECK_INVARIANTS = false;

function checkInvariants(s, message, isOccupied = (c => Piece.includes(c))) {
  T4Eng.checkInvariants(s.s4, message, isOccupied);
  if (!s.gameover) {
    const expected = shadowY(s.s1); // flattened (§0.3)
    console.assert(s.gy === expected, `LowestShadowY (gy matches shadowY) failed @ ${message}`);
    console.assert(s.gy <= s.s1.py, `gy <= py failed @ ${message}`);
  }
}
```
`isOccupied` exists purely to be forwarded (only `T7` ever overrides it, to admit its
`'garbage'` cell sentinel) — T5 itself never needs a non-default value.
The `¬gameover` guard mirrors `LowestShadowY`'s own precondition exactly — without
it, a freshly-spawned piece under `gameover = true` isn't guaranteed `Valid` at its
own position, and `shadowY`'s recomputation would be checking a claim `T5.v` itself
doesn't make in that state.

### 6.10 `updateShadowY()`

```js
updateShadowY() {
  this.gy = shadowY(this.s1);
}
```

### 6.11 `snapshot(machine)` — extends T4's inline

```js
function snapshot(machine) {
  return {
    ...T4Eng.snapshot(machine.s4),
    gy: machine.gy,
  };
}
```

## 7. `model.js` exported function

```js
export function T(
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX,
  NextLen,
  MAX_SAFE_INTEGER = Number.MAX_SAFE_INTEGER,
) {
  const T4Eng = T4(Piece, InitialMainGrid, ForbiddenGrid, RotGrid, InitialY, InitialX,
                    PW, FY, FX, NextLen, MAX_SAFE_INTEGER);
  const T1Eng = T4Eng.T1Eng; // flattened (§0.3)
  …
}
```
Parameter order identical to T4's — T5 adds no abstract parameters (`T5.v`
declares no `Parameter` of its own at all). `checkAxioms` is `T4Eng.checkAxioms` unchanged. Returned object,
in order: (§5: `shadowY`), `T4Eng`, `T1Eng` (flattened, §0.3), `checkAxioms`,
`checkInvariants`, `Machine`, `snapshot`.

## 8. `proofs.md` (scope)

Delta over `t4/proofs.md`.

1. **Scope.** Safety only. `Drop` has no refinement claim in `T5.v` itself (§1) —
   structural, not a codegen choice, same as `t3/proofs.md`'s treatment of `Hold`.
2. **α.** `α_T5(js) = { s4 := α_T4(js.s4); gy := js.gy }` — `gy` maps directly (a
   plain integer, no coercion).
3. **`movePiece`/`rotatePiece`/`fixPiece`/`holdPiece` — full-use transfer, plus one
   new obligation each: `gy` after a successful call equals `shadowY` of the
   post-call state.** This is definitional, not inductive — `updateShadowY()`
   *is* that computation, called exactly when `T5.v`'s `option_map` would reach
   `UpdateShadowY`. The stuttering-step property (guard fails ⟹ zero mutation)
   extends to `gy` for the same reason: the failure path never calls
   `updateShadowY()`.
4. **`fallStep`** — disjoint-guard sequencing, unaffected, as T1–T4.
5. **`dropPiece` — no-use for the relocation step, full use for the trailing fix.**
   - **Guard:** the single `this.gameover` check.
   - **Soundness of the relocation, given `¬gameover` at the pre-drop state:** cite
     `LowestShadowY` as an imported fact — `gy s ≤ py(s4 s)`,
     `ValidPieceCannotGoDown s (gy s)` (i.e. `Valid(gy)` and `¬Valid(gy-1)`), both
     conditional on `¬gameover(s4 s)`, established at `Init` and preserved by every
     T5 action (item 3 above shows `gy` always equals a fresh `shadowY` computation,
     and `shadowY`'s own loop invariant — proved separately, not re-derived here —
     guarantees its result satisfies `ValidPieceCannotGoDown` whenever the starting
     `Valid(py)` holds, which `T4.Correct`'s `PieceOnFreeBlocks` supplies whenever
     `¬gameover`). `T1.NewPieceYXState`'s relocation therefore preserves
     `PieceOccupiedInsideBounds`/`PieceOnFreeBlocks` at the relocated state (via
     `Valid(gy)`), and the relocated state's `py - 1` is exactly `gy - 1`, so
     `T1.FixPiece`'s guard (`¬gameover ∧ ¬Valid(py-1,...)`) is exactly
     `¬Valid(gy-1)` — already established. No case where the relocation is followed
     by a rejection exists; no peek-then-commit ordering is needed (contrast
     `t4/proofs.md` §4).
   - **The trailing `fixPiece` call** is covered by item 3 above — its own
     `gy`-refresh obligation is inherited, not re-argued.
6. **Cap soundness — not applicable.** `dropPiece` introduces no new arithmetic and
   touches no capped accumulator; it only relocates `py` and then delegates to
   `fixPiece`, already covered by `t2/proofs.md` §5.
7. **`Init`.** `constructor(bagsFn)` ≙ `Init bags H` (`T5.v`): `this.s4 = new
   T4Eng.Machine(bagsFn)` ≙ `T4.Init bags H`; `this.gy = shadowY(...)` ≙
   `ShadowY s4`, by definition.
8. **Each action — summary.** `movePiece`/`rotatePiece`/`fixPiece`/`holdPiece`: full
   use, `gy`-refresh-on-success (§3). `fallStep`: disjoint-guard sequencing (§4).
   `dropPiece`: no-use relocation + full-use fix, single upfront guard sufficient
   given `LowestShadowY` (§5).

## 9. Tests (`tests/`)

Mirror T4's suite (`t4/implementation.md` §9) on the same small fixture, plus:

- **`testInstance.js`** — `export * from '../../t4/tests/testInstance.js';`.
- **`oracle.js`** — reuses T4's oracle for `s4`; hand-rolls `shadowY` and
  `newPieceYState` independently (own loop, own field-copy, not importing
  `model.js`/`t1/model.js` — same independence discipline as every prior oracle).
  Exposes `initState5`, `movePiece5`, `rotatePiece5`, `fixPiece5`, `fallStep5`,
  `holdPiece5`, `dropPiece5`, `snapshotOf5`.
- **`model.unit.test.js`** — golden vectors:
  - **Overhang board, hand-crafted:** a board where the piece's column has a
    locked shelf a few rows up and open space beneath it, down to the true floor
    (which may be below row 0 — see the next bullet). `shadowY` must return the
    shelf-top row, not the true floor beneath it — test this directly, not just
    the unobstructed case.
  - **Unobstructed-column floor, per piece type:** on an empty column, `shadowY`
    must equal `-(minRow of that piece's rotation-0 grid)`, not `0` — verified
    against the real instance, this is `-1` for six of the seven standard pieces
    and `-2` for `I`, since their occupied cells start at local row 1 or 2, not 0
    (`AxiomsRotGrid` only guarantees *some* occupied cell, not one at row 0). Test
    every piece type in `Piece`, not just one.
  - `shadowY` unaffected by a pure vertical move: compute it, `movePiece(-1,0)`,
    recompute — same value, even when that value is negative.
  - `shadowY` changes after a horizontal move or a rotation, when the new
    column/orientation has a different floor/obstruction.
  - `dropPiece` locks the piece at exactly `gy` (not `py`), and fires whenever
    `¬gameover`, regardless of how far above the floor the piece currently sits —
    including from spawn, where the true floor can be several rows below `0`.
  - `dropPiece` blocked by `gameover`.
  - narrow-blast-radius: a successful `dropPiece` changes exactly what a
    `fixPiece` at row `gy` would change, plus `gy` itself (refreshed for the new
    piece) — nothing else.
- **`model.properties.test.js`** — fast-check: `gy` always equals a fresh
  `shadowY` computation after every step (when `¬gameover`); `gy ≤ py` always;
  `gy ≥ -(PW-1)` always (the fuel bound); differential oracle over every snapshot
  field, across all six event kinds.
- **`model.fuzz.test.js`** — long random traces including `dropPiece`, `gy`
  invariant checked every step, differential oracle, adversarial `checkAxioms`
  (delegated, no new axioms to test directly).

## 10. Acceptance oracle

A regeneration is correct iff:
1. Every `T5.v` definition with a §3 mapping is realised; every "not emitted" entry
   is absent.
2. `model.js` never reimplements a T1–T4 free function; `newPieceYState` is reached
   via `T1Eng.newPieceYXState` (flattened, §0.3), not reimplemented (§0.2).
3. `movePiece`/`rotatePiece`/`fixPiece`/`holdPiece` each call `updateShadowY()` if
   and only if the delegated T4 call fired.
4. `dropPiece` performs exactly one `gameover` check, before relocating `py`, and
   never defers/re-checks after relocation.
5. `checkInvariants` recomputes `shadowY` and compares, gated on `¬gameover`.
6. `tests/` includes the overhang golden vector (§9) and passes it.
7. The `t1/model.js` patch (§0.2) is present and additive-only.

## 11. Instantiation (`instance.js`)

```js
export * from '../t4/instance.js';
```
Pure re-export. `T5.v` declares no `Parameter` of its own — no abstract parameters to add.

## 12. Generator determinism rules

Inherit `t1/implementation.md` §12 and subsequent models' "reuse over restatement"
verbatim. The §0.2 `t1/model.js` patch is a prerequisite of T5 codegen, not part of
T5's own output — an unresolved gap here is surfaced as a blocking TODO, not guessed
around.

## 13. `instance.js` parameters

None beyond T4's. See §11.

## 14. `view.js` — renderer (ghost piece + T4's grid/panels/preview)

T5's `view.js` redefines nothing from T1–T4 — every grid/panel/hold/preview primitive
(`cellOrigin`/`drawBackground`/`drawGridLines`/`drawBlock`/`drawGrid`/`drawPiece`/
`drawGameOver`/`labelGeometry`/`holdBoxGeometry`/`drawHoldBox`/`drawPanel`/`drawBanners`/
`effectiveRowRange`/`previewGeometry`/`drawPreview`) is imported from `t4/view.js`
(itself importing the grid primitives from `t1`, hold/panel/banners from `t3`) and
re-exported. `drawGhost` is the only genuinely new function here — it needs
`snapshot.gy`, a field that doesn't exist before this layer.

### 14.1 Public API

```js
export function render(canvas, constants, snapshot, pieceColor = {}, banners = null) { … }
```
Same signature as T4's — `gy` arrives through `snapshot` (§6.11), with two additive
properties, neither breaking any existing caller:
- `render` **returns `cellSize`** — no caller before `T7` reads this return value.
- `cellSize` is computed from `constants.gridAreaWidth ?? canvas.width` rather than a
  bare `canvas.width` — this supports `T7`'s mini-grid strip, which needs the main
  board drawn narrower than the full canvas to leave room on the side; no caller
  before `T7` sets `constants.gridAreaWidth`, so this is `canvas.width` for every
  other layer.

### 14.2 Ghost transparency

```js
const GHOST_ALPHA = 0.25;
```
A starting value, not a measured-optimal one — same caveat T4's own font-fraction
picks carry (`t3/implementation.md` §14.3's precedent).

### 14.3 `drawGhost`

```js
function drawGhost(ctx, constants, snapshot, cellSize, pieceColor) {
  const { HM, WM, PW, PANEL_PX } = constants;
  const rg = constants.rotGrid(snapshot.p, snapshot.pr);
  const color = pieceColor[snapshot.p] ?? '#FFFFFF';
  ctx.globalAlpha = GHOST_ALPHA;
  for (let y = 0; y < PW; y++) {
    for (let x = 0; x < PW; x++) {
      if (rg[y][x] === false) continue;   // exact-sentinel test (t1/implementation.md D1), not truthiness
      const gridY = snapshot.gy + y;
      const gridX = snapshot.px + x;
      if (gridY < 0 || gridY >= HM || gridX < 0 || gridX >= WM) continue;
      const { cx, cy } = cellOrigin(gridY, gridX, cellSize, HM, PANEL_PX);
      drawBlock(ctx, cx, cy, cellSize, color);
    }
  }
  ctx.globalAlpha = 1;
}
```
Same piece colour as the active piece — only the alpha differs. No special-case
for `gy === py` (piece already resting on its shadow): the opaque active piece,
drawn afterward, fully covers the ghost in that case; branching to skip the ghost
draw would save one loop's worth of (invisible) fills at the cost of an extra
condition on every frame, not worth it.

### 14.4 Call order inside `render`

```
1. drawBackground
2. drawHoldBox
3. drawPanel
4. drawBanners
5. drawPreview
6. drawGrid               (locked blocks — colored per-cell, t1/implementation.md D1)
7. drawGridLines
8. drawGhost              (new — between grid and active piece)
9. drawPiece              (active piece, opaque, clipped)
10. if snapshot.gameover: drawGameOver
```
`drawGhost` reads `constants`/`cellSize`/`pieceColor` exactly as `drawPiece` does,
differing only in which `py`-like field it uses (`gy` vs `py`) and the alpha —
kept as a separate function rather than parameterizing `drawPiece` with an alpha
argument, since the two have different bounds-source fields and merging them would
make `drawPiece`'s signature carry a ghost-only concept.

## 15. `controller.js` — controller / entry point

Extends T4's `controller.js`. Same input model (keyboard + gamepad, shared DAS
engine, single rAF loop) reused verbatim except where noted.

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
  rotGrid: eng.T4Eng.T3Eng.T2Eng.T1Eng.rotGrid, // one level deeper than T4's controller
  PANEL_PX: 0,
};
```
Not the flattened `eng.T1Eng.rotGrid` the §0.3 retrofit makes available at the
top level of `eng` — `controller.js` reaches `rotGrid` through the same deep
chain every controller from `t3/controller.js` on already used, one hop
deeper each time a new model is stacked (`t4/controller.js`'s own line is
`eng.T3Eng.T2Eng.T1Eng.rotGrid`, itself one hop deeper than `t3/controller.js`'s).
The retrofit's flattened accessor is used inside `model.js` itself (§4-T5a,
§4-T5d, §6.9) — no controller in the tower adopts it for this particular
access until `t6/controller.js` does.

### 15.2 `ACTIONS` — `DROP` added, no repeat

```js
const ACTIONS = {
  LEFT:  { repeat: true,  effect: () => { machine.movePiece(0, -1); afterAction(); } },
  RIGHT: { repeat: true,  effect: () => { machine.movePiece(0, 1); afterAction(); } },
  DOWN:  { repeat: true,  effect: () => { machine.fallStep(shuffleBag()); afterAction(); } },
  CCW:   { repeat: false, effect: () => { machine.rotatePiece(false); afterAction(); } },
  CW:    { repeat: false, effect: () => { machine.rotatePiece(true); afterAction(); } },
  HOLD:  { repeat: false, effect: () => { machine.holdPiece(shuffleBag()); afterAction(); } },
  DROP:  { repeat: false, effect: () => { machine.dropPiece(shuffleBag()); afterAction(); } },
};
```
`repeat: false` — a hard drop is a single decisive action, same class as `HOLD`/
`CCW`/`CW`, not a held/repeated one.

### 15.3 Keyboard and gamepad bindings

```js
const KEYMAP = new Map([
  ['ArrowLeft', 'LEFT'], ['ArrowRight', 'RIGHT'], ['ArrowDown', 'DOWN'], ['ArrowUp', 'DROP'],
  ['z', 'CCW'], ['x', 'CW'], [' ', 'HOLD'],
]);

const GAMEPAD_MAP = new Map([
  [14, 'LEFT'], [15, 'RIGHT'], [13, 'DOWN'], [12, 'DROP'],
  [0, 'CCW'], [1, 'CW'], [3, 'HOLD'],
]);
```
`Map`, not a plain object — the same choice every controller in the tower
makes (`t3/controller.js`, `t4/controller.js`, `t6/controller.js`), consumed
via `KEYMAP.get(e.key)` and `for (const [idx, name] of GAMEPAD_MAP)`.
Button `12` is D-pad up in the W3C Standard Gamepad mapping — the existing entries
(`13`/`14`/`15` for down/left/right) already follow that mapping, so `12` is the
consistent choice for up, not a new convention. No conflict with the face buttons
already bound (`0`/`1`/`3`).

### 15.4 Everything else

Unchanged from T4 (§15 there) — `afterAction`, `onTick`, `startGame`,
`handleGameover`, `computeHeld`, `processInput`, `frame`, `sizeCanvas`, the
keyboard/gamepad event wiring, `shuffleBag`/`makeBagsFn`. `DROP`'s entry in
`ACTIONS` is picked up by the existing tap-edge branch in `processInput` with no
further change there.

### 15.5 `index.html`

Unchanged in structure from T4's — the ghost is a canvas-drawing concern (§14),
not an HTML-structure one.
