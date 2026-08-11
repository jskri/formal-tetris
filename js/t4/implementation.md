# implementation.md — ImplementationInstructions for T4

Per-model instructions for the transformation

```
FormalModel (T4.v)  ×  ImplementationInstructions (this file)
      ── rocq-to-js skill ──▶  Code (model.js, view.js, controller.js, instance.js, index.html)
                             ×  Proofs (proofs.md)  ×  Tests (tests/)
```

`rocq-to-js.md` is the **generic process**; this file is the **T4-specific source of
truth**. T4 refines T3 for every event (§1); `t3/implementation.md` fixes rules that
apply here too and this file states only what is specific to T4. Generated
artifacts are never hand-edited: to change one, change this file or `T4.v` and
regenerate. All references to `T4.v` are **by definition name**.

## 0. Inputs, outputs, and what is frozen

Codegen-time inputs:
- `T4.v` — the abstract model (refines `T3.v` for every event — see §1).
- `T3.v`/`t3/implementation.md` (and transitively `T2.v`/`T1.v`) — reused.
- this file.
- `rocq-to-js.md` — generic rules (cited as "skill §x").

Runtime input (NOT codegen-time): `instance.js` — extends T3's with `NextLen`
(§11, §13).

Outputs: `model.js`, `view.js`, `controller.js`, `instance.js`, `index.html`,
`proofs.md`, `tests/` (§9).

### 0.1 Files reused from T1/T2/T3 unchanged

| file | role in T4 |
|------|-----------|
| `lib/utils.js` | shared primitives — imported transitively |
| `t1/model.js` | the T1 engine — reached as `T3Eng.T2Eng.T1Eng` |
| `t2/model.js` | the T2 engine — reached as `T3Eng.T2Eng` |
| `t3/model.js` | the T3 engine — imported as `T3` (alias for `T`); called as `T3(...)` |
| `t3/instance.js` | re-exported, with one addition — `NextLen` (§11) |

### 0.2 No prerequisite patch to `t3/model.js`

T4 requires no patch to `t3/model.js`. `T3.FixPiece`/`T3.FallStep` already take an
explicit `pNew : Piece` argument, and `T3.HoldPiece` already takes an explicit
`p2 : Piece` argument (`t3/model.js` §6.4/§6.6) — exactly the shape T4 needs to
supply `next s 0` into. Confirm this against the actual `t3/model.js` signatures
before codegen.

## 1. The refinement, and what it buys — and what it doesn't

`T4.State` embeds `T3.State` as `s3` and adds a `Draw` (`bag_`, `next_` — no
`bagLen_`, see §3) (T4.v's `State` record).

Refinement mapping (T4.v's `Refinement` section): `fₛ = s3 : T4.State → T3.State`.
`fₑ` maps every one of T4's five events into a T3 event (T4.v's `fₑ` definition):
```
Move dy dx    ↦ T3.Event2 (T2.Move dy dx)
Rotate cw     ↦ T3.Event2 (T2.Rotate cw)
Fix bagNew _  ↦ T3.Event2 (T2.Fix (next s 0))
Fall bagNew _ ↦ T3.Event2 (T2.Fall (next s 0))
Hold bagNew _ ↦ T3.Hold (next s 0)
```
`fₑ` is **state-dependent** (`s` appears free in the `Fix`/`Fall`/`Hold` cases) —
the piece T3 needs is not present in the T4 event, it's `next s 0`, read off the
pre-transition state. This is the crux of what T4 *is*: T3's externally-supplied
`p_new` is resolved into an internal mechanism (bag + preview), and `bagNew` is the
only genuinely new external input (the bag's refill, i.e., "randomisation" per
req-preview-init).

Per skill §7.1's three cases, this is a uniform "full use, with a precomputed
argument":

- **`movePiece`/`rotatePiece` — full uses**, `option_map (UnchangedT4Part s)` over
  the corresponding `T3` call (T4.v's `MovePiece`/`RotatePiece` definitions), `d`
  untouched.
- **`fixPiece` — full use, with the piece supplied by T4**: delegates to
  `T3.FixPiece (next s 0)` after popping/refilling `d` via `DrawNextPiece` (T4.v's
  `FixPiece` definition). `t3/proofs.md`'s `fixPiece` argument transfers once the
  supplied piece is shown equal to `next s 0` — the new obligation is entirely
  about *which* piece is supplied, not about T3's own logic.
- **`holdPiece` — same shape, plus one invariant-dependent hazard (§8.5)**: the
  `DrawNextPiece` call happens even when `hold s = Some _` (its result discarded,
  T4.v's `HoldPiece` definition) — in JS this is realized as *not calling it at
  all* in that branch (§4-T4h), which is safe only because `SwappedImplyHoldSome`
  (`t3/proofs.md`) guarantees `hold = None ⟹ ¬swapped`, so T3's own `swapped`
  guard can never reject a hold that reached the point of actually drawing.

## 2. File layout

```
instance.js            # extends t3/instance.js: adds NextLen (§11)
model.js               # T4 engine: wraps T3, adds bag_/next_ (§5–§7)
view.js                # renderer: hold box (Hold label) + preview column (Next label,
                        #   right panel) + T3's grid/panel/banners (§14)
controller.js           # controller / entry point; bag shuffle, H checks (§15)
index.html              # canvas + script mount (§15.10)
proofs.md               # refinement proof, delta over t3/proofs.md (§8)
tests/
  testInstance.js       # extends t3/tests/testInstance.js with NextLen fixture value
  model.unit.test.js
  model.properties.test.js
  model.fuzz.test.js
  oracle.js              # executable T4.v reference (reuses T3's oracle for s3)
```

## 3. Naming map (T4.v → JS)

Only T4-introduced names; T1/T2/T3 names keep their own maps, reached through nested
inner engines.

| T4.v | JS |
|------|----|
| `State` (record) | the `T4.Machine` instance; fields below |
| `s3` | `this.s3` (a `T3.Machine`) |
| `Draw` (record) | flattened onto `Machine` — no nested object (§3 note below) |
| `bag_` | `this.bag_` — fixed-capacity array, treated as a **stack** (`pop()`); no separate bound field |
| `bagLen_` | **not implemented** — `this.bag_.length` *is* `bagLen_`; keeping both would be redundant state that could desync |
| `next_` | `this.next_` — fixed-length array, length `NextLen`; `next_ 0` is `this.next_[0]` |
| `MaxBagLen` | **not implemented as a separate constant** — `NUM_PIECES = Piece.length`, the single source of truth also used for `bag_`'s capacity. This isn't a style choice: `PieceSet bag := Bijective bag MaxBagLen`'s surjectivity clause requires `bag`'s image on `[0, MaxBagLen)` to cover all of `Piece`; for any `Piece` with a fixed finite cardinality, this is only satisfiable when `MaxBagLen` equals that cardinality exactly. A separate hand-kept constant would be redundant state that could desync from `Piece.length`. |
| `NextLen` | instance parameter, value `6` (`t4/instance.js`) |
| `Bijective`, `PieceSet` | `isPieceSet(arr)` — pure predicate: `arr.length === NUM_PIECES && new Set(arr).size === NUM_PIECES` (dedupe + length suffices by pigeonhole: `arr` has exactly `NUM_PIECES` pairwise-distinct elements of `Piece`, a set of the same cardinality — a length-`NUM_PIECES` injection into an `NUM_PIECES`-element set is automatically a bijection, so no separate "all types present" check is needed) |
| `H : PieceSet bagNew` (event-level precondition) | `assertPieceSet(arr)` — throws (uncaught) if `!isPieceSet(arr)`; called unconditionally at the top of every `fixPiece`/`fallStep`/`holdPiece`/`Init` call |
| `TypeOK` | `PieceSet (bag s)`, a claim about the *unbounded* Rocq bag function on `[0, MaxBagLen)`. Not realized as a single predicate call in `checkInvariants` (§6.9): the finite-array `bag_` shrinks below `NUM_PIECES` mid-cycle, so `isPieceSet(bag_)` would misfire whenever `bag_.length < NUM_PIECES`, which is the common case. `checkInvariants` instead asserts the representable analogue directly — `bag_` non-empty, no longer than `NUM_PIECES`, pairwise distinct, drawn from `Piece` — the invariant a finite prefix of a valid piece set actually satisfies. |
| `ShiftNext` | not emitted as a named function — realized inline as `next_.shift(); next_.push(pNew)` (§4-T4a) |
| `DrawNextPiece` | `drawOnce(bag_, next_, bagNew)` (free helper) / `Machine#drawNextPiece(bagNew)` (method wrapping it) — §4-T4a |
| `BuildInitNext` | `initPieceAndDraw`'s internal loop (§4-T4b) — not a separate emitted function, folded in (Rocq's `Fixpoint`→JS `for`, standard pattern) |
| `InitPieceAndDraw`, `InitPiece` | `initPieceAndDraw(bagsFn)` (free helper), called once from the constructor | 
| `Init` | `new eng.Machine(bagsFn)` |
| `Event` | implicit (controller dispatch + method args, as T1–T3) |
| `UnchangedT4Part` | not emitted — realized by delegating then leaving `bag_`/`next_` untouched |
| `MovePiece`/`RotatePiece` | `Machine.movePiece(dy, dx)` / `Machine.rotatePiece(cw)` |
| `FixPiece` | `Machine.fixPiece(bagNew)` |
| `FallStep` | `Machine.fallStep(bagNew)` |
| `HoldPiece` | `Machine.holdPiece(bagNew)` |
| `Next` | not emitted — JS dispatch already maps controller event → method |
| `BagNonEmpty` | not implemented as a runtime check — `bag_.length > 0` is a structural invariant of the stack representation (a `pop()` on empty is never reachable if `TypeOK`/`H` hold; `checkInvariants` still asserts it as a cheap sanity check, §6.9) |
| `BagNextConsistent`, `Correct` | proofs.md only; not emitted |
| `fₑ`, `fₛ`, `InitRefineT3`, `NextRefineT3`, `RefineT3` | proofs.md only; not emitted |

**Note on `Draw` flattening:** `bag_`/`next_` (T4's own new state) sit directly on
`Machine`, not inside a `this.d = {...}` wrapper — there is no JS counterpart to
the `Draw` record as a distinct object, only as a pair of sibling fields. `s3`
stays nested (it's the embedded sub-model).

## 4. Per-definition translation rules (T4-specific)

Carry over every T1/T2/T3 rule. T4 points:

- **§4-T4a. `bag_`/`next_` as array + stack, not function + bound.** `DrawNextPiece`
  (T4.v's `DrawNextPiece` definition) becomes:
  ```js
  // spec: DrawNextPiece d bagNew — mutates bag_/next_ in place, returns { p, resetting }
  function drawOnce(bag_, next_, bagNew) {
    const resetting = bag_.length === 1;   // bagLen_ d <=? 1; BagNonEmpty ⟹ ≤1 ⟺ ===1
    const p = next_.shift();               // next_ 0, consumed
    next_.push(bag_.pop());                // ShiftNext ... (bag_ (bagLen_ - 1))
    if (resetting) bag_.push(...bagNew);   // bagSingle branch: bag_ is now empty; refill := bagNew
    return { p, resetting };
  }
  ```
  The two Rocq operations —
  popping the bag "backwards" (`bag_ (bagLen_-1)`, decrementing) and shifting `next_`
  left with an appended tail — collapse to `Array.prototype.pop()` and
  `shift()`/`push()` exactly, with no index arithmetic needed. `Machine#drawNextPiece`
  wraps this against `this.bag_`/`this.next_`, discarding `resetting` (only
  `initPieceAndDraw`'s bookkeeping needs it, §4-T4b).

- **§4-T4b. `BuildInitNext`/`InitPieceAndDraw`.** Literal loop translation of T4.v's
  `BuildInitNext` `Fixpoint`, kept generic in `bagsFn : ℕ → array` rather than
  hardcoded to the two bag-indices this concrete instantiation happens to need
  (`NextLen = 6`, `MaxBagLen = 7`: exactly one bag boundary is ever crossed, at the
  7th draw — worth knowing when reading a trace, not worth special-casing in code,
  since a generic loop is no more complex and stays traceable against `T4.v`):
  ```js
  function initPieceAndDraw(bagsFn) {
    let bag_  = bagsFn(0).slice();                    // length MaxBagLen (= NUM_PIECES)
    let next_ = Array(NEXT_LEN).fill(bagsFn(0)[0]);    // length NextLen — NOT bagsFn(0).slice():
                                                         // that would give length NUM_PIECES,
                                                         // wrong whenever NextLen ≠ NUM_PIECES
                                                         // (true for the real instance: 6 ≠ 7).
                                                         // Values are arbitrary — every entry is
                                                         // overwritten within NextLen draws below
                                                         // (T4.v's `BuildInitNext` comment) — only
                                                         // the *length* has to be right up front,
                                                         // since drawOnce's shift+push is
                                                         // length-neutral.
    let bagIdx = 1;
    for (let k = 0; k < NEXT_LEN; k++) {
      const { resetting } = drawOnce(bag_, next_, bagsFn(bagIdx));
      if (resetting) bagIdx++;
    }
    const { p } = drawOnce(bag_, next_, bagsFn(bagIdx));
    return { p, bag_, next_ };
  }
  ```
  `bagsFn` must be referentially consistent (`bagsFn(i)` called more than once for the
  same `i` — which happens whenever several loop iterations share a `bagIdx` before it
  advances — must return the *same* array each time), matching `bags : ℕ → ℕ → Piece`
  being a pure function in Rocq. The controller supplies a memoizing closure for this
  (§15.2).

- **§4-T4c. `H` — checked unconditionally, at every event boundary, before anything
  else.** `assertPieceSet` is called first in `fixPiece`, `fallStep`, `holdPiece`, and
  (via the `bagsFn` wrapper) `Init` — regardless of whether the bag actually resets
  this call. `fallStep`'s delegation to `fixPiece` re-checks the same `bagNew` a
  second time; harmless (`isPieceSet` is O(`NUM_PIECES`) = O(7)) and follows from
  checking independently at each event's own boundary rather than threading an
  "already checked" flag through — the latter would be an optimization not present in
  the spec (each `Event` constructor carries its own `H`, T4.v's `H : PieceSet bagNew`
  precondition).

- **§4-T4d. `fixPiece(bagNew)` — peek before the guard, commit only on success.**
  ```js
  fixPiece(bagNew) {
    assertPieceSet(bagNew);
    const p = this.next_[0];        // pure read of next_ 0 — no mutation yet
    const fired = this.s3.fixPiece(p);
    if (!fired) return false;        // zero mutation: matches every other guarded action
    this.drawNextPiece(bagNew);       // commit now that T3.FixPiece is confirmed to fire
    if (CHECK_INVARIANTS) checkInvariants(this, 'fixPiece');
    return true;
  }
  ```
  T4.v's `FixPiece` definition computes `d'` unconditionally via a `let` before the
  `option_map`, but that's a Rocq value binding, not an observable side effect: if
  `T3.FixPiece` returns `None`, `option_map` discards `d'` entirely and the whole
  function returns `None` — nothing about `d'` is ever read again, so Rocq's
  semantics impose no requirement that a *stateful* translation must "commit" it.
  Every guarded action (`movePiece`, `rotatePiece`, `fixPiece`, `holdPiece`) must
  satisfy "guard fails ⟹ zero mutation," which is what the stuttering-step
  arguments in `t1/proofs.md`–`t3/proofs.md` rely on. A version that calls
  `this.drawNextPiece(bagNew)` (which mutates `this.bag_`/`this.next_` in place)
  *before* knowing whether `this.s3.fixPiece(p)` succeeds would break that pattern
  here specifically: `T3.FixPiece`'s guard (`¬gameover ∧ ¬Valid(mg,p,py-1,px,pr)`) is
  **not** guaranteed to hold just because `T4.fixPiece` was called — nothing in
  `T4.v` gives `fixPiece` its own independent guard (contrast `holdPiece`,
  §4-T4g/h below) — so a caller invoking `fallStep` (hence `fixPiece`) when
  `gameover` is already `true` would hit exactly this case: `movePiece(-1,0)` fails
  (gameover is one of its guard conjuncts), `fixPiece` is attempted and *also* fails
  (same conjunct), yet a mutate-before-check version would have already advanced
  `bag_`/`next_` — a state with no corresponding `T4.v`-reachable state. The version
  above avoids this: `p` is read without mutating, and the draw is only committed
  once `fired` is confirmed `true`, giving identical `p` and identical post-success
  `bag_`/`next_` to a mutate-first version, while additionally satisfying "guard
  fails ⟹ zero mutation" on the failure path.

- **§4-T4e. `fallStep(bagNew)`.** Disjoint-guard sequencing (T4.v's `FallStep`
  definition):
  ```js
  fallStep(bagNew) {
    if (this.movePiece(-1, 0)) return true;
    return this.fixPiece(bagNew);   // re-checks bagNew (§4-T4c) — accepted redundancy
  }
  ```

- **§4-T4f. `movePiece`/`rotatePiece`.** One-line delegation to `this.s3`; `bag_`/
  `next_` untouched (full use, §1).

- **§4-T4g. `holdPiece(bagNew)`.**
  ```js
  holdPiece(bagNew) {
    assertPieceSet(bagNew);
    if (this.gameover) return false;
    // spec draws unconditionally and discards the result when hold !== null
    // (T4.v's HoldPiece definition); skipping the draw here instead is
    // behaviorally identical (d'' := d s in that branch means bag_/next_ are
    // provably unchanged either way) — see §4-T4h for why this needs no
    // §4-T4d-style peek-then-commit restructuring.
    const p2 = (this.s3.hold !== null) ? this.s3.hold : this.drawNextPiece(bagNew);
    const fired = this.s3.holdPiece(p2);
    if (!fired) return false;
    if (CHECK_INVARIANTS) checkInvariants(this, 'holdPiece');
    return true;
  }
  ```
  `this.s3.hold`/`this.s3.swapped` are read/written entirely inside `this.s3.holdPiece`
  (T3's own logic) — T4 does not duplicate T3's guard or field writes, and does not
  add its own `hold` getter: `hold` has exactly one read site (here), so it's
  inlined as `this.s3.hold` rather than wrapped in a T4-level accessor.

- **§4-T4h. Why `holdPiece` needs no peek-then-commit fix, unlike `fixPiece`.** Two
  separate claims, not one:
  - **The `hold !== null` (skip) branch matches the spec exactly, independent of any
    invariant.** T4.v's `hold` is a direct passthrough of T3's own field
    (`hold s := T3.hold (s3 s)`), so `T3.HoldPiece`'s internal
    `match hold s with Some p => p | None => p_new end` reads the *same* value T4's
    branch just tested (`this.s3.hold`, literally T3's own field) — whichever branch
    T4 takes, T3 necessarily takes the corresponding one. Skipping the draw here
    changes nothing T3 observes.
  - **The `hold === null` (commit) branch cannot subsequently fail — this is where an
    invariant is actually needed.** `T3.HoldPiece`'s guard is `¬gameover ∧ ¬swapped`.
    `¬gameover` is already established by `T4.holdPiece`'s own check three lines
    above. `¬swapped` is *not* locally checked — it's supplied by
    `t3/proofs.md`'s `SwappedImplyHoldSome` (`swapped ⟹ hold ≠ None`), whose
    contrapositive gives `hold = None ⟹ ¬swapped`. Since we're in the branch where
    `this.s3.hold === null`, `¬swapped` is guaranteed, so `this.s3.holdPiece(p2)` is
    guaranteed to fire whenever the mutating branch is taken — there is no reachable
    "mutate then reject" state here, unlike `fixPiece`, where no invariant makes that
    same guarantee. `t4/proofs.md` must cite `SwappedImplyHoldSome` explicitly at this
    point as an imported dependency, not re-derive it.

## 5. Free functions emitted by `model.js` (T4.v source order)

- `isPieceSet(arr)` — realizes `Bijective`/`PieceSet` (§3).
- `assertPieceSet(arr)` — the runtime realization of `H`; throws, uncaught by design:
  no intermediate `catch` may swallow this and resume play; only a top-level handler
  may log and end the session (§15.4).
- `drawOnce(bag_, next_, bagNew)` — realizes `DrawNextPiece`, shared between
  `Machine#drawNextPiece` and `initPieceAndDraw`'s loop (§4-T4a/b).
- `initPieceAndDraw(bagsFn)` — realizes `BuildInitNext` + `InitPieceAndDraw` (§4-T4b).

## 6. `T4.Machine`

Constructed by `T(...)` (§7). Wraps a `T3.Machine`. Fields mirror `T4.State`.

### 6.1 Constructor — `Init bags H` (T4.v)

```js
constructor(bagsFn) {
  const checkedBagsFn = (i) => { const b = bagsFn(i); assertPieceSet(b); return b; };
  const { p, bag_, next_ } = initPieceAndDraw(checkedBagsFn);
  this.s3 = new T3Eng.Machine(p);   // spec: T3.Init p
  this.bag_ = bag_;
  this.next_ = next_;
  if (CHECK_INVARIANTS) checkInvariants(this, 'Init');
}
```
`assertPieceSet` fires exactly once per index `bagsFn` is actually asked for — the
runtime realization of `H`'s per-`i` obligation; a literal "check for all `i`" has no
meaning outside Rocq (§4-T4c note carries over).

### 6.2–6.3 `movePiece`/`rotatePiece` — §4-T4f, one line each, delegate to `this.s3`.

Each also runs `checkInvariants` when `CHECK_INVARIANTS` is set, matching every
other public method (§6.9).

### 6.4 `fixPiece(bagNew)` — §4-T4d.

### 6.5 `fallStep(bagNew)` — §4-T4e.

### 6.6 `holdPiece(bagNew)` — §4-T4g, hazard note §4-T4h.

### 6.7 Read-through getters

Scoped to exactly what `controller.js` and `view.js` read directly:
```js
get gameover()          { return this.s3.gameover; }
get level()              { return this.s3.level; }
get totalClearedLines()  { return this.s3.totalClearedLines; }
get combo()               { return this.s3.combo; }
get perfectClear()        { return this.s3.perfectClear; }
get score()                { return this.s3.score; }
get s1()                  { return this.s3.s1; }   // flattened access, §6.10
```

### 6.8 `snapshot(machine)` — extends T3's inline

```js
function snapshot(machine) {
  return {
    ...T3Eng.snapshot(machine.s3),
    next: machine.next_.slice(),   // defensive copy — view.js must never mutate
  };
}
```
`hold`/`swapped` already arrive via `T3Eng.snapshot` (embedded). `bag_` itself has no
view-facing use (it's never rendered) and is intentionally not included.

### 6.9 `checkInvariants` (D7, default off)

```js
const CHECK_INVARIANTS = false;   // module-level, as in t1/model.js, t2/model.js, t3/model.js

function checkInvariants(s, message, isOccupied = (c => Piece.includes(c))) {
  T3Eng.checkInvariants(s.s3, message, isOccupied);
  console.assert(s.bag_.length > 0, `BagNonEmpty failed @ ${message}`);
  // TypeOK is a claim about the unbounded Rocq bag function, bijective on
  // [0, MaxBagLen) regardless of bagLen_'s current value. bag_ shrinks below
  // NUM_PIECES mid-cycle (the common case), so isPieceSet(bag_) is the wrong
  // check here; the checks below assert the invariant the finite array
  // actually maintains: bag_ is always a prefix of some valid piece set —
  // non-empty, no longer than NUM_PIECES, pairwise distinct, and drawn from
  // Piece.
  console.assert(s.bag_.length <= NUM_PIECES, `bag_ length bound failed @ ${message}`);
  console.assert(new Set(s.bag_).size === s.bag_.length,
    `bag_ elements not pairwise distinct @ ${message}`);
  console.assert(s.bag_.every(p => Piece.includes(p)), `bag_ ⊆ Piece failed @ ${message}`);
  console.assert(s.next_.length === NEXT_LEN, `next_ length failed @ ${message}`);
  console.assert(s.next_.every(p => Piece.includes(p)), `next_ ⊆ Piece failed @ ${message}`);
}
```
`isOccupied` exists purely to be forwarded to `T3Eng.checkInvariants` — T4 itself
never needs a non-default value (only `T7` ever overrides it, to admit its
`'garbage'` cell sentinel) — passing it through untouched here is what lets a
descendant's override actually reach `T1Eng.typeOK`, where it's checked. Delegates
to `T3Eng.checkInvariants` rather than reimplementing it. Called wherever
`CHECK_INVARIANTS` gates it — `Init` (§6.1), `movePiece`/`rotatePiece` (§6.2–6.3),
`fixPiece` (§4-T4d), `holdPiece` (§4-T4g) — every public method, never
unconditionally.

### 6.10 Flattened access: `get s1()` and `T1Eng`

`get s1()` above and `T1Eng: T3Eng.T1Eng` (§7) keep the depth to the innermost
`T1.Machine`/`T1Eng` at one hop regardless of how many models are stacked.

## 7. `model.js` exported function

```js
export function T(
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX,
  NextLen,
  MAX_SAFE_INTEGER = Number.MAX_SAFE_INTEGER,
) {
  const T3Eng = T3(Piece, InitialMainGrid, ForbiddenGrid, RotGrid, InitialY, InitialX,
                    PW, FY, FX, MAX_SAFE_INTEGER);
  const T1Eng = T3Eng.T1Eng; // flattened, §6.10
  const NEXT_LEN = NextLen;
  const NUM_PIECES = Piece.length;   // MaxBagLen, derived — not a separate parameter
  …
}
```
`NextLen` is placed after the T1–T3 parameters, before the defaulted
`MAX_SAFE_INTEGER` — required parameters precede defaulted ones, standard JS
convention. `checkAxioms` is `T3Eng.checkAxioms` composed with one further check,
`NextLen > 0` (T4.v's `AxiomsNextLen` axiom).

## 8. `proofs.md` (scope)

Delta over `t3/proofs.md`.

1. **Scope.** Safety only. `RefineT3` (T4.v's `RefineT3` definition) has exactly two
   conjuncts — `InitRefineT3` and `NextRefineT3` — no `None`-preservation clause.
   State explicitly *why* it's absent, not just that it is: a candidate
   `NoneRefineT3` in the direction "T4 blocks ⟹ T3 blocks" was considered and dropped
   as unnecessary for a forward-simulation safety argument (Lynch & Vaandrager,
   *Information and Computation* 121(2):214–233, 1995, §3 requires only start/step
   conditions); the *converse* direction ("T3 permits ⟹ T4 permits", i.e. behavioral
   completeness) is actively **false** — `T3.Fix` accepts an arbitrary piece per call
   and so admits traces like "`Fix X` forever" for a fixed `X`, which no reachable T4
   state can produce once `bag_` is forced to biject with `Piece` (`PieceSet`,
   `MaxBagLen = |Piece| ≥ 2`). This is a property of the model, not something
   `proofs.md` needs to re-derive per implementation — reference it, don't restate the
   argument in full.
2. **α.** `α_T4(js) = { s3 := α_T3(js.s3); bag := js.bag_; next := js.next_ }` — apply
   `t3/proofs.md`'s `α_T3` to the embedded machine; `bag_`/`next_` map to the
   corresponding Rocq `ℕ → Piece` functions via `arr[i mod arr.length]`-style index
   correspondence restricted to `[0, arr.length)` (the "array = bounded total
   function" pattern already used for T1's grids).
3. **`movePiece`/`rotatePiece` — full-use transfer**, one line each (§1, §4-T4f).
4. **`fixPiece`/`fallStep` — full-use transfer with a supplied piece, plus a
   stuttering-step obligation.** Two things to show, beyond what transfers from
   `t3/proofs.md`: (a) the piece passed to `this.s3.fixPiece` equals `next s 0` at the
   pre-state — definitional (`const p = this.next_[0]` *is* the read of index 0,
   taken before any mutation), not an argument requiring induction; (b) guard failure
   implies zero mutation of `bag_`/`next_` — true by construction of §4-T4d's
   peek-then-commit ordering (`this.drawNextPiece(bagNew)` is only reached after
   `fired` is confirmed), needed so the stuttering-step argument `t1/proofs.md`–
   `t3/proofs.md` rely on (guard fails ⟹ `α` of the post-call state equals `α` of the
   pre-call state) extends to T4's own new fields.
5. **`holdPiece` — full-use transfer, plus two dependencies to state explicitly, not
   re-derive.** (a) The `hold !== null` (skip) branch matches `T3.HoldPiece`'s own
   branch on the same underlying field (T4.v's `hold` field definition), independent
   of any T3 invariant. (b) The `hold === null` (commit) branch's mutation can never
   precede a subsequent rejection: cite `t3/proofs.md`'s `SwappedImplyHoldSome`
   (`swapped ⟹ hold ≠ None`) — its contrapositive, `hold = None ⟹ ¬swapped`,
   combined with the local `¬gameover` check, guarantees `T3.HoldPiece`'s guard holds
   whenever the mutating branch is taken. Both points are argued in full in §4-T4h;
   state them here as imported facts, don't restate the argument.
6. **`TypeOK`/`BagNonEmpty`/`BagNextConsistent` preservation.** These have no T3
   analogue and need their own induction over `drawOnce`'s two branches (reset /
   no-reset), checked against `BagNextConsistent`'s `k = min(MaxBagLen - bagLen,
   NextLen)` formula in each case — this is not carried out in this file; it's
   `proofs.md`'s own obligation to discharge. `TypeOK` preservation across a reset
   additionally needs `H`'s `PieceSet bagNew` — this is where `assertPieceSet` (a
   runtime check) stands in for a Rocq proof term; state plainly that this obligation
   is *conditional on the check having passed*, i.e., `TypeOK` is only proved to be
   preserved given `assertPieceSet` didn't throw, not unconditionally.
7. **`Init`.** `InitRefineT3` (T4.v's `InitRefineT3` proof) needs `unfold Init,
   InitPiece, InitPieceAndDraw; destruct (BuildInitNext ...)` to force both call
   sites' pair destructuring to the same term before `reflexivity` applies — the
   JS-side analogue is that `initPieceAndDraw` is called exactly once in the
   constructor and its `p` is what seeds `T3Eng.Machine`, so there is no JS
   equivalent of the definitional-unfolding friction.
8. **Cap soundness — not applicable** (T4 introduces no new arithmetic on
   `score`/`combo`/`totalClearedLines`).

## 9. Tests (`tests/`)

Mirror T3's suite (`t3/implementation.md` §9) on the same small fixture, plus T4-
specific coverage.

- **`testInstance.js`** — extends `t3/tests/testInstance.js` with a fixture
  `NextLen = 6` (or a smaller value for faster/more exhaustive small-fixture tests,
  as T1–T3 already do for grid dimensions — confirm against whatever convention
  `t1/tests/testInstance.js` uses for shrinking fixture parameters).
- **`oracle.js`** — reuses T3's oracle for `s3`; independently hand-rolls
  `drawOnce`/`initPieceAndDraw`-equivalents (a shared bug between translation and
  helper should still surface as a mismatch, so the oracle avoids importing
  `model.js`'s own implementation).
- **`model.unit.test.js`** — golden vectors:
  - **Not** T4.v's own worked-trace comments — those use a 3-piece set (`{T,S,L}`,
    `MaxBagLen=3`), but the fixture chain (`t1/tests/testInstance.js` →
    `t3/tests/testInstance.js`, reused by `t4`'s own, §9 above) has exactly two
    pieces (`A`, `B`), and per §3's forced-equality argument its `MaxBagLen` is
    **2**, not 3 — copying `T4.v`'s traces verbatim would need a fixture this chain
    doesn't have. Adding a third piece to the shared fixture isn't done here
    either: `A`/`B`'s existing tests are built around occupancy/rotation edge cases
    specific to `A`'s full-block vs `B`'s single-cell asymmetry, and a third piece
    would need its own `RotGrid`/`InitialY`/`InitialX` values satisfying
    `AxiomsRotGrid`, at the risk of shifting behavior in tests already verified
    passing.
  - Instead, hand-verify new vectors directly on the existing `A`/`B` fixture, the
    same method `T4.v`'s own comments use (simulate `drawOnce`/`initPieceAndDraw`
    by hand or by a throwaway script, then assert the exact sequence) — for
    example, with `NextLen = 3` for this test file specifically (chosen for a
    short, hand-traceable sequence that still crosses a bag boundary at least
    once) and `bagsFn = i ↦ [['A','B'], ['B','A'], ['A','B'], ...][i]`:
    `initPieceAndDraw(bagsFn)` yields `p = 'B'`, `bag_ = ['A','B']`, `next_ =
    ['A','A','B']`; one further `drawOnce` (bag resets, since `bag_.length === 1`
    doesn't hold yet here — the *next* draw is the one that empties it) exercises
    the non-reset branch, and continuing for a couple more draws crosses into the
    reset branch once `bag_` empties. Assert the exact sequence produced, not just
    "it doesn't throw."
  - `isPieceSet`/`assertPieceSet`: a malformed `bagNew` (wrong length, a duplicate)
    throws; a valid one doesn't.
  - initial population: given two known bags, the resulting `bag_`/`next_`/current
    piece match hand-computed values (mirroring `BuildInitNext`'s own worked trace,
    on the fixture above, not on `T4.v`'s 3-piece example).
  - `holdPiece`'s skip-vs-discard: firing a hold when `hold !== null` leaves `bag_`/
    `next_` byte-identical to before the call.
  - `fixPiece`'s guard-fail case (§4-T4d): calling `fixPiece` when the underlying
    `T3.FixPiece` guard is not satisfied (e.g. piece can still fall) leaves `bag_`/
    `next_` byte-identical to before the call — the property the peek-then-commit
    ordering exists to guarantee.
  - `fixPiece`/`fallStep` consume exactly one piece from `next_` per *successful*
    call (narrow-blast-radius style check, as T3's §9).
- **`model.properties.test.js`** — fast-check: `TypeOK`, `BagNonEmpty`,
  `BagNextConsistent` hold after every step (including across bag resets);
  `T3.Correct`'s conjuncts (delegated) hold after every step; differential oracle
  over every snapshot field, including `next`.
- **`model.fuzz.test.js`** — same shape as T1–T3's: N seeds × M steps, using a real
  Fisher–Yates shuffle (not the controller's — a test-local one) to generate
  `bagNew`/`bagsFn` inputs, structural + the new invariants + oracle differential.

## 10. Acceptance oracle

A regeneration is correct iff:
1. Every `T4.v` definition with a §3 mapping is realised; every "not emitted" entry
   is absent.
2. `model.js` constructs the T3 engine via `T3(...)` and never reimplements a T1/T2/T3
   free function.
3. `tests/` passes on the small fixture: unit + fuzz fully; properties under
   `fast-check` when installed.
4. The differential oracle agrees with `model.js` on every snapshot field, including
   `next`, over every generated trace.
5. `assertPieceSet` is called, unconditionally, at the top of `fixPiece`, `fallStep`,
   `holdPiece`, and inside `Init`'s `bagsFn` wrapper — never only conditionally on
   whether a reset will actually occur (§4-T4c).
6. `holdPiece` never calls `drawNextPiece` when `hold !== null` (§4-T4g/h).
7. `fixPiece` reads `next_[0]` before calling `this.s3.fixPiece`, and calls
   `this.drawNextPiece` only after that call is confirmed to have fired — never
   before (§4-T4d). Equivalently: a guard-failing `fixPiece`/`fallStep` call leaves
   `bag_`/`next_` byte-identical to before the call.
8. `checkInvariants` asserts `TypeOK`'s representable analogue (bag_ non-empty, at
   most `NUM_PIECES` long, pairwise distinct, drawn from `Piece`) plus
   `BagNonEmpty`/`next_` well-formedness, delegating to `T3Eng.checkInvariants`
   rather than reimplementing it.
9. No thrown `assertPieceSet` error is caught anywhere except a single top-level
   handler that logs and ends the session — grep for any intermediate `try/catch`
   around a `fixPiece`/`fallStep`/`holdPiece`/`Init` call path.

## 11. Instantiation (`instance.js`)

```js
export * from '../t3/instance.js';
export const NextLen = 6;
```
`NextLen` is a genuine new abstract parameter (T4.v's `NextLen` parameter), not
derivable from `Piece` the way `MaxBagLen` is (§3), so it has no choice but to be
supplied here.

## 12. Generator determinism rules

Inherit `t1/implementation.md` §12 / `t2/implementation.md` §12 / `t3/implementation.md`
§12's "reuse over restatement" verbatim. No `t3/model.js` patch is a prerequisite
here (§0.2).

## 13. `instance.js` parameters

`NextLen` — value `6` (§11). Everything else inherited from T1's parameter set.

## 14. `view.js` — renderer (hold box + preview column + T3's grid/panel/banners)

T4's `view.js` does not redefine `cellOrigin`/`drawBackground`/`drawGridLines`/
`drawBlock`/`drawGrid`/`drawPiece`/`drawGameOver` (imported from `t1/view.js`, which
implements them generally enough to serve every layer) or `labelGeometry`/
`holdBoxGeometry`/`drawHoldBox`/`drawPanel`/`drawBanners` (imported from
`t3/view.js`). What's genuinely T4's own: `effectiveRowRange`, `drawPreview`
(§14.7), and `previewGeometry` (§14.7). `drawGameOver`'s two-panel-safe dimming
(§14.8, below) lives in `t1/view.js` as the one canonical version, general enough
to serve every layer with any number of side panels.

### 14.1 Public API

Same signature as T3's — `next` arrives through `snapshot()` (§6.8).

### 14.2 Two-panel geometry — halved budget, not retuned constants

`sizeCanvas` (`controller.js`) computes T3's *total* panel budget, then splits it
in two, guaranteeing byte-identical grid `cellSize` to T3 at every viewport size —
verifiable by direct substitution, not a new tuned constant:
```js
const PANEL_FRAC = 0.22, PANEL_MIN = 120, PANEL_MAX = 360;
const totalPanel = Math.min(PANEL_MAX, Math.max(PANEL_MIN, Math.round(PANEL_FRAC * vw)));
const panel = totalPanel / 2;                                 // per-side width
const gridMaxW = vw * 0.95 - 2 * panel;                        // == vw*0.95 - totalPanel
...
constants.PANEL_PX = panel;                                    // shared by both side panels
canvas.width = 2 * panel + constants.WM * cell;
```
`drawBackground`/`drawGrid`/`drawGridLines`/`drawPiece` all offset by `PANEL_PX` (the
*left* panel's width) — the grid's horizontal origin doesn't change, only what's
drawn to its right.

### 14.3 Font/margin fractions — halved for two panels

T3's single-panel fractions (`margin: 0.12`, `labelFont: 0.16`, `valueFont: 0.26`)
are tuned for a panel twice this width; T4 uses half of each (`0.08`/`0.11`/`0.17`)
to keep roughly the same absolute text size now that each panel is half as wide — a
starting point, not a proven-optimal one. `t3/implementation.md` §14.4 documents
these same fractions as T3's own, so T3 and T4 render this text identically and T4
imports rather than redefines. The `Math.max` floors protect legibility at the
narrow end independent of the fraction chosen.

### 14.4 Held-piece-never-shrinks trade-off

The hold box's clamp (`hbSize = Math.min(PW*cellSize, PANEL_PX - 2*margin)`) can still
bind at the narrowest viewports even after the fraction reduction — `PANEL_MIN/2 = 60`
puts a hard floor under `PANEL_PX` that `PW*cellSize` can exceed. Accepted trade-off:
the hold box clips/clamps at extreme narrow widths, rather than raising `PANEL_MIN`
(which would cost grid room instead).

### 14.5 Label geometry — shared helper, both panels

`labelGeometry` (defined in `t3/view.js`, imported here) is used by both "Hold"
and "Next" — same font/colour/advance convention as T3's `SCORE`/`LEVEL` text:
`#AAAAAA`, `textAlign='left'`, `textBaseline='top'`.

### 14.6 Hold-box geometry — extended with the label

`holdBoxGeometry`/`drawHoldBox` (defined in `t3/view.js`, imported here) draw the
"Hold" caption above the box, sharing `labelGeometry`'s fractions.

### 14.7 Preview-column geometry — right panel, borderless, one-cell gap, capped by effective height, aligned to the held piece

`constants` (built in `controller.js`, §15) must carry `NextLen` and `Piece`
alongside `PW`/`FY`/`FX`/etc. — only `view.js` needs them (`NextLen` for the cap,
`Piece` for the effective-height computation below).

Slot height is sized by pieces' actual occupied-row span, not by `PW`: every piece
type occupies the same row range at rotation 0, derived generically from
`Piece`/`rotGrid` rather than assumed:

```js
// Union of occupied rows across every piece type at rotation 0. AxiomsRotGrid
// (t1/model.js) guarantees every piece has >=1 occupied cell at every rotation,
// so minRow/maxRow are always well-defined here.
function effectiveRowRange(constants) {
  let minRow = constants.PW, maxRow = -1;
  for (const p of constants.Piece) {
    const rg = constants.rotGrid(p, 0);
    for (let y = 0; y < constants.PW; y++) {
      for (let x = 0; x < constants.PW; x++) {
        if (rg[y][x] !== false) {   // exact-sentinel test (t1/implementation.md D1)
          if (y < minRow) minRow = y;
          if (y > maxRow) maxRow = y;
        }
      }
    }
  }
  return { minRow, maxRow };
}
```

`previewGeometry` clamps its own `previewCellSize` the same way `holdBoxGeometry`
clamps `hbCellSize` — otherwise a piece up to `PW` cells wide can exceed `PANEL_PX`
and bleed past the panel's own right edge:
```js
function previewGeometry(constants, cellSize) {
  const { margin, labelFont, labelHeight } = labelGeometry(constants);
  const { minRow, maxRow } = effectiveRowRange(constants);
  const effectiveRows = maxRow - minRow + 1;
  const previewCellSize = Math.min(cellSize, (constants.PANEL_PX - 2 * margin) / constants.PW);
  const gap = previewCellSize;
  const boxSize = effectiveRows * previewCellSize;
  // The hold box draws within a full PW×PW box, so its piece's top edge sits
  // (PW-1-maxRow) cells below the box's own top — the same margin every piece
  // has above it there, since maxRow is the same for every piece type. topGap
  // reproduces that offset here, so the top preview piece's top edge lines up
  // with the held piece's top edge, not just with the "Next" label.
  const topGap = (constants.PW - 1 - maxRow) * previewCellSize;
  const boxTop = margin + labelHeight + topGap;
  const availableH = constants.HM * cellSize - margin - labelHeight - topGap - margin;
  const perSlot = boxSize + gap;
  const count = Math.max(0, Math.min(constants.NextLen, Math.floor((availableH + gap) / perSlot)));
  // silent truncation if count < constants.NextLen — see closing note below
  const rightOrigin = constants.PANEL_PX + constants.WM * cellSize; // left panel + grid width
  return { margin, labelFont, labelY: margin, boxTop, boxSize,
           cellSize: previewCellSize, gap, count, rightOrigin, minRow, maxRow };
}
```
A **uniform** slot height (the global max over all piece types), not a per-piece
variable one — deliberately: a per-piece height would make `count` depend on which
pieces are actually in the queue (jumpy, frame-to-frame varying layout), whereas
every other geometry quantity here is a pure function of `constants`/`cellSize`
alone. `I`'s slot (only 1 occupied row) has unused space above/below within its
2-row slot — the same "unused space within a fixed box" pattern the hold box and
in-grid piece rendering already exhibit (both draw within a `PW×PW` box using
`rg[y][x]` checks, filling only occupied cells).

`topGap`, `gap`, and `boxSize` are all computed from `previewCellSize`, not the main
grid's raw `cellSize` — so the preview column and the hold box scale consistently
with each other, clamp for clamp, not just when neither clamp binds.

Deliberately scoped to the preview column only — the hold box (§14.3–14.4) has no
analogous "how many fit" problem (it's a single fixed box, not a packed list), so
its `PW`-based sizing is untouched.

(`constants.PANEL_PX` for the right panel is the *same* value as the left, per "same
size" — no separate right-panel width constant.)

```js
function drawPreview(ctx, constants, snapshot, geom, pieceColor) {
  const { rightOrigin, cellSize, maxRow } = geom;
  ctx.fillStyle = '#AAAAAA';
  ctx.textAlign = 'left'; ctx.textBaseline = 'top';
  ctx.font = `${geom.labelFont}px sans-serif`;
  ctx.fillText('Next', rightOrigin + geom.margin, geom.labelY);

  for (let i = 0; i < geom.count; i++) {
    const p = snapshot.next[i];
    const rg = constants.rotGrid(p, 0);           // always rotation 0, as the hold box
    const color = pieceColor[p] ?? '#FFFFFF';
    const boxY = geom.boxTop + i * (geom.boxSize + geom.gap);
    for (let y = 0; y < constants.PW; y++) {
      for (let x = 0; x < constants.PW; x++) {
        if (rg[y][x] === false) continue;         // exact-sentinel test (D1), not truthiness
        const cx = rightOrigin + geom.margin + x * cellSize;
        // maxRow (not PW-1) is the top of the *effective* slot — every piece's
        // occupied rows fall within [minRow, maxRow] by construction of
        // effectiveRowRange, so this never goes negative.
        const cy = boxY + (maxRow - y) * cellSize;
        drawBlock(ctx, cx, cy, cellSize, color);
      }
    }
  }
}
```
No `strokeRect` call — unlike the hold box, preview boxes are borderless per
instruction; only the piece blocks themselves are drawn. `rightOrigin` is
`PANEL_PX + WM*cellSize` — left panel width plus grid width — computed once in
`previewGeometry` and threaded through `geom`, the same pattern `holdBoxGeometry`
already uses for its own shared quantities (§14.6); no separate `cellOrigin`-style
helper is needed since the right panel has no per-row/per-column grid to index into,
only a flat vertical stack of slots.

Truncation is silent — no indicator when `count < constants.NextLen`. This matches
the hold box's own established precedent (§14.4: clip/clamp rather than resize
anything else) rather than introducing a new failure-visibility convention for just
this one element.

### 14.8 `drawGameOver`

Lives in `t1/view.js`, not redefined here — one canonical version general enough to
dim exactly the grid's own width (`gridX = PANEL_PX ?? 0`, `gridW = WM*cellSize`)
regardless of how many side panels exist, rather than `canvas.width - PANEL_PX`
(which would also dim the right panel here).

### 14.9 Call order inside `render`

```
1. drawBackground
2. drawHoldBox          (left panel — Hold label + box)
3. drawPanel             (score / level, shifted down by geom.panelTopY)
4. drawBanners            (combo / perfect-clear, shifted down)
5. drawPreview            (right panel — Next label + capped column)
6. drawGrid               (locked blocks — colored per-cell, t1/implementation.md D1)
7. drawGridLines
8. drawPiece              (active piece, clipped)
9. if snapshot.gameover: drawGameOver (grid only, §14.8)
```
Neither `drawPanel` (step 3) nor `drawPreview` (step 5) may `fillRect` any
background — `drawBackground` (step 1) already covers the full canvas, including
both side panels, exactly once, and both steps 3 and 5 run after something else
(`drawHoldBox`) has already drawn into their respective region. A background clear
in either would silently erase that prior drawing.

## 15. `controller.js` — controller / entry point

Extends T3's `controller.js`. Same input model reused verbatim except where noted.

### 15.1 Bag shuffle — replaces `randomPiece()`

```js
function shuffleBag() {
  const a = Piece.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}
```
Fisher–Yates over the full `Piece` array (length `NUM_PIECES`) — produces a fresh
*permutation*, not a single piece. `randomPiece()` is removed entirely; nothing in
T4's controller needs a single uniformly-random piece (`Move`/`Rotate` need none,
`Fix`/`Fall`/`Hold` each need a fresh *bag*).

### 15.2 `startGame()` — `bagsFn` construction

```js
function makeBagsFn() {
  const bags = [];
  return (i) => { while (bags.length <= i) bags.push(shuffleBag()); return bags[i]; };
}

function startGame() {
  machine = new eng.Machine(makeBagsFn());
  ...
}
```
Memoizes each newly-requested index exactly once, satisfying `initPieceAndDraw`'s
referential-consistency requirement (§4-T4b) — a fresh `makeBagsFn()` per game, not a
module-level singleton (avoids leaking bags across restarts).

### 15.3 `ACTIONS` — `bagNew` replaces `pNew`

```js
const ACTIONS = {
  LEFT:  { repeat: true,  effect: (now) => { machine.movePiece(0, -1); afterAction(now); } },
  RIGHT: { repeat: true,  effect: (now) => { machine.movePiece(0, 1); afterAction(now); } },
  DOWN:  { repeat: true,  effect: (now) => { machine.fallStep(shuffleBag()); afterAction(now); } },
  CCW:   { repeat: false, effect: (now) => { machine.rotatePiece(false); afterAction(now); } },
  CW:    { repeat: false, effect: (now) => { machine.rotatePiece(true); afterAction(now); } },
  HOLD:  { repeat: false, effect: (now) => { machine.holdPiece(shuffleBag()); afterAction(now); } },
};
```
Each effect takes the current tick's `now` and forwards it to `afterAction`, which
uses it to retarget the gravity accumulator on a level change (§15.5). A fresh
`shuffleBag()` per call — most calls discard it (`bag_.length > 1`), which is the
accepted cost of D5's "non-determinism as explicit args" convention. `onTick`
likewise calls `machine.fallStep(shuffleBag())`.

### 15.4 Uncaught `assertPieceSet` — no controller-level catch

Nothing in `controller.js` wraps `movePiece`/`rotatePiece`/`fixPiece`/`fallStep`/
`holdPiece` calls in a `try/catch`. An `assertPieceSet` failure (which, given
`shuffleBag`'s correctness, should never actually fire) propagates uncaught to the
browser's default handler — full stack trace, no swallowed-and-continued session. If
a top-level crash reporter is added later, it must only log and end the session,
never resume `startGame()` silently from the same `bagsFn`.

### 15.5 Everything else

`sizeCanvas` (two-panel split, §14.2), `KEYMAP`/`GAMEPAD_MAP`, `processInput`/DAS
engine, `afterAction`, `handleGameover` — reused from T3 (`t3/implementation.md`
§15.3–§15.9; `HOLD` is `repeat: false`).

### 15.6 `index.html`

Structurally the same as T3's — the second panel is purely a canvas-drawing
concern (§14), not an HTML-structure one (`t3/implementation.md` §15.10).
