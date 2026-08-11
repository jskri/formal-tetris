# implementation.md — ImplementationInstructions for T2

Per-model instructions for the transformation

```
FormalModel (T2.v)  ×  ImplementationInstructions (this file)
      ── rocq-to-js skill ──▶  Code (model.js, view.js, controller.js, instance.js, index.html)
                             ×  Proofs (proofs.md)  ×  Tests (tests/)
```

`rocq-to-js.md` is the **generic process**; this file is the **T2-specific source of
truth**. T2 refines T1 (§1); `t1/implementation.md` fixes rules that apply here too
and this file states only what is specific to T2. Generated artifacts are never
hand-edited: to change one, change this file or `T2.v` and regenerate. All
references to `T2.v` are **by definition name**, so renaming/reordering in the
model is caught by the coverage check (§10), not silently mismatched line numbers.

## 0. Inputs, outputs, and what is frozen

Codegen-time inputs:
- `T2.v` — the abstract model (refines `T1.v` via the mapping `f = (fₑ, fₛ)`).
- `T1.v` and `t1/implementation.md` — the refined model and its frozen instructions (reused).
- this file.
- `rocq-to-js.md` — generic rules (cited as "skill §x").

Runtime input (NOT codegen-time):
- `instance.js` — the concrete instantiation of the abstract parameters (§11). For T2
  this re-exports `instance.js` unchanged (the abstract parameter set is identical to
  T1's; T2 adds no model parameters — see §13).

Outputs: `model.js`, `view.js`, `controller.js`, `instance.js`, `index.html`, `proofs.md`,
`tests/` (§9). The acceptance oracle is §10. **Byte-identity is not required**;
behavioural equivalence up to the fixed naming map is.

### 0.1 Files reused from T1 unchanged (NOT regenerated, imported as-is)

| file | role in T2 |
|------|-----------|
| `lib/utils.js` | shared primitives (`mod`, `copyGrid`, `emptyRow`, `emptyRows`, and the T2 helpers `natSub`, `natDiv`, `capAdd`) — imported by `model.js` |
| `t1/model.js` | the T1 engine — imported as `T1` (alias for `T`); called as `T1(...)` internally |
| `t1/instance.js` | the concrete T1 parameters — re-exported by T2's own `instance.js` (§11) |

`model.js` does **not** duplicate any T1 free function (grid ops, `rotGrid`, `isFullLineb`,
…); it reaches them through the object returned by `T1(...)` or recomputes only what T2
needs (the inner T1 state's `clearedLines`, §4-T2a). There is exactly one copy of the T1 engine.

---

## 1. The refinement, and what it buys

`T2.State` embeds `T1.State` as the field `s1` and adds five scalar/flag fields:
`score`, `level`, `combo`, `perfectClear`, `totalClearedLines` (`T2.v` `Record State`).

The refinement mapping (`T2.v` Refinement section):
- `fₑ : T2.Event → T1.Event` is the constructor-wise identity.
- `fₛ : T2.State → T1.State` is the projection `s1`.
- `RefineT1 : ∀ e2 s2 s2', T2.Next e2 s2 = Some s2' → T1.Next (fₑ e2) (fₛ s2) = Some (fₛ s2')`.

Consequence for codegen: the `s1` half of every T2 transition **is** a T1 transition.
So `model.js`'s machine holds a real `T1.Machine` and delegates the `s1` update to it; only
the five T2 fields need new JS logic, and only `FixPiece` changes them non-trivially.

Scope (`proofs.md`, full structure in §8 below): safety/refinement only. Fall-speed (§15) and on-screen
banners (§14) are controller concerns outside the refinement, exactly as fall timing was
outside T1.

---

## 2. File layout

```
instance.js            # re-exports t1/instance.js; adds nothing model-level (§13)
model.js               # T2 engine: wraps T1, adds score/level/combo/perfectClear (§5–§7)
view.js                # renderer: T1 grid + left info panel + transient banners (§14)
controller.js          # controller / entry point; level→fall-speed; banner timing (§15)
index.html             # shell: canvas + module bootstrap (§15.10)
proofs.md             # refinement proof, delta over t1/proofs.md (§8)
tests/
  testInstance.js     # re-exports T1's tests/testInstance.js (small fixture) + T2 scalars
  model.unit.test.js
  model.properties.test.js
  model.fuzz.test.js
  oracle.js           # executable T2.v reference (reuses T1 oracle for s1)
```

`lib/utils.js`, `t1/model.js`, `t1/instance.js` are imported from their T1 locations (§0.1), not copied.

---

## 3. Naming map (T2.v → JS)

Only T2-introduced names appear here; T1 names keep their `t1/implementation.md` §3 mapping
and are reached through the inner engine.

| T2.v | JS |
|------|----|
| `State` (record) | the `T2.Machine` instance; fields below |
| `s1` | `this.s1` (a `T1.Machine`); snapshot exposes the T1 fields inline (§7) |
| `score` | `this.score` |
| `level` | `this.level` |
| `combo` | `this.combo` (stored = visible combo + 1; see §6) |
| `perfectClear` | `this.perfectClear` |
| `totalClearedLines` | `this.totalClearedLines` |
| `gameover` (helper) | `get gameover()` → `this.s1.gameover` — controller convenience, not a stored field |
| `Init` | `new eng.Machine(p0)` (where `eng = T(...)`) |
| `Event` | implicit (controller dispatch + method args), as in T1 |
| `UpdateS1` | not emitted — realised by delegating to `this.s1` then copying scalars (§6) |
| `MovePiece` | `Machine.movePiece(dy, dx)` |
| `RotatePiece` | `Machine.rotatePiece(cw)` |
| `FixPiece` | `Machine.fixPiece(pNew)` |
| `FallStep` | `Machine.fallStep(pNew)` |
| `LineClearPoints` | `lineClearPoints(clearedLines, level)` |
| `ComboPoints` | `comboPoints(level, combo)` |
| `PerfectClearPoints` | `perfectClearPoints(perfectClear, clearedLines, level)` |
| `Points` | `points(clearedLines, level, combo, perfectClear)` |
| `clearedLines` (read of `s1'.(clearedLines)`) | `this.s1.clearedLines` (now a T1 field, set on the pre-clear grid) |
| `EmptyGridb` | `emptyGridb(g)` |
| `fₑ` | not emitted — JS dispatch already maps controller event → method |
| `fₛ` | not emitted — `this.s1` IS the projection |
| `Correct`, `LevelCorrect`, `NonDecreasing*`, `ScoreRisesOnClear`, `CorrectStep` | proofs.md only; not emitted |

---

## 4. Per-definition translation rules (T2-specific)

Carry over every T1 rule from `t1/implementation.md` §4 (guard-before-index, `negb`→`!`,
structural-equality, deep-copy, totality boundary, etc.). New T2 points:

- **§4-T2a — `clearedLines` comes from the inner T1 state.** `T1.v` records
  `clearedLines := FullLineCount u` on the **post-union, pre-clear** grid `u` inside
  `T1.FixPiece`, and carries it through `MovePiece`/`RotatePiece` unchanged. `T2.FixPiece`
  reads `s1'.(clearedLines)` directly. So `model.js`'s `fixPiece` calls `this.s1.fixPiece(pNew)`
  and then reads `const clearedLines = this.s1.clearedLines` — **no** before/after
  `fullLineCount` capture, no re-derived union. `model.js`
  does not define `fullLineCount`; it lives in `t1/model.js` (`t1/implementation.md`) and the inner
  machine uses it.

- **§4-T2b — `combo` field carries the +1.** `T2.v` stores `combo = visible + 1`. JS
  keeps the field identical (`this.combo`); the displayed/scoring combo is `combo - 1`
  with `nat`-style flooring at 0, realised as `natSub(this.combo, 1)` (`lib/utils.js`
  `natSub(a,b) = a>b ? a-b : 0`; skill: `nat` subtraction → `natSub`).

- **§4-T2c — `nat` division.** `level := 1 + totalClearedLines/10` uses **integer** division:
  `1 + natDiv(totalClearedLines, 10)` (`lib/utils.js` `natDiv(a,b) = Math.floor(a/b)`). No `mod`
  is needed in the current `T2.v` (level/total are independent accumulators).

- **§4-T2d — the move/rotate/fall scalars ride along unchanged.** `MovePiece`,
  `RotatePiece`, and the move-branch of `FallStep` are `UpdateS1` of a T1 call: the five
  T2 fields are copied verbatim. In JS this is automatic because those methods mutate only
  the inner `this.s1`; `this.score/level/combo/perfectClear/totalClearedLines` are left
  untouched. No explicit copy needed (skill: `UpdateS1` = "delegate + leave scalars").

- **§4-T2e — saturating caps on incremented fields (defensive).** The accumulators
  `score`, `combo`, and `totalClearedLines` grow without a model bound (`T2.v` places no
  cap on them — unlike T1's bounded state). To keep every field a *safe integer*, each
  increment saturates at `MAX_SAFE_INTEGER` using `lib/utils.js` `capAdd`:
  `capAdd(a, b, max) = b > max - a ? max : a + b`. Critically, `capAdd` tests headroom
  (`b > max - a`) **before** forming `a + b`, so it never constructs an unsafe sum (a
  post-hoc `Math.min(max, a+b)` is WRONG: `a+b` past `2^53` may round below `max` and
  defeat the clamp). Saturation is monotone, so it preserves `NonDecreasing*`.
  - Only the **accumulators** are capped: `score`, `combo`, `totalClearedLines`.
  - `level` is **not** capped directly; it is recomputed as `1 + natDiv(totalClearedLines,
    10)`. Since `totalClearedLines ≤ MAX_SAFE_INTEGER`, `level ≤ 1 + ⌊MAX/10⌋ < MAX`, so
    `level` is a safe integer by inheritance (no clamp needed; see §8.4 below for the
    cap-soundness argument proofs.md must give).
  - `perfectClear` is a flag (no cap). `clearedLines ∈ [0,4]` and `points(...)` outputs are
    bounded by the formula (≤ ~2800·level), but `score + points` is the unbounded site, so
    the cap lives on the `score` accumulation, not on `points` itself.

---

## 5. Free functions emitted by `model.js` (T2.v source order)

All operate on `boolean[][]`, or the widened `(false|Piece)[][]` `mg`/`RotGrid` output
(T1's grid representation, `t1/implementation.md` D1). `model.js`
imports `natSub`, `natDiv`, `capAdd` (and, transitively via the T1 engine, the grid
primitives) from `lib/utils.js`; it does not redefine them.

- `fullLineCount(g)` is **not** a T2 free function: it lives in `t1/model.js` (it sets
  `T1.State.clearedLines`). `model.js` re-exports it (`fullLineCount: T1Eng.fullLineCount`)
  for the UI/oracle/tests but does not define it.

- `emptyGridb(g)` — `EmptyGridb` (T2.v): `g.every(row => row.every(c => !T1Eng.occ(c)))`
  — routed through T1's `occ` (D1), correct for both `boolean[][]` and the colored
  `(false|Piece)[][]` cell type.

- `lineClearPoints(clearedLines, level)` — `LineClearPoints`: `switch(clearedLines){
  0→0; 1→100*level; 2→300*level; 3→500*level; default→800*level }`.

- `comboPoints(level, combo)` — `ComboPoints`: `combo > 0 ? 50*combo*level : 0`.

- `perfectClearPoints(perfectClear, clearedLines, level)` — `PerfectClearPoints`:
  `!perfectClear ? 0 : switch(clearedLines){ 0→0; 1→800*level; 2→1200*level; 3→1800*level;
  default→2000*level }`.

- `points(clearedLines, level, combo, perfectClear)` — `Points`:
  `lineClearPoints(clearedLines, level) + comboPoints(level, combo)
   + perfectClearPoints(perfectClear, clearedLines, level)`.

Argument orders match the `T2.v` definitions exactly (note `comboPoints` is `(level,
combo)` and `perfectClearPoints` is `(perfectClear, clearedLines, level)`).

---

## 6. `T2.Machine`

Constructed by `T(...)` (§7). Wraps a `T1.Machine`. Fields mirror `T2.State`.

### 6.1 Constructor — `Init p` (T2.v)

```
this.s1               = new T1Eng.Machine(p0)   // T1.Init p
this.score            = 0                        // req-score-init
this.level            = 1                        // req-level-init
this.combo            = 0
this.perfectClear     = false
this.totalClearedLines = 0
```

### 6.2 `movePiece(dy, dx)` — `MovePiece` (T2.v)

```
return this.s1.movePiece(dy, dx);   // delegate; scalars unchanged (§4-T2d)
```
Returns the inner boolean (fired / stuttered). No T2 field changes.

### 6.3 `rotatePiece(cw)` — `RotatePiece` (T2.v)

```
return this.s1.rotatePiece(cw);     // delegate; scalars unchanged
```

### 6.4 `fixPiece(pNew)` — `FixPiece` (T2.v)  [the only non-trivial T2 logic]

Sequential order, mirroring `T2.FixPiece`'s `let`-bindings. `clearedLines` is read from the
inner T1 state (§4-T2a); the §4-T2e saturating caps apply. `MAX` = the engine's
`MAX_SAFE_INTEGER` parameter (§7).

```
 1.  const fired = this.s1.fixPiece(pNew);             // T1.FixPiece; mutates this.s1 in place
 2.  if (!fired) return false;                          // option_map None ⇒ no T2 update
 3.  const clearedLines  = this.s1.clearedLines;        // T2.v: s1'.(clearedLines) (set by T1 on pre-clear grid)
 4.  const combo2        = (clearedLines === 0) ? 0 : capAdd(this.combo, 1, MAX);  // combo'
 5.  const perfectClear2 = emptyGridb(this.s1.mg);                     // EmptyGridb s1'.(mg)
 6.  const pts = points(clearedLines, this.level,
                        natSub(combo2, 1), perfectClear2);             // Points … (combo'-1), OLD level
 7.  const total2 = capAdd(this.totalClearedLines, clearedLines, MAX); // totalClearedLines'
 8.  this.combo             = combo2;
 9.  this.perfectClear      = perfectClear2;
10.  this.score             = capAdd(this.score, pts, MAX);            // saturating; OLD level used in pts
11.  this.totalClearedLines = total2;
12.  this.level             = 1 + natDiv(total2, 10);                  // 1 + totalClearedLines'/10 (NEW total)
13.  return true;
```

Ordering note (skill §4b): `clearedLines` is read from the inner state immediately after
`this.s1.fixPiece` (step 3), so it reflects this fix (T1 sets it on the post-union pre-clear
grid). Steps 3–7 read pre-state scalars (`this.combo`, `this.level`, `this.totalClearedLines`);
steps 8–12 write. `pts` (step 6) uses the **pre-state** `this.level`, and `this.score` is
written in step 10 — so `score` uses the **old** `level`, matching `Points clearedLines
s.(level) …`. `this.level` is written in step 12 from the **new** total (`total2`) — matching
`1 + totalClearedLines'/10`. Do not write `this.level` before computing `pts`, else the score
would use the new level. `level` is a pure function of the new total (not an increment), so it
is **not** capped (§4-T2e); the cap rides on `score`/`combo`/`totalClearedLines` only.

### 6.5 `fallStep(pNew)` — `FallStep` (T2.v)

```
if (this.movePiece(-1, 0)) return true;   // T2.MovePiece (-1) 0 — delegate, scalars unchanged
return this.fixPiece(pNew);               // T2.FixPiece — full §6.4 logic
```
Guards are mutually exclusive exactly as in T1 (skill §6.6); the inner `T1` move-branch
and fix-branch never both fire.

### 6.5a `get gameover()` — controller convenience, not a `T2.State` field

```js
get gameover() { return this.s1.gameover; }
```
Realizes T2.v's own `gameover` helper (`T1.gameover (s1 s)`) — a pass-through read
of the embedded T1 state, not a stored T2 field, so it needs no entry in `Init`, no
new field write anywhere, and no place in `snapshot`'s field list beyond what
`T1Eng.snapshot` already includes (§6.6). Exists purely so `controller.js` can read
`machine.gameover` directly instead of `machine.s1.gameover`.

### 6.6 `snapshot(machine)` — read-only observer (extends T1's)

Returns the T1 snapshot fields **inline** plus the five T2 fields:
```
{ ...T1Eng.snapshot(this.s1),    // mg, p, py, px, pr, gameover  (deep-copied by T1)
  score, level, combo, perfectClear, totalClearedLines }
```
`totalClearedLines` is included for completeness/oracle diffing; the UI does not read it
(§14). All T1 grid data is deep-copied by the inner `snapshot` (skill §4d).

### 6.7 `checkInvariants` (D7, default off)

`checkInvariants(s, message, isOccupied = c => Piece.includes(c))` — the `isOccupied`
parameter exists purely to be forwarded: T2 itself never needs a non-default value
(only `T7`, which introduces the `'garbage'` cell sentinel, ever overrides it), but
every layer between `T1` and any `Ti` that does must pass it through untouched, or a
descendant's override never reaches `T1Eng.typeOK` where it's actually checked. If
`CHECK_INVARIANTS`: assert `T1Eng.checkInvariants(this.s1, message, isOccupied)` (a
single delegated call — no separate direct `T1Eng.typeOK(this.s1)` assertion; that
would just duplicate what `T1Eng.checkInvariants` already does internally), and assert
the T2-only `LevelCorrect` (`this.level === 1 + Math.floor(this.totalClearedLines / 10)`),
`this.combo >= 0`, `this.totalClearedLines >= 0`, `this.score >= 0`, and that all four
numeric fields are `Number.isSafeInteger` (the cap, §4-T2e, guarantees this). These mirror
`T2.Correct`'s extra `LevelCorrect` conjunct and the cap-soundness obligation (`t2/proofs.md`
§5; cap soundness per this doc's §8.4 below).

### 6.8 Flattened-access retrofit (T5's `implementation.md` §0.3) — no change needed here

T5's `implementation.md` §0.3 retrofits T2–T5's `model.js` so that reaching `T1Eng` and
the innermost `T1.Machine` stays a one-hop access regardless of how many models are
stacked on top. T2 needs no change for either part: `this.s1` is already T2.Machine's
own field (literally named `s1`, not a nested one), and `T1Eng` is already returned
directly (`t2/model.js`'s own `T1Eng` constant, not a re-export of something deeper).

---

## 7. `model.js` exported function

```js
export function T(
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX,
  MAX_SAFE_INTEGER = Number.MAX_SAFE_INTEGER,
) { … }
```

Parameter order is **identical to `T1`** (§7 of `t1/implementation.md`) — T2 adds no abstract
parameters. Internally:
```
const T1Eng = T1(Piece, InitialMainGrid, ForbiddenGrid,
                 RotGrid, InitialY, InitialX, PW, FY, FX, MAX_SAFE_INTEGER);
```
`checkAxioms` is the inner `T1Eng.checkAxioms` (no new axioms in T2). The returned object
exposes (in order): the §5 free functions, `T1Eng` (or a re-export of its free functions
if convenient), `checkInvariants`, `Machine` (the §6 `T2.Machine`), `snapshot`. `Machine`
closes over `T1Eng`. There is no separate `checkAxioms` for T2.

---

## 8. `proofs.md` (scope)

`t2/proofs.md` establishes that `model.js` simulates `T2.v`, reusing:
1. `t1/model.js ⊨ T1.v` (`t1/proofs.md`) for the `s1` half.
2. `RefineT1` (T2.v): every T2 transition's `s1` component is the corresponding T1
   transition — so `movePiece`/`rotatePiece`/the move-branch of `fallStep` need no new
   argument beyond "delegates to the verified T1 method, scalars untouched".
3. New per-field obligations for `fixPiece` only: `score`, `level`, `combo`,
   `perfectClear`, `totalClearedLines` equal their `T2.FixPiece` values. Each is a direct
   transcription (§6.4) of a `let`-binding; the one subtlety, `clearedLines`, is now read
   from the inner state (`this.s1.clearedLines` = `s1'.(clearedLines)`). `T1.v` sets that
   field to `FullLineCount u` on the post-union pre-clear grid `u`; `t1/proofs.md`'s
   L-clearedLines establishes the JS `t1/model.js` writes exactly that value. So `T2` consumes a
   correct count with no re-derivation and no difference-of-counts.
4. `LevelCorrect` preservation (the extra `T2.Correct` conjunct, not covered by
   `RefineT1`): `level` is `1 = 1 + natDiv(0, 10)` at init (`totalClearedLines = 0`), and
   `fixPiece` recomputes `level := 1 + natDiv(total2, 10)` from the **same** `total2` it
   just wrote to `this.totalClearedLines`; `movePiece`/`rotatePiece` leave both fields
   unchanged. Hence `this.level === 1 + natDiv(this.totalClearedLines, 10)` holds after
   every step — `LevelCorrect` — and in particular `this.level ≥ 1`, discharging
   `ScoreRisesOnClear`'s `Hc` need.
5. **Cap soundness (§8.4 below).** The saturating caps (§4-T2e) are a JS-representational
   safeguard with no `T2.v` counterpart; argue they preserve monotonicity and `level`'s
   range. See §8.4.
6. Out of scope (controller, safety-only boundary as in T1): fall-speed (§15), banner
   timing (§14). No liveness.

### 8.4 Integer-range / cap soundness

The new arithmetic (`score`, `points`, `level`, `totalClearedLines`) is unbounded in
`T2.v`: `score` and `totalClearedLines` grow without any model bound, unlike T1's bounded
state. There is **no** `T2JsBounds.v` and **no** machine-checked "never overflows" claim —
that claim would be false, since a long enough game exceeds any fixed bound. Instead
`model.js` applies a **saturating cap** at `MAX_SAFE_INTEGER` to the three accumulators
(`score`, `combo`, `totalClearedLines`) via `capAdd` (§4-T2e). proofs.md states two things
about this cap, both elementary:

- **Safety of representation.** `capAdd(a,b,MAX)` returns a safe integer for all
  `0 ≤ a ≤ MAX`, `0 ≤ b` (it tests `b > MAX − a` before adding, never forming an unsafe
  sum). So every field stays a safe integer at every step — the JS analogue of T1's
  `NoOverflow`, but achieved by saturation rather than by a structural bound.
- **Monotonicity preserved.** Saturation is monotone and ≥ identity-on-the-left
  (`capAdd(a,b) ≥ a` for `b ≥ 0`), so `NonDecreasingScore` / `NonDecreasingLevel` and
  `totalClearedLines` monotonicity still hold under capping. `ScoreRisesOnClear` is
  unaffected *until* `score` reaches `MAX` (after which it cannot strictly rise); flag this
  as the one place the cap weakens an abstract property, reachable only after ~10¹⁵ points,
  i.e. never in real play.
- **`level` bound by inheritance.** `level = 1 + natDiv(totalClearedLines, 10)` and
  `totalClearedLines ≤ MAX` give `level ≤ 1 + ⌊MAX/10⌋ < MAX`, so `level` is a safe integer
  without its own clamp. This is the proof obligation justifying "cap accumulators only".

The cap is therefore a documented divergence from `T2.v` (which has no cap): `model.js` refines
`T2.v` exactly up to the saturation point and conservatively (monotonically) beyond it.

---

## 9. Tests (`tests/`)

Mirror T1's suite (`t1/implementation.md` §9) on the **small fixture**.

- `testInstance.js` — re-exports T1's `tests/testInstance.js` (PW=2, one L-piece, 4×4
  grid, the structural `rotGrid`) verbatim; adds nothing (T2 has no new params). Re-export
  so the T2 suites import from one place.
- `oracle.js` — faithful `T2.v` interpreter. Reuses T1's oracle for the `s1` part
  (`oracleInit`/`oracleNext` over the inner state) and adds the five scalar fields,
  reading `clearedLines` from the inner T1 oracle state (the T1 oracle now sets it on the
  pre-clear union grid), then `score`/`level`/`combo`/`perfectClear`/
  `totalClearedLines` per `T2.FixPiece`. Exposes `oracleInit`, `oracleNext`,
  `states2Equal` (compares all six components), `applyEvent2`.
- `model.unit.test.js` — golden vectors for `lineClearPoints`/`comboPoints`/
  `perfectClearPoints`/`points` (all `clearedLines ∈ {0,1,2,3,4,5}`, `combo ∈ {0,1,2}`,
  `perfectClear ∈ {false,true}`, a couple of `level`s); `fullLineCount`/`emptyGridb`;
  and `fixPiece` scenarios that actually clear lines (fill a 4×4 row, fix, assert score
  and level deltas; a perfect-clear scenario; a combo sequence across two consecutive
  clearing fixes; a non-clearing fix asserts combo resets to 0 and score unchanged).
- `model.properties.test.js` — fast-check: every event preserves the T1 invariants on `s1`
  (delegate to T1 `typeOK`), `level ≥ 1` always, `score`/`level`/`totalClearedLines`
  non-decreasing, all numeric fields stay safe integers, and the differential oracle (all
  six components). For "score strictly rises on a clear", detect a clear via the
  **`totalClearedLines` delta this step**, NOT `s1.clearedLines > 0`: `clearedLines` carries
  through `MovePiece`/`RotatePiece` unchanged, so a `Fall` resolving as a move leaves a
  previous fix's `clearedLines` value in place and would give a false positive.
- `model.fuzz.test.js` — dependency-free xorshift runner, same shape as T1's: N seeds × M
  steps, structural + monotonicity checks + safe-integer checks + the same
  `totalClearedLines`-delta clear detection + oracle differential (six components) at every
  step.

The SRS grids in the real `instance.js` are validated by `checkAxioms` at startup
(inherited from T1), not by these suites — same boundary as T1 (`t1/implementation.md` §13.6).

---

## 10. Acceptance oracle (definition of correct regeneration)

A regeneration is correct iff:
1. Every `T2.v` definition with a §3 mapping is realised with the mapped name/behaviour;
   every "not emitted" entry is absent.
2. `model.js` constructs the T1 engine via `T1(...)` (imported as alias for `T` from `t1/model.js`) and never reimplements a T1 free
   function or duplicates `t1/model.js`.
3. `tests/` passes on the small fixture: unit + fuzz fully; properties under `fast-check`
   when installed (network-gated, as in T1).
4. The differential oracle (`oracle.js`) agrees with `model.js` on all six state components
   over every generated trace.
5. `fixPiece` reads `clearedLines` from the inner T1 state immediately after the inner
   fix (§4-T2a), and scores with the **old** `level` while setting the **new** `level` from
   the updated total
   (§6.4 ordering).

Byte-identity is not required; behavioural equivalence up to the §3 naming map is.

---

## 11. Instantiation (`instance.js`)

```js
export * from '../t1/instance.js';
```
T2 introduces no abstract parameters, so `instance.js` is a pure re-export of the T1
`instance.js` (the 7 SRS pieces, 22×10 grid, forbidden zone, colours, `InitialY=19`,
`InitialX=3`). `model.js`'s `checkAxioms` (= T1's) validates it at construction (`new eng.Machine(...)`,
where `eng = T(...)`).
Fall-speed constants are **controller** constants and live in `controller.js` (§15), not here.

---

## 12. Generator determinism rules

Inherit `t1/implementation.md` §12 verbatim (temperature 0, frozen orders, no invented
behaviour, ambiguity→TODO, closure-scope rule). T2 addition:

- **Reuse over restatement.** Never copy a T1 definition into `model.js`/`view.js`/`controller.js`
  when it can be imported. The only intentional duplications are the new `view.js`/
  `controller.js` (they extend, not fork, T1's view/controller) and `index.html`. If a T2
  file would be byte-identical to its T1 counterpart, import the T1 one instead.

---

## 13. `instance.js` parameters

None beyond T1's. See §11. (Section kept for parallelism with `t1/implementation.md` §13;
intentionally empty of new content.)

---

## 14. `view.js` — renderer (grid + left info panel + transient banners)

### 14.1 Public API

```js
export function render(canvas, constants, snapshot, pieceColor, banners) { … }
```
- `constants` — `{ HM, WM, PW, FY, FX, FH, FW, rotGrid, PANEL_PX }` (T1's struct plus
  `PANEL_PX`, the left-panel pixel width, §14.2). Read-only.
- `snapshot` — `model.js`'s `snapshot` (T1 grid fields inline + `score`, `level`, `combo`,
  `perfectClear`). `totalClearedLines` is present but unused by the UI (D3).
- `pieceColor` — as T1.
- `banners` — controller-owned transient `{ combo, perfectClear, t } | null` (§15),
  snapshotting the values at the triggering fix and the timestamp; `null` when no banner
  is active.

`view.js` imports nothing from `model.js`/`instance.js` (same decoupling as T1's `view.js`).

### 14.2 Layout / scaling

The grid keeps square cells; the **left panel width is relative to the viewport, not to
the cell size** (a cell can be tiny when the grid is large). `controller.js` computes
(§15.6a):
```
PANEL_PX  = round(PANEL_FRAC × viewportW)      // PANEL_FRAC = 0.22, clamped to [120, 360] px
gridMaxW  = viewportW × 0.95 − PANEL_PX
gridMaxH  = viewportH × 0.95
cellSize  = max(1, floor(min(gridMaxW / WM, gridMaxH / HM)))
canvas.width  = PANEL_PX + WM × cellSize
canvas.height = HM × cellSize
```
`PANEL_PX` is passed into `constants`. The grid is drawn offset right by `PANEL_PX`; the
panel occupies `[0, PANEL_PX)`.

### 14.3 Coordinate transform

Grid cell `(y, x)` → canvas pixel `(PANEL_PX + x·cellSize, (HM−1−y)·cellSize)`. The only
change from T1's `cellOrigin` is the additive `PANEL_PX` on the x axis:
```js
function cellOrigin(y, x, cellSize, HM, panelPx) {
  return { cx: panelPx + x * cellSize, cy: (HM - 1 - y) * cellSize };
}
```
All grid sub-procedures take `PANEL_PX` (from `constants`) and use this.

### 14.4 Sub-procedures

Grid sub-procedures (`drawBackground`, `drawGridLines`, `drawBlock`, `drawGrid`,
`drawPiece`, `drawGameOver`) are T1's, adjusted only to (a) offset x by `PANEL_PX` via the
updated `cellOrigin`, and (b) clear the **whole** canvas in `drawBackground` (already
T1's behaviour) so the panel area is cleared too. New T2 sub-procedures:

```js
function panelMetrics(constants) {
  const { PANEL_PX } = constants;
  const margin = PANEL_PX * 0.12;
  const labelFont = Math.max(10, Math.floor(PANEL_PX * 0.11));
  const valueFont = Math.max(12, Math.floor(PANEL_PX * 0.17));
  const bannerFont = Math.max(10, Math.floor(PANEL_PX * 0.10));
  return { margin, labelFont, valueFont, bannerFont };
}
```
Both `drawPanel` and `drawBanners` call this rather than each computing its own
margin/font sizes — the two functions lay out the same column, so a single source
keeps their fractions from drifting apart.

```
drawPanel(ctx, constants, snapshot, cellSize)
  — fills the panel column [0, PANEL_PX) with the page background (#111); draws, top-down,
    left-aligned with panelMetrics's margin:
      "SCORE"  label  + snapshot.score        (value on next line, larger)
      "LEVEL"  label  + snapshot.level
    Font sizes are relative to PANEL_PX (labelFont = PANEL_PX×0.11, valueFont = PANEL_PX×0.17,
    floored at 10/12 px), NOT to cellSize. Numbers are decimal, no grouping.

drawBanners(ctx, constants, banners, cellSize)
  — when banners ≠ null, draws in the panel BELOW the LEVEL block, stacked so they never
    overlap (combo line first, perfect-clear line below):
      if banners.combo - 1 > 0:   "<n>-hit combo!"  with n = banners.combo - 1   (skill §6 / §4-T2b)
      if banners.perfectClear:    "Perfect clear!"
    bannerFont = PANEL_PX×0.10 floored at 10px. Combo colour #FFD000, perfect-clear colour
    #00E0FF. Both lines are allotted a fixed slot height (bannerFont×1.4) so the
    perfect-clear line position is independent of whether the combo line is shown
    (reserve the combo slot even when empty, so "Perfect clear!" never jumps).
```

`n-hit combo!` uses `banners.combo - 1` (the visible combo); shown only when `≥ 1`, i.e.
the stored `combo ≥ 2` — no combo banner on the first clear of a streak (§B2, matches
scoring). Both banners read the controller's *snapshotted* values (§15), not live fields.

### 14.5 Piece colour parameter

As T1 §14.5 (`pieceColor` param, fallback `#FFFFFF`); `controller.js` passes `PieceColor`.

### 14.6 Call order inside `render`

```
1. drawBackground        (whole canvas)
2. drawPanel             (score / level)
3. drawBanners           (combo / perfect-clear, if banners ≠ null)
4. drawGrid              (locked blocks, offset by PANEL_PX)
5. drawGridLines         (offset by PANEL_PX)
6. drawPiece             (active piece, clipped, offset by PANEL_PX)
7. if snapshot.gameover: drawGameOver   (overlay spans the GRID area; panel stays readable)
```
`drawGameOver` overlay covers the grid region `[PANEL_PX, canvas.width)`, leaving the panel
visible (so score/level remain readable at game over). `maxWidth`-constrained text as T1.

---

## 15. `controller.js` — controller / entry point

Extends T1's `controller.js`. Imports `T` from `./model.js`, `render` from `./view.js`, and the
parameters from `./instance.js`. Same input model (keyboard + gamepad, shared DAS engine,
single rAF loop, §15.7/§15.8 of `t1/implementation.md`) — reused verbatim except where noted.

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
  rotGrid: eng.T1Eng.rotGrid,
  PANEL_PX: 0,              // set by sizeCanvas (§15.6a) before first frame
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
automatic fall step is due, in place of a separate timer. `disposed` guards against
`frame` re-scheduling itself after `dispose()` (§15.7) has already fired for an
in-flight frame.

### 15.4 Fall speed — classic Tetris gravity (§C1)

```js
const BASE_PERIOD = 1000;   // ms at level 1 (1000 × 0.8^0)
const MIN_PERIOD  = 16;     // ms floor (~one 60 Hz frame)
const EPS         = 1e-6;   // guard so the base stays positive for very high levels

// time-per-cell (seconds) = (0.8 − (level−1)·0.007)^(level−1); ms, rounded, floored.
function fallPeriod(level) {
  const base = Math.max(EPS, 0.8 - (level - 1) * 0.007);
  const secs = Math.pow(base, level - 1);
  return Math.max(MIN_PERIOD, Math.round(BASE_PERIOD * secs));
}
```
Level 1 → 1000 ms, 2 → 793, 5 → 394, 10 → 118, flooring at 16 ms; total for all `level ≥ 1`
(§C1.3 base-guard). `currentGravityPeriod` is recomputed whenever `level` changes
(§15.5), and `frame` (§15.7) fires the next fall step once `now - lastGravityAt >=
currentGravityPeriod`.

### 15.5 `afterAction(now)` / fix detection / banner capture

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
Runs after every state-changing input (tick, key, gamepad) and:
1. If `machine.level !== prevLevel` → recompute `currentGravityPeriod` and restart
   the gravity accumulator fresh at `now` (faster gravity takes effect at the moment
   the level rises, discarding whatever had already accumulated toward the previous
   period — off the same clock `frame` already uses for input, not a second
   independent timer).
2. Banner capture: if the just-applied action was a fix that cleared lines, snapshot the
   banner. Detection without leaking model internals: compare `machine.totalClearedLines`
   to a stored previous value; if it grew, a clear happened this action. On a clear,
   set `banner = { combo: machine.combo, perfectClear: machine.perfectClear, t: now }`.
   (`combo`/`perfectClear` are read straight after the fix, so they are this clear's
   values.) Update the stored previous total.
3. Gameover: if `machine.gameover` → `handleGameover()`.

`banner` is cleared (set to `null`) when `now - banner.t > BANNER_MS` (§15.6),
`BANNER_MS = 1200`.

```js
function onTick(now) {
  machine.fallStep(randomPiece());
  afterAction(now);
}
```

### 15.6 Banner lifetime

```
const BANNER_MS = 1200;   // combo / perfect-clear banner visible duration
```
In the frame loop, before `render`, expire the banner: `if (banner && now - banner.t >
BANNER_MS) banner = null;`. `render` receives `banner` (may be `null`).

### 15.6a `sizeCanvas` (§14.2 geometry)

Computes `PANEL_PX` from the viewport (not the cell size) and sets `canvas.width/height`
per §14.2, then writes `constants.PANEL_PX = PANEL_PX`. Registered on `resize` and called
once before the first frame.

```js
function sizeCanvas() {
  const PANEL_FRAC = 0.22, PANEL_MIN = 120, PANEL_MAX = 360;
  const vw = window.innerWidth, vh = window.innerHeight;
  const panel = Math.min(PANEL_MAX, Math.max(PANEL_MIN, Math.round(PANEL_FRAC * vw)));
  const gridMaxW = vw * 0.95 - panel;
  const gridMaxH = vh * 0.95;
  const cell = Math.max(1, Math.floor(Math.min(gridMaxW / constants.WM,
                                               gridMaxH / constants.HM)));
  constants.PANEL_PX = panel;
  canvas.width  = panel + constants.WM * cell;
  canvas.height = constants.HM * cell;
}
```

### 15.7 Logical actions + keyboard/gamepad handlers

```js
const ACTIONS = {
  LEFT:  { repeat: true,  effect: (now) => { machine.movePiece(0, -1); afterAction(now); } },
  RIGHT: { repeat: true,  effect: (now) => { machine.movePiece(0, 1); afterAction(now); } },
  DOWN:  { repeat: true,  effect: (now) => { machine.fallStep(randomPiece()); afterAction(now); } },
  CCW:   { repeat: false, effect: (now) => { machine.rotatePiece(false); afterAction(now); } },
  CW:    { repeat: false, effect: (now) => { machine.rotatePiece(true); afterAction(now); } },
};

const KEYMAP = new Map([
  ['ArrowLeft', 'LEFT'], ['ArrowRight', 'RIGHT'], ['ArrowDown', 'DOWN'],
  ['z', 'CCW'], ['x', 'CW'],
]);

const GAMEPAD_MAP = new Map([
  [14, 'LEFT'], [15, 'RIGHT'], [13, 'DOWN'],
  [0, 'CCW'], [1, 'CW'],
]);
```
Each effect takes the tick's `now` and forwards it to `afterAction` (§15.5), so
level-change rescheduling and banner capture happen uniformly on every action path —
`controller.js` never calls `fixPiece` directly, only `fallStep` (the soft-drop key
uses it too).

`processInput`/DAS engine (`computeHeld`, the repeat/tap-edge dispatch loop over
`ACTIONS`) is unchanged in shape from T1's — one more entry in the loop, no T2-specific
branch.

```js
function frame(now) {
  processInput(now);
  if (!machine.gameover && now - lastGravityAt >= currentGravityPeriod) {
    lastGravityAt = now;
    onTick(now);
  }
  if (banner && now - banner.t > BANNER_MS) banner = null;
  render(canvas, constants, eng.snapshot(machine), PieceColor, banner);
  if (disposed) return; // dispose() may have fired while this frame was already in flight
  rafId = window.requestAnimationFrame(frame);
}
```
`startGame()` resets `prevLevel = 1`, `banner = null`, and the stored previous total,
and recomputes `currentGravityPeriod`/`lastGravityAt` fresh, in place of T1's fixed
1000ms-period start.

`main(canvas)` returns a `dispose()` function that cancels the pending animation
frame, removes every listener `main` registered, and clears `keyHeld`/`repeatTimers`
— makes `main()` safe to call again for a fresh, independent game with no leftover
state or duplicate handlers from a previous call.

### 15.10 `index.html`

T1's shell with the script importing `./controller.js`:
```html
<canvas id="game" width="360" height="360"></canvas>
<script type="module">
  import { main } from './controller.js';
  main(document.getElementById('game'));
</script>
```
Placeholder canvas size; `sizeCanvas` overwrites it (now including the panel) on load and
resize. `overflow: hidden`, viewport meta, full-height flex centring as T1.

