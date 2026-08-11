# proofs.md — refinement proof, `t2/model.js ⊨ T2.v`

`T2.v` refines `T1.v` via `f = (fₑ, fₛ)` with `fₛ = s1`
(state projection) and `fₑ` the constructor-wise identity on events. This proof
reuses `t1/model.js ⊨ T1.v` for the `s1` half wherever T2's own transition
delegates to a T1 one, and argues only the five new scalar fields where T2 adds
logic of its own (`fixPiece`).

## 1. Scope

Safety/refinement only, exactly as `t1/proofs.md` §1 (D11): no liveness. Additionally
out of scope here: fall-speed (`controller.js` §15, level → interval period) and
banner timing (`view.js`/`controller.js` §14–15) — controller concerns with no
`T2.v` counterpart, same boundary as T1's fall-timing was.

## 2. State mapping and reuse of `t1/proofs.md`

`T2.Machine`'s `s1` field holds a real `T1.Machine` (skill §7's reuse principle:
`B`'s state embeds `A`'s). The refinement mapping is

```
α_T2(js) = { s1 := α_T1(js.s1)
           ; score := js.score
           ; level := js.level
           ; combo := js.combo
           ; perfectClear := js.perfectClear
           ; totalClearedLines := js.totalClearedLines
           }
```

— apply `t1/proofs.md`'s `α_T1` to the embedded inner machine, map T2's five new
fields directly (skill §7.2). `α_T1` is already established total and well-defined
on every reachable `js.s1` by `t1/proofs.md` §2; the five new fields are plain
`number`/`boolean` scalars needing no coercion.

`T2.v`'s own `RefineT1` theorem is the formal statement that `fₛ` commutes with
`Next`: for every T2 transition `T2.Next e2 s2 = Some s2'`,
`T1.Next (fₑ e2) (fₛ s2) = Some (fₛ s2')`. Per §7.1 (full use / partial use / no
use):

`Machine.gameover` (a getter, `get gameover() { return this.s1.gameover; }`) is a
**controller convenience, not a T2.State field**: it stores nothing and is not part
of `α_T2`'s domain — it is a pass-through read of `α_T1`'s own `gameover`, added
only so `controller.js` can write `machine.gameover` instead of `machine.s1.gameover`.
Since it introduces no new state, it needs no new refinement argument beyond
`t1/proofs.md`'s existing `gameover` correspondence.

- **`movePiece`, `rotatePiece`, and the move-branch of `fallStep`** are **full
  uses**: `T2.MovePiece`/`RotatePiece` are exactly `UpdateS1` of the corresponding
  `T1` call — T2 contributes no new guard or field write. JS: `this.s1.movePiece(dy,dx)`
  / `this.s1.rotatePiece(cw)`, one-line delegating calls (§9 below). T1's own action
  lemma (`t1/proofs.md` §9) transfers unchanged; T2's obligation is only "the inner
  machine received the identical call."
- **`fixPiece`** is a **partial use**: it calls the inner `T1.Machine.fixPiece`
  first, then computes `score`/`level`/`combo`/`perfectClear`/`totalClearedLines`
  from fields the inner action already set (`this.s1.clearedLines`, `this.s1.mg`)
  — only that second part is new (§3 below).
- No T2 action is a **no-use** case (T2 introduces no event without a T1
  counterpart).

## 3. `fixPiece` — the new logic

`T2.FixPiece p_new s` is `option_map` over `T1.FixPiece p_new (s1 s)`: `None` iff
the inner call fails, otherwise every field of the result is a `let`-bound
computation over the inner post-state `s1'` and the pre-state T2 scalars. The JS
`fixPiece` reproduces this field-by-field, assuming `typeOK(this.s1)` (from
`t1/proofs.md` §5, transferred since `this.s1` is a genuine `T1.Machine`):

- **Guard / `option_map None`**: `const fired = this.s1.fixPiece(pNew); if (!fired)
  return false;` — the inner call's own guard-fail argument (`t1/proofs.md` §9)
  applies; on failure `this.s1` is untouched (T1's stuttering-step argument), and no
  T2 field is written, matching `option_map` over `None`.
- **`clearedLines` (§4-T2a)**: `const clearedLines = this.s1.clearedLines;` reads
  `s1'.(clearedLines)` directly, per `T2.FixPiece`'s `let clearedLines := clearedLines
  s1'`. `t1/proofs.md`'s own field-by-field `fixPiece` argument (§9) establishes that
  `this.s1.clearedLines` after the inner call equals `FullLineCount u` on the
  post-union pre-clear grid — exactly `T1.v`'s `clearedLines s1'`. No re-derivation,
  no difference-of-counts.
- **`combo'`**: `const combo2 = (clearedLines === 0) ? 0 : capAdd(this.combo, 1,
  MAX);` matches `let combo' := if clearedLines =? 0 then 0 else combo s + 1`
  up to the saturating cap (§5 below) — `capAdd(a,1,MAX)` computes `a+1` whenever
  `a < MAX`, and only diverges from `+1` at the cap itself.
- **`perfectClear'`**: `const perfectClear2 = emptyGridb(this.s1.mg);` — `emptyGridb`
  is a direct transcription of `EmptyGridb`'s `forallbz2 (λ y x, negb (L g y x))`
  (every cell `false`) restricted to `[0,H g)×[0,W g)`, matching `js.mg`'s box
  under `typeOK` (`t1/proofs.md` §5 — every reachable `mg` is box-determined).
  Argument is `s1'.(mg)`, i.e. `this.s1.mg` **after** the inner fix, matching
  `EmptyGridb (mg s1')`.
- **`score`**: `const pts = points(clearedLines, this.level, natSub(combo2, 1),
  perfectClear2);` then (after `combo`/`perfectClear` are written) `this.score =
  capAdd(this.score, pts, MAX);`. `points` is `lineClearPoints + comboPoints +
  perfectClearPoints`, each a direct `switch`/conditional transcription of
  `LineClearPoints`/`ComboPoints`/`PerfectClearPoints` (case-for-case, argument
  order preserved per `implementation.md` §5 — `comboPoints(level,combo)`,
  `perfectClearPoints(perfectClear,clearedLines,level)`). `natSub(combo2,1)` is
  `combo'-1` under Rocq `nat` subtraction (floors at 0 — never negative since
  `combo2 ≥ 0`), matching `T1.v`'s comment "`combo'-1` is 0 at min because of nat
  subtraction". `this.level` at the point `pts` is computed is still the
  **pre-fix** value (not yet overwritten — see the ordering argument below),
  matching `Points clearedLines (level s) (combo'-1) perfectClear'`, i.e. the
  **old** `level s`.
- **`totalClearedLines'`**: `const total2 = capAdd(this.totalClearedLines,
  clearedLines, MAX);` matches `totalClearedLines s + clearedLines` up to the cap.
- **`level'`**: `this.level = 1 + natDiv(total2, 10);` — written from `total2`
  (already computed, itself already written to `this.totalClearedLines` at this
  point in the sequence), matching `1 + totalClearedLines' / 10` (Rocq `nat`
  division = `natDiv`, both floor).

**Simultaneous→sequential ordering (skill §4b).** `T2.FixPiece`'s `let`-block binds
`clearedLines`, `combo'`, `perfectClear'`, `totalClearedLines'` from `s1'` and `s`
(none of T2's own fields yet written), then assigns all five result fields
simultaneously; `score` reads `level s` (the pre-state value) and `combo'`/`perfectClear'`
(the freshly-bound locals), not `level s1'` (there is no such field — T2's `level` is
its own, not part of `s1`). The JS sequence in `fixPiece` (`model.js` §6.4,
reproduced in the method body) is:
1. `this.s1.fixPiece(pNew)` — mutates only `this.s1`; none of T2's own fields read
   or written yet.
2. `clearedLines`, `combo2`, `perfectClear2`, `pts`, `total2` are computed into
   locals, in that order; `pts` (step depending on `this.level`) is computed
   **before** `this.level` is overwritten (step below) — this is the one ordering
   hazard, and the JS body computes `pts` from `this.level` strictly before the
   `this.level = …` assignment.
3. `this.combo`, `this.perfectClear`, `this.score`, `this.totalClearedLines`,
   `this.level` are then written from the locals — `this.level`'s write reads
   `total2` (a local, already fixed at step 2), not `this.totalClearedLines`
   (which is written in the same step group but to the *same* value `total2`, so
   no discrepancy arises regardless of the two assignments' relative order).

No step reads a T2 field after it has been overwritten with a value the Rocq
`let`-block's corresponding read would not have seen: every read of `this.level`
happens before its own write; every other read is of a value computed once into a
local. This reproduces `T2.FixPiece`'s simultaneous assignment.

## 4. `fallStep` — disjoint-guard sequencing (skill §6.6)

Identical structure to `t1/proofs.md` §10: `T2.FallStep` tries `MovePiece (-1) 0`
first, falls back to `FixPiece p_new`. `T2.MovePiece (-1) 0`'s guard reduces to
`T1.MovePiece (-1) 0 (s1 s)`'s guard (full use, §2), and `T2.FixPiece`'s guard
likewise reduces to `T1.FixPiece`'s (its own guard is unconditional on T1's
success/failure — §3's guard step). So the same mutual-exclusivity argument
(`t1/proofs.md` §10) transfers: `this.movePiece(-1,0)` and `this.fixPiece(pNew)`
in `fallStep`'s JS body fire under exactly the guard conditions their Rocq
counterparts do, and never both.

## 5. Cap soundness (§8.4 of `implementation.md`)

`score`, `combo`, and `totalClearedLines` are unbounded accumulators in `T2.v` —
unlike T1's bounded state, there is no `T2JsBounds.v` and no claim that they never
exceed `Number.MAX_SAFE_INTEGER` in the abstract model, because that claim is false
for a sufficiently long game. `model.js` instead applies `capAdd` (`lib/utils.js`)
at every accumulation site (`combo2`, `total2`, `this.score`), which is a
**JS-representational safeguard with no `T2.v` counterpart**:

- **Representation safety.** `capAdd(a,b,max)` tests `b > max - a` before forming
  `a + b`; for every reachable `0 ≤ a ≤ max` and `b ≥ 0` (both hold here: `a` is
  itself a prior `capAdd` result or `0`; `b ∈ {0,1,clearedLines,pts}`, all
  non-negative), the returned value is exactly `min(a+b, max)` computed without
  ever forming an unsafe intermediate sum. Hence `score`, `combo`,
  `totalClearedLines` are `Number.isSafeInteger` at every reachable state — the
  JS-representational analogue of T1's structural `NoOverflow`.
- **Monotonicity preserved.** `capAdd(a,b,max) ≥ a` for `b ≥ 0` (either `a+b ≥ a`
  or the result is `max ≥ a`, since `a ≤ max` is an invariant maintained by every
  prior `capAdd` call and by `Init`'s `a=0`). So `NonDecreasingScore`,
  `NonDecreasingLevel` (via `total2 ≥ this.totalClearedLines` and
  `natDiv` monotone in its first argument), and `totalClearedLines` monotonicity
  all hold under capping — `movePiece`/`rotatePiece` leave the three accumulators
  untouched (§2), and `fixPiece` only ever grows them (or leaves `score` fixed
  when `pts = 0` and `clearedLines = 0` leaves `combo2 = 0 = ` — not necessarily
  `≥ this.combo`, but `T2.v`'s own `combo'` is likewise reset to `0` on a
  non-clearing fix, so this is not a T2-JS divergence, just `T2.v`'s own
  semantics: `combo` is not itself claimed non-decreasing by `CorrectStep`, only
  `score`/`level`).
- **`ScoreRisesOnClear` weakens only past the cap.** Once `score = MAX`, `capAdd`
  returns `MAX` regardless of `pts > 0`, so a clear no longer strictly raises
  `score`. This is the one place the cap diverges from `T2.v`'s abstract
  `ScoreRisesOnClear` — reachable only after accumulating ~`2^53` points
  (`MAX_SAFE_INTEGER`), i.e. not in any real play session. Flagged, not hidden.
- **`level` is a safe integer by inheritance, not its own cap.** `this.level = 1 +
  natDiv(total2, 10)` with `total2 ≤ MAX_SAFE_INTEGER` (by the point above) gives
  `this.level ≤ 1 + ⌊MAX_SAFE_INTEGER/10⌋ < MAX_SAFE_INTEGER`, safe without a
  direct clamp — justifying `implementation.md` §4-T2e's "cap accumulators only."

The cap is a **documented divergence** from `T2.v`: `model.js` refines `T2.v`
exactly up to the saturation point, and conservatively (monotonically, never
exceeding the true value it would have taken) beyond it.

## 6. `LevelCorrect` preservation

`LevelCorrect s := level s = 1 + totalClearedLines s / 10` is `T2.Correct`'s extra
conjunct beyond `T1.Correct (s1 s)`, not covered by `RefineT1` (which only
constrains the `s1` projection). Proved directly:

- **`Init`**: `this.totalClearedLines = 0`, `this.level = 1 = 1 + natDiv(0,10)`. ✓
- **`movePiece`/`rotatePiece`**: neither field is touched (§2, full-use delegation)
  — `LevelCorrect` is preserved trivially (both sides of the equation are
  unchanged).
- **`fixPiece`**: `this.level` is written (step 12 of §3's sequence) as `1 +
  natDiv(total2, 10)` from the **same** `total2` just written to
  `this.totalClearedLines` (step 11) — so immediately after `fixPiece` returns,
  `this.level === 1 + natDiv(this.totalClearedLines, 10)` holds by construction,
  not by a separate argument. (Guard-fail case: neither field is touched, §3.)

Hence `LevelCorrect` holds at every reachable state, and in particular
`this.level ≥ 1` always (since `natDiv(_, 10) ≥ 0`) — discharging the hypothesis
`ScoreRisesOnClear` needs from `Correct` (`level s > 0`, used implicitly wherever
`Points` is scaled by `level`).

## 7. `Init`

`constructor(p)` ≙ `Init p` (`T2.v`), field-by-field:

| field | JS | Rocq (`Init p`) |
|---|---|---|
| `s1` | `new T1Eng.Machine(p)` | `T1.Init p` — by `t1/proofs.md` §8 |
| `score` | `0` | `0` (req-score-init) |
| `level` | `1` | `1` (req-level-init) |
| `combo` | `0` | `0` |
| `perfectClear` | `false` | `false` |
| `totalClearedLines` | `0` | `0` |

`checkAxioms` is `T1Eng.checkAxioms` unchanged (T2 introduces no new abstract
parameters or axioms, `implementation.md` §7) — validated once, at `new
T1Eng.Machine(p)` inside the T2 constructor.

## 8. Each action — summary

- **`movePiece(dy,dx)`** — one-line delegation to `this.s1.movePiece(dy,dx)`;
  full-use transfer (§2). No T2 field read or written.
- **`rotatePiece(cw)`** — one-line delegation to `this.s1.rotatePiece(cw)`;
  full-use transfer (§2).
- **`fixPiece(pNew)`** — partial use; inner call transfers by §2, new logic
  argued in §3, ordering in §3's closing paragraph, cap soundness in §5,
  `LevelCorrect` in §6.
- **`fallStep(pNew)`** — disjoint-guard sequencing, §4.
