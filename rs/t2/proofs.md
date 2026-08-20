# proofs.md — refinement proof: `model.rs` ⊑ `T2.v`

Follows the `rocq-to-rust` skill's `proofs.md` skeleton (skill §6), specialized by §7's
wrapping-module rules: this file states only the **delta** over `t1/proofs.md`, reusing
`t1/model.rs ⊨ T1.v` in full for every `s1`-shaped fact. Order: parameter/state mapping
(§1–§2), helper lemmas for the five new free functions (§3), each action (§4), the
disjunctive action (§5), the `LevelCorrect` invariant (§6), saturation soundness (§7),
`Init` (§8), `check_axioms`/`check_invariants` correspondence (§9), coverage (§10).

> **Scope.** Safety/refinement only, transferred from `t1/proofs.md`'s own scope note.
> No liveness claim is made or needed beyond what `t1/proofs.md` already establishes.

All section/definition references without a file prefix are to `T2.v`; `Dn`/`D-Name`
references are to `implementation.md`'s decision register; `α`/`Ln` (unprefixed) refer to
`t1/proofs.md`'s state mapping and lemmas.

---

## 1. Parameter mapping

Unchanged from `t1/proofs.md` §1: `T2.v` introduces no abstract parameters, so the proof
is generic over the same `P: Params` for which `t1::model::check_axioms::<P>()` succeeds,
instantiating `T1.v`'s parameters exactly as `t1/proofs.md` §1 states. There is nothing to
add here.

---

## 2. State mapping α₂

```
α₂(rs2) = {| s1                := α(rs2.s1)
          ;  score             := rs2.score as ℕ
          ;  level              := rs2.level as ℕ
          ;  combo               := rs2.combo as ℕ
          ;  perfectClear         := rs2.perfect_clear
          ;  totalClearedLines     := rs2.total_cleared_lines as ℕ
          |}
```

**Totality and well-definedness.** `α` is total on every `Machine<P>` (`t1/proofs.md`
§2.2). `rs2.score/level/combo/total_cleared_lines as ℕ` require the respective field to
be `≥ 0`: trivially true, since all four are `u64` — a Rust type with no negative values
to exclude, unlike `t1/proofs.md`'s `cleared_lines: i64` case, which needed an explicit
non-negativity argument. So `α₂` is total on every well-typed `t2::model::Machine<P>`
value, not merely on reachable ones — matching `t1/proofs.md`'s totality claim for `α`,
with a strictly simpler argument for the four new numeric fields.

**Homomorphism condition 1** (α₂ sends initial states to initial states) is §8's `Init`
correspondence. **Condition 2** (the commuting square) is discharged action-by-action in
§4–§5, reusing `t1/proofs.md`'s own condition-2 discharge for the `s1` component of every
action (skill §7.1's transfer argument).

---

## 3. Helper lemmas

One lemma per new free function (`implementation.md` §5). Each is a direct case-by-case
transcription of its `T2.v` definition with no loop, no array read, and no guard, so each
proof is immediate by unfolding both sides on every argument value — unlike `t1/proofs.md`
§3's grid lemmas, which needed an explicit "loop visits exactly this domain" argument.

### L-line_clear_points
`line_clear_points(cl, level) = LineClearPoints cl level` for all `cl, level: ℕ`.
*Proof.* Both sides `match`/`match` on `cl` with the same four arms
(`0 → 0; 1 → 100·level; 2 → 300·level; 3 → 500·level; _ → 800·level`) verbatim. ∎

### L-combo_points
`combo_points(level, combo) = ComboPoints level combo`.
*Proof.* `combo > 0` (Rust `u64 > 0`) ⟺ `0 <? combo` (Rocq `ℕ`, same truth table); both
branches return `50 · combo · level` / `0` identically. ∎

### L-perfect_clear_points
`perfect_clear_points(pc, cl, level) = PerfectClearPoints pc cl level`.
*Proof.* `!pc` early-return `0` ⟺ `negb perfectClear` guard; the remaining `match` on `cl`
has the same five arms (`0,1,2,3,_`) with the same four nonzero multipliers
(`800,1200,1800,2000`) times `level`, verbatim. ∎

### L-points
`points(cl, level, combo, pc) = Points cl level combo pc`.
*Proof.* Immediate sum of L-line_clear_points, L-combo_points, L-perfect_clear_points —
`points`'s body is exactly the three-term sum `Points` is, in the same order, over the
same arguments. ∎

### L-empty_gridb
`empty_gridb::<P>(g) = true ⟺ EmptyGridb ⟦g⟧₍₀,₀₎ = true`, for `g: Vec<Vec<Option<P::Piece>>>`.
*Proof.* `EmptyGridb g' = forallbz2 (λ y x, negb (occ (L g' y x))) (seqz 0 (H g')) (seqz 0
(W g'))` — every cell of `g'`'s own box is unoccupied. `⟦g⟧`'s box is `(g.len(),
g[0].len())` (L-dims), and its content at `(y,x)` in that box is `occ(g[y][x])` (§2.1 of
`t1/proofs.md`). `empty_gridb`'s `g.iter().all(|row| row.iter().all(|c| !c.occ()))` visits
exactly that same index range in the same row-major order and tests the same negated `occ`
predicate at each cell — the two universally-quantified statements have the identical
domain and the identical per-cell test, so they agree. ∎

---

## 4. Actions

### 4.1 `move_piece(&mut self, dy, dx) -> bool` ≙ `MovePiece (dy,dx)` — full use (skill §7.1)

`self.s1.move_piece(dy, dx)` is exactly `t1::model::Machine::move_piece`, already proved
(`t1/proofs.md` §4.1) to commute with `α` and `T1.MovePiece`. Since `t2::model::Machine::
move_piece` does nothing besides forward to it and return its result, and `T2.MovePiece`
is defined as `UpdateS1 (T1.MovePiece dyx (s1 s)) s` — leaving `score`/`level`/`combo`/
`perfectClear`/`totalClearedLines` unchanged on the Rocq side exactly as the Rust method
leaves them unwritten — `α₂` commutes with this step by direct composition with
`t1/proofs.md` §4.1: the `s1` component tracks via the cited lemma, and every other `α₂`
field is unchanged on both sides by inspection (no assignment to any T2 field appears in
the method body). No new argument is needed beyond "the delegated call was made with
identical arguments and its result was returned unmodified." ∎

### 4.2 `rotate_piece(&mut self, cw) -> bool` ≙ `RotatePiece cw` — full use

Identical shape to §4.1, composing with `t1/proofs.md` §4.2 instead of §4.1: `self.s1.
rotate_piece(cw)` is forwarded and returned verbatim, and `T2.RotatePiece cw = UpdateS1
(T1.RotatePiece cw (s1 s)) s` leaves the five T2 fields unchanged on the Rocq side to
match. ∎

### 4.3 `fix_piece(&mut self, p_new) -> bool` ≙ `FixPiece p_new` — partial use, the only
non-trivial T2 action

**The `s1` half.** `let fired = self.s1.fix_piece(p_new);` is exactly `t1::model::Machine
::fix_piece`, proved in `t1/proofs.md` §4.3 to commute with `α` and `T1.FixPiece`: `fired
= false` corresponds exactly to `T1.FixPiece p_new (s1 s) = None`, and `fired = true`
corresponds to `T1.FixPiece p_new (s1 s) = Some s1'` with `α(self.s1) = s1'` after the
call. `T2.FixPiece` is `option_map (λ s1', {| … |}) (T1.FixPiece pNew (s1 s))` — so the
`None` case of the inner call must produce `None` on the T2 side too, and the `Some` case
must build the five T2 fields from that same `s1'`.

**`fired = false` (guard fails).** `t2::model::Machine::fix_piece` returns `false`
immediately, writing nothing — matching `option_map`'s behavior on `None`: the whole
`T2.FixPiece` call is `None`, i.e. a stutter, with `self` (hence `α₂(self)`) unchanged, as
required.

**`fired = true` (guard holds) — the five new fields.** Let `s1'` be `self.s1` *after* the
inner call (already shown `α(s1') = s1'` in Rocq's naming, per the previous paragraph).
Each subsequent local/field matches its `let`-binding in `T2.FixPiece` directly:

- `cleared_lines := self.s1.cleared_lines as u64`. By `t1/proofs.md` §2.2's `α` definition,
  `α(s1').(clearedLines) = self.s1.cleared_lines as ℕ` (non-negative, `t1/proofs.md` §2.2)
  — matching Rocq's `clearedLines := clearedLines s1'` read exactly, with no re-derivation
  (implementation.md §4-T2a).
- `combo2 := if cleared_lines == 0 { 0 } else { self.combo.saturating_add(1) }`. Below
  saturation (§7), `saturating_add(1) as ℕ = (combo s + 1) as ℕ`; matches Rocq's `combo' :=
  if clearedLines =? 0 then 0 else combo s + 1` cell-for-cell (`self.combo` is read before
  any T2 field is written this call, so it is `combo s`, the pre-state value).
- `perfect_clear2 := empty_gridb::<P>(&self.s1.mg)`. By L-empty_gridb and `α(s1').mg =
  ⟦self.s1.mg⟧` (`t1/proofs.md` §2.2), this equals `EmptyGridb (mg s1')` — Rocq's
  `perfectClear' := EmptyGridb (mg s1')` exactly.
- `pts := points(cleared_lines, self.level, combo2.saturating_sub(1), perfect_clear2)`.
  `self.level` is read here, **before** `self.level` is written later in this same call
  (the assignment `self.level = 1 + total2/10` is textually and temporally after) — so
  this is `level s`, the pre-state value, matching Rocq's `Points clearedLines (level s)
  (combo'-1) perfectClear'` exactly, with `combo2.saturating_sub(1)` matching `combo'-1`'s
  `nat`-subtraction floor-at-zero by L-points composed with the definition of
  `saturating_sub` (`a.saturating_sub(b) = max(0, a-b)` over `ℕ`, the same total function
  `nat` subtraction is).
- `total2 := self.total_cleared_lines.saturating_add(cleared_lines)`. Below saturation
  (§7), equals `(totalClearedLines s + clearedLines s1') as ℕ` — Rocq's
  `totalClearedLines' := totalClearedLines s + clearedLines`.

**Field-write order and no read-after-write hazard (skill §4b).** The five writes
(`self.combo`, `self.perfect_clear`, `self.score`, `self.total_cleared_lines`, `self.
level`) all happen after every local (`cleared_lines`, `combo2`, `perfect_clear2`, `pts`,
`total2`) has already been computed from pre-state field values — no write in this block
is read by a later computation in the same call. In particular `self.level`'s write is
last, so `pts`'s computation (which reads `self.level`) unconditionally sees the pre-state
value, matching Rocq's `let`-order (`score` computed from `level s`, `level` computed
afterward from `totalClearedLines'`) exactly. `self.score = self.score.saturating_add
(pts)` then matches `score := score s + Points …` (mod saturation, §7); `self.level = 1 +
total2/10` matches `level := 1 + totalClearedLines'/10` directly (Rust `/` on `u64` is
Rocq `nat`-division, no adjustment needed — implementation.md §4-T2c).

Every `α₂` field after this call therefore matches its `T2.FixPiece` counterpart:
`s1 := α(s1')`, and the five new fields as derived above. `α₂` commutes with the step
whenever the guard holds; guard-fails is a stutter as shown above. ∎

### 4.4 `fall_step` — see §5 (disjunctive action).

---

## 5. Disjunctive action: `fall_step(&mut self, p_new) -> bool` ≙ `FallStep p_new`

Rocq: `match MovePiece (-1,0) s with Some s' => Some s' | None => FixPiece pNew s end`.
Rust: `if self.move_piece(-1, 0) { return true; } self.fix_piece(p_new)`.

**Mutual exclusivity**, inherited directly from `t1/proofs.md` §5: `self.s1.move_piece
(-1,0)`'s guard and `self.s1.fix_piece(·)`'s guard are `t1::model`'s own, unchanged by T2
— T2 adds no new guard to either. So exactly the same case split `t1/proofs.md` §5
establishes for `t1::model::Machine::fall_step` applies here, one level up: if `self.
move_piece(-1,0)` (§4.1, itself calling `self.s1.move_piece(-1,0)`) returns `true`, T2's
`fall_step` returns `true` immediately, matching Rocq's `Some s'` branch via §4.1's
already-proved commutation; otherwise it falls through to `self.fix_piece(p_new)` (§4.3),
matching Rocq's `None` branch falling through to `FixPiece pNew s` exactly. No new argument
is needed beyond composing §4.1 and §4.3 with `t1/proofs.md`'s own mutual-exclusivity
lemma. ∎

---

## 6. `LevelCorrect` preservation

`LevelCorrect s ≡ level s = 1 + totalClearedLines s / 10`. Not covered by `T2RefinesT1`
(that mapping only constrains the `s1` projection), so it is an independent obligation.

- **At `Init`** (§8): `level := 1`, `totalClearedLines := 0`, and `1 = 1 + 0/10` — holds.
- **`move_piece`/`rotate_piece`** (§4.1–4.2): neither `level` nor `total_cleared_lines` is
  written, so if `LevelCorrect` held before the call it holds after, trivially.
- **`fix_piece`** (§4.3, guard-fails case): no field written, trivially preserved.
- **`fix_piece`** (guard-holds case): `self.level` is written *last*, as `1 + total2 / 10`,
  from the *same* `total2` just written to `self.total_cleared_lines` — so `self.level ==
  1 + self.total_cleared_lines / 10` holds immediately after the call by construction, not
  by an inductive argument on the pre-state's `LevelCorrect`.
- **`fall_step`** (§5): each branch is one of the above.

`LevelCorrect` therefore holds after every reachable step, by induction on the trace
length with `Init` as the base case — matching `T2.v`'s `LevelCorrect`, one conjunct of
`Correct` alongside `T1.Correct (s1 s)` (which `t1/proofs.md` already establishes for the
`s1` component). In particular `level s ≥ 1` always (immediate from `1 + _/10 ≥ 1`),
discharging `ScoreRisesOnClear`'s `Hc : Correct s` premise wherever it's needed. ∎

---

## 7. Saturation soundness

`score`, `combo`, and `total_cleared_lines` are unbounded in `T2.v`: no `Axiom` or
invariant caps them, and a sufficiently long game exceeds any fixed bound — so no
machine-checked "never saturates" claim is made. `model.rs` instead applies
`u64::saturating_add` at each of their three increment sites (§4.3).

- **Representation safety.** `saturating_add` is a total, non-panicking, non-wrapping
  standard-library primitive: for all `a, b: u64`, `a.saturating_add(b) = min(a+b,
  u64::MAX)` computed without ever forming an out-of-range intermediate value. Every
  accumulator field is therefore a valid `u64` at every step, with no argument beyond the
  primitive's own specification.
- **Monotonicity.** `a.saturating_add(b) ≥ a` for all `b: u64` (`min(a+b, u64::MAX) ≥ a`
  since `a+b ≥ a` and `u64::MAX ≥ a`). So each of `score`, `combo`, `total_cleared_lines`
  is non-decreasing across every `fix_piece` call, and unchanged across `move_piece`/
  `rotate_piece` (§4.1–4.2) — giving `NonDecreasingScore` unconditionally. `NonDecreasingLevel`
  follows since `level = 1 + total_cleared_lines/10` is monotone in `total_cleared_lines`
  (integer division is monotone in its dividend) and `total_cleared_lines` is
  non-decreasing.
- **`ScoreRisesOnClear`.** Holds exactly as in the uncapped model until `score` reaches
  `u64::MAX`, past which `saturating_add` can no longer strictly increase it — the one
  place saturation weakens `T2.v`'s abstract guarantee, reachable only after roughly
  1.8·10¹⁹ accumulated points, i.e. never in a real playthrough. Below that threshold
  (`self.score < u64::MAX`) `saturating_add(pts)` with `pts > 0` is ordinary addition,
  strictly increasing — `pts > 0` whenever `cleared_lines > 0` (`line_clear_points`'s
  `0 ↦ 0` arm is the only zero case, and every other arm is a positive multiple of
  `level ≥ 1`, §6), matching `ScoreRisesOnClear`'s hypothesis `0 < clearedLines (s1 s')`.
- **`level`'s range needs no clamp of its own.** `total_cleared_lines ≤ u64::MAX` gives
  `level = 1 + total_cleared_lines/10 ≤ 1 + u64::MAX/10`, itself far inside `u64`'s range
  — the bound `§4-T2e` of `implementation.md` relies on to justify capping the three
  accumulators only.

This is a documented, sound divergence from `T2.v` (which has no cap): `model.rs` refines
`T2.v` exactly up to the saturation point and conservatively (monotonically) beyond it. ∎

---

## 8. `Machine::new(p0, piece_source)` ≙ `Init p`

`self.s1 := T1Machine::new(p0, piece_source)`; by `t1/proofs.md` §9, `α(self.s1) = T1.Init
p0`. The four remaining fields are written literal constants: `score := 0`, `level := 1`,
`combo := 0`, `perfect_clear := false`, `total_cleared_lines := 0` — matching `T2.v`'s
`Init p`'s `score := 0; level := 1; combo := 0; perfectClear := false; totalClearedLines :=
0` field-for-field, with no computation and hence no ordering hazard. So `α₂(Machine::new
(p0, ·)) = T2.Init p0` for every `p0` a caller supplies from `P::piece_all()`, matching
Rocq's `∀ p : Piece, Init p` — homomorphism condition 1 (§2). ∎

---

## 9. `check_axioms`/`check_invariants` correspondence

**`check_axioms`.** T2 emits none: every call site uses `t1::model::check_axioms::<P>()`
directly (`implementation.md` §7). Since `T2.v` states no `Axiom` block beyond `T1.v`'s
own, this is not a gap — there is nothing for a T2-specific `check_axioms` to check, and
`t1/proofs.md` §11's correspondence table already covers every conjunct that exists.

**`check_invariants`.** `t2::model::check_invariants` (i) calls `t1::model::check_invariants
(&s.s1)`, which by `t1/proofs.md` §6/§11 checks exactly `T1.Correct (s1 s)`'s five
conjuncts, and (ii) asserts `s.level == 1 + s.total_cleared_lines / 10`, exactly
`LevelCorrect s` (§6 above). Together these are exactly `T2.Correct s`'s two conjuncts
(`T1.Correct (s1 s) ∧ LevelCorrect s`) — no more, no fewer. ∎

---

## 10. Coverage

Every `T2.v` `Definition`/`Record` name introduced by T2 (i.e. everything beyond what
`t1/proofs.md` §12 already covers for `T1.v`) is accounted for above or in
`implementation.md`'s §3 naming map: `State`/`s1`/`score`/`level`/`combo`/`perfectClear`/
`totalClearedLines` (§2), `Init` (§8), `Event`/`Next` (§4–§5, mirroring `T1.v`'s own
`Next` shape via `t1/proofs.md`), `UpdateS1` (§4.1–4.2, not emitted, realized as
"delegate and leave the rest untouched"), `LineClearPoints`/`ComboPoints`/
`PerfectClearPoints`/`Points`/`EmptyGridb` (§3), `FixPiece`/`FallStep` (§4.3/§5),
`LevelCorrect`/`Correct` (§6/§9), `NonDecreasingScore`/`NonDecreasingLevel`/
`ScoreRisesOnClear`/`CorrectStep` (§6–§7), `fₑ`/`fₛ`/`T2RefinesT1` (used throughout as the
justification for reusing `t1/proofs.md`'s action lemmas, never emitted as Rust — §1–§2).
`T2AllowsAllT1`, `RunT1`, `RunT2`, `gₑ` are proof-only constructions with no `model.rs`
counterpart to translate (`implementation.md` states no naming-map entry for them because
none is needed: they characterize `T2.v`'s relationship to `T1.v` in the Rocq development
itself, not a runtime behavior). No `model.rs` behavior relies on anything not accounted
for above or, transitively, in `t1/proofs.md`. ∎
