# proofs.md — refinement proof: `model.rs` ⊑ `T3.v`

Follows the `rocq-to-rust` skill's `proofs.md` skeleton (skill §6), specialized by §7's
wrapping-module rules: this file states only the **delta** over `t2/proofs.md`, reusing
`t2/model.rs ⊨ T2.v` (hence, transitively, `t1/model.rs ⊨ T1.v`) in full for every
`s2`-shaped fact. Order: scope (this note), parameter/state mapping (§1–§2), each
`Event2` action (§3), the disjunctive action (§4), `hold_piece` argued fresh (§5), the two
new state invariants and `HoldMonotone` (§6), `Init` (§7), `check_axioms`/
`check_invariants` correspondence (§8), coverage (§9).

> **Scope, and what is different from every prior model in this tower.** `T3.v`'s own
> `T3RefinesT2` quantifies only over `Event2 e2` (`T3.v`'s `Refinement` section, restated
> in `implementation.md` §1) — `Hold` carries **no** refinement claim to `T2.v`/`T1.v` at
> all. This is not a codegen simplification; it is what the model states: "T3 does not
> refine T2" (`T3.v`'s own design note), only "T3 minus holding a piece" does. Consequently
> §3–§4 below reuse `t2/proofs.md` by direct composition, exactly as `t2/proofs.md` reused
> `t1/proofs.md`, but §5 (`hold_piece`) is a **complete, independent** safety argument
> with no lemma to inherit — the skill §7.1 "no use" case, carried through in full rather
> than by transfer.

All section/definition references without a file prefix are to `T3.v`; `Dn`/`D-Name`
references are to `implementation.md`'s decision register; unprefixed `α`/`Ln` refer to
`t1/proofs.md`; `α₂`/T2-prefixed `Ln` refer to `t2/proofs.md`.

---

## 1. Parameter mapping

Unchanged from `t2/proofs.md` §1: `T3.v` introduces no abstract parameters (its own "No
new parameter" comment), so the proof is generic over the same `P: Params` for which
`t1::model::check_axioms::<P>()` succeeds. Nothing to add here.

---

## 2. State mapping α₃

```
α₃(rs3) = {| s2      := α₂(rs3.s2)
          ;  hold     := rs3.hold.map(|p| p)   (* Option<P::Piece> ↦ option Piece, identity on the payload *)
          ;  swapped  := rs3.swapped
          |}
```

**Totality and well-definedness.** `α₂` is total on every `t2::model::Machine<P>` value
(`t2/proofs.md` §2). `rs3.hold: Option<P::Piece>` maps to `option Piece` by the identity
coercion on the payload (no numeric cast, no non-negativity side-condition — unlike
`α₂`'s `u64 → ℕ` fields, `Option<P::Piece>` has no representable value `option Piece`
cannot express); `rs3.swapped: bool` maps to `bool` directly. So `α₃` is total on every
well-typed `t3::model::Machine<P>` value, with a strictly simpler argument than either
`α`'s or `α₂`'s numeric fields needed.

**Homomorphism condition 1** (α₃ sends initial states to initial states) is §7's `Init`
correspondence. **Condition 2** (the commuting square) is discharged **only for
`Event2`-tagged transitions** in §3–§4, reusing `t2/proofs.md`'s own condition-2 discharge
for the `s2` component of each — matching `T3RefinesT2`'s own restriction to `Event2 e2`
(the scope note above). `Hold` is outside condition 2's scope by construction of `T3.v`
itself; §5 instead establishes `T3.Correct` preservation directly (`CorrectStep`'s own
target, not `T3RefinesT2`'s).

---

## 3. `Event2` actions

### 3.1 `move_piece(&mut self, dy, dx) -> bool` ≙ `MovePiece (dy,dx)` — full use (skill §7.1)

`self.s2.move_piece(dy, dx)` is exactly `t2::model::Machine::move_piece`, already proved
(`t2/proofs.md` §4.1) to commute with `α₂` and `T2.MovePiece`. `T3.MovePiece dyx s =
option_map (UnchangedT3Part s) (T2.MovePiece dyx (s2 s))` — `UnchangedT3Part` copies
`hold`/`swapped` from the pre-state `s` unchanged. Since `t3::model::Machine::move_piece`
forwards to the T2 call and returns its result with no write to `self.hold`/`self.swapped`
anywhere in the method body, `α₃` commutes with this step by direct composition with
`t2/proofs.md` §4.1: the `s2` component tracks via the cited lemma, and `hold`/`swapped`
are unchanged on both sides by inspection. No new argument beyond "the delegated call was
made with identical arguments and its result returned unmodified, and the two T3-only
fields are literally untouched by this method." ∎

### 3.2 `rotate_piece(&mut self, cw) -> bool` ≙ `RotatePiece cw` — full use

Identical shape to §3.1, composing with `t2/proofs.md` §4.2 instead of §4.1:
`self.s2.rotate_piece(cw)` is forwarded and returned verbatim; `T3.RotatePiece cw =
option_map (UnchangedT3Part s) (T2.RotatePiece cw (s2 s))` leaves `hold`/`swapped`
unchanged on the Rocq side to match. ∎

### 3.3 `fix_piece(&mut self, p_new) -> bool` ≙ `FixPiece p_new` — partial use

**The `s2` half.** `let fired = self.s2.fix_piece(p_new);` is exactly
`t2::model::Machine::fix_piece`, proved in `t2/proofs.md` §4.3 to commute with `α₂` and
`T2.FixPiece`: `fired = false` corresponds to `T2.FixPiece p_new (s2 s) = None`, and
`fired = true` corresponds to `T2.FixPiece p_new (s2 s) = Some s2'` with `α₂(self.s2) =
s2'` after the call. `T3.FixPiece pNew s = option_map (λ s2', {| s2 := s2'; swapped :=
false; hold := hold s |}) (T2.FixPiece pNew (s2 s))`.

**`fired = false` (guard fails).** `t3::model::Machine::fix_piece` returns `false`
immediately, writing nothing — matching `option_map`'s behavior on `None`: the whole
`T3.FixPiece` call is `None`, a stutter, with `self` (hence `α₃(self)`) unchanged, as
required.

**`fired = true` (guard holds).** `self.swapped = false` is the only new write —
`self.hold` is left untouched — matching `T3.FixPiece`'s explicit `swapped := false;
hold := hold s` field literals exactly, with no computation and hence no ordering hazard
beyond "write `swapped` after the inner call returns" (already satisfied: the inner call
happens first, unconditionally, before the `swapped` write). Combined with the `s2` half
above, `α₃(self)` after the call equals `{| s2 := s2'; hold := hold s; swapped := false |}`
= `T3.FixPiece p_new s`, as required. ∎

### 3.4 `fall_step` — see §4 (disjunctive action).

---

## 4. Disjunctive action: `fall_step(&mut self, p_new) -> bool` ≙ `FallStep p_new`

Rocq: `match MovePiece (-1,0) s with Some s' => Some s' | None => FixPiece pNew s end`
(`T3.v`, identical shape to `T2.v`'s own `FallStep`). Rust: `if self.move_piece(-1, 0) {
return true; } self.fix_piece(p_new)`.

**Mutual exclusivity**, inherited by composition through `t2/proofs.md` §5 and, beneath
that, `t1/proofs.md` §5: `self.move_piece(-1, 0)` (§3.1, itself calling
`self.s2.move_piece(-1,0)`, itself calling `self.s2.s1.move_piece(-1,0)`) and
`self.fix_piece(·)` (§3.3, itself calling `self.s2.fix_piece(·)`, itself calling
`self.s2.s1.fix_piece(·)`) share their guard at the innermost `t1::model::Machine` layer —
T2 and T3 each add no new guard to either. So the same case split `t1/proofs.md` §5
establishes applies here, two levels up: if `self.move_piece(-1,0)` returns `true`, T3's
`fall_step` returns `true` immediately, matching Rocq's `Some s'` branch via §3.1's
already-proved commutation; otherwise it falls through to `self.fix_piece(p_new)` (§3.3),
matching Rocq's `None` branch falling through to `FixPiece pNew s` exactly. ∎

---

## 5. `hold_piece(&mut self, p_new) -> bool` ≙ `HoldPiece p_new` — no use, fresh argument

No `T2`/`T1` action is called (`new_piece_state` is a free function, not an action — using
it is not a "use" in skill §7.1's sense). This section is a complete safety argument, not
a transfer.

### 5.1 Guard

```rust
if !(!self.s2.s1.gameover && !self.swapped) { return false; }
```
`self.s2.s1.gameover` and `self.swapped` are both native T3 reads — the former is exactly
`T3.v`'s own `gameover` helper (`gameover s := T1.gameover (s1 (s2 s))`),
the latter a plain field. The guard is the literal negation-conjunction of `T3.v`'s `!
gameover s && ! swapped s` (`HoldPiece`'s own guard). Guard fails → `return false`, no
field touched → matches `None`, a stutter.

### 5.2 `p2` — the new current piece

```rust
let p2 = self.hold.unwrap_or(p_new);
```
`Option::unwrap_or` on `Some(x)` yields `x`, on `None` yields the argument — exactly
`T3.v`'s `match hold s with Some p => p | None => pNew end`. `p2: P::Piece` in both
branches (`self.hold: Option<P::Piece>`, `p_new: P::Piece`), so `p2 ∈ Piece` unconditionally
— needed below for the spawn-containment argument to apply.

### 5.3 Field-update ordering (skill §4b) and `new_piece_state`

```rust
let old_p = self.s2.s1.p;                              // 1
new_piece_state::<P>(p2, &mut self.s2.s1);              // 2
self.hold = Some(old_p);                                // 3
self.swapped = true;                                    // 4
```

`T3.v`'s right-hand side is `{| s2 := T2.UnchangedT2Part s2_ (T1.NewPieceState p2 (s1
s2_)); hold := Some (p s); swapped := true |}`, where `s2_ = s2 s` and `p s = T1.p (s1
(s2 s))` — the **pre-state** current piece, read *before* `NewPieceState` is applied.

Step 1 captures exactly that pre-state value: `old_p := self.s2.s1.p` is read before any
mutation in this call. Step 2 then calls `new_piece_state::<P>(p2, &mut self.s2.s1)`,
which (`t1::model`'s own definition, cited verbatim in `t1/proofs.md` §10's
`L-new_piece_state`) sets `s2.s1.p/py/px/pr := p2, P::initial_y(p2), P::initial_x(p2), 0`
and leaves `mg/gameover/cleared_lines` untouched — a direct field-for-field match to
`NewPieceState p2 (s1 s2_)`'s own record update (`p := p2; pyx := InitialYX p2; pr := 0`,
rest from `s1 s2_`), already proved total and unconditionally α-commuting by
`L-new_piece_state`.

Because `new_piece_state` mutates `self.s2.s1` **in place**, step 1 must precede step 2 —
had the read been placed after, it would observe `p2`, not the pre-state `p`, silently
mismatching `T3.v`'s `p s` read. This is the one hazard skill §4b requires flagging, and
it is the entire content of `implementation.md` §4-T3e's ordering note.

`T2.UnchangedT2Part s2_ (...)` — the outer wrapper in `T3.v`'s RHS — sets the new `s2`'s
`s1` field to the given argument and copies every other T2 field (`score`, `level`,
`combo`, `perfectClear`, `totalClearedLines`) from `s2_` unchanged. `t3::model::hold_piece`
realizes this by *only* mutating `self.s2.s1` (step 2) and never writing
`self.s2.score`/`level`/`combo`/`perfect_clear`/`total_cleared_lines` anywhere in the
method body — the absence of an assignment is definitionally `UnchangedT2Part`'s "rest
from `s2_`" clause, needing no further argument.

Step 3 (`self.hold = Some(old_p)`) matches `hold := Some (p s)` directly, using the value
captured in step 1. Step 4 (`self.swapped = true`) matches `swapped := true` directly.
Every subsequent read in this call (there are none past step 4) sees only
already-finalized values, so no field is read after being overwritten by a later step —
`α₃(self)` after the call equals `T3.HoldPiece`'s RHS field-for-field.

### 5.4 `T1.Correct (s1 (s2 s))` preservation

`new_piece_state` touches only `p, py, px, pr` (§5.3, `t1/proofs.md` §10). Checking each
of `T1.v`'s five `Correct` conjuncts (`t1/proofs.md` §6/§11) against that fact:

- **`TypeOK`** — `mg`'s shape/content and `pr ∈ [0,3]` are the only conjuncts touching a
  written field; `pr := 0 ∈ [0,3]` trivially, `mg` is untouched. Holds.
- **`Gameover`** — `gameover ⟺ ForbiddenGrid ∩ mg ⊈ ∅`; both `gameover` and `mg` are
  untouched by `new_piece_state`, so if the pre-state satisfied `Gameover`, the post-state
  does too, trivially. (And by §5.1's guard, the pre-state has `gameover = false`, so this
  is the vacuous side of the biconditional in the reachable case, but the argument holds
  unconditionally regardless.)
- **`NoFullLine`** — a pure `mg` property; `mg` untouched. Holds trivially.
- **`PieceOccupiedInsideBounds`** — `(RotGrid p2 0 ⊕ InitialYX p2) ⊆ Full mg`, i.e. the new
  piece's `r=0` grid at its spawn position lies inside `mg`'s box. This is exactly
  `AxiomsRotGrid`'s own spawn-containment conjunct, `(RotGrid p 0 ⊕ InitialYX p) ⊆
  ForbiddenGrid`, stated `∀ p : Piece` — hence applying to `p2` regardless of which piece
  it turns out to be (§5.2's `p2 ∈ Piece` fact) — composed with `AxiomsForbiddenGrid`'s
  `Full ForbiddenGrid ⊆ Full InitialMainGrid` and `TypeOK`'s `HW mg = HW InitialMainGrid`.
  This is the **identical** composition `t1/proofs.md` §9 (`Machine::new`) and
  `t1/proofs.md` §4.3 (`fix_piece`'s respawn) already use for their own spawns — re-invoked
  here for `hold_piece`'s spawn, not re-derived. `check_axioms::<P>()`'s own
  `AxiomsRotGrid`/`AxiomsForbiddenGrid` assertions (`t1/proofs.md` §11) are exactly the
  runtime witnesses this composition needs, and they are checked once, before any
  `Machine<P>` of this `P` is constructed (§7 of `implementation.md`, inherited).
- **`PieceOnFreeBlocks`** — `!gameover → (RotGrid p2 0 ⊕ InitialYX p2) ∩ mg ⊆ ∅`. Same
  spawn-position fact as above, now for the intersection-with-content conjunct rather than
  the location-only one; `AxiomsRotGrid`'s spawn conjunct together with `mg`'s content
  being `⊆ ForbiddenGrid`'s complement in the reachable region gives this exactly as
  `t1/proofs.md`'s own `Init`/`fix_piece` spawn arguments do — no new lemma, same
  composition, applied to `p2`.

### 5.5 `LevelCorrect (s2 s)` preservation

Trivial: `score`/`level`/`combo`/`perfect_clear`/`total_cleared_lines` are untouched by
`hold_piece` (§5.3's observation that only `self.s2.s1` is written), so both sides of
`LevelCorrect`'s equation (`t2/proofs.md` §6) are literally unchanged by this call. If
`LevelCorrect` held before, it holds after, with no computation needed.

### 5.6 Cap/overflow soundness — not applicable

`hold_piece` introduces no arithmetic and touches none of the three saturating
accumulators (`score`, `combo`, `total_cleared_lines`, `t2/proofs.md` §7) — no new
obligation beyond what `t2/proofs.md` §7 already covers for the paths that *do* touch
them (`fix_piece`, unaffected by T3).

---

## 6. The two new state invariants and `HoldMonotone`

### 6.1 `SwappedImplyHoldSome` — `swapped s = true → hold s ≠ None`

Case analysis over all five T3 transitions:
- **`Hold`** (§5.3, guard holds): sets `hold := Some(old_p)` and `swapped := true` in the
  same call — `hold` is `Some(_)` exactly when `swapped` is newly `true`, satisfying the
  implication directly by construction, not by an inductive appeal to the pre-state.
- **`Move`/`Rotate`** (§3.1–3.2): both fields untouched — if the pre-state satisfied the
  implication, the post-state does too, trivially.
- **`Fix`** (§3.3, guard holds): `swapped := false` — the implication's antecedent is
  false in the post-state, so it holds vacuously regardless of `hold`.
- **Any guard-fails case**: no field written, trivially preserved.

By induction on trace length (base case: `Init`, §7, `swapped = false` — vacuously true),
`SwappedImplyHoldSome` holds in every reachable state. ∎

### 6.2 `GameoverImplyNotSwapped` — `gameover s = true → swapped s = false`

- **`Hold`**: guarded by `!self.s2.s1.gameover` (§5.1) — `gameover` is `false` in the
  pre-state, and `new_piece_state` leaves `gameover` untouched (§5.4's `Gameover` case),
  so `gameover` is still `false` in the post-state. The implication's antecedent is false,
  so it holds vacuously — `gameover` cannot newly become `true` on this branch at all.
- **`Move`/`Rotate`** (§3.1–3.2): `t1::model::Machine::move_piece`/`rotate_piece`'s own
  guards require `!gameover` to fire (`t1/proofs.md` §4.1–4.2), and neither writes
  `gameover` to `true` when they do fire (only `fix_piece` ever sets `gameover`,
  `t1/proofs.md` §4.3); `swapped` is untouched by either T3 method. If `gameover` was
  `false` before (required for the call to fire at all) it stays `false` after, so the
  antecedent stays false.
- **`Fix`** (§3.3, guard holds): `swapped := false` — the implication's consequent is true
  unconditionally in the post-state, satisfying it regardless of the new `gameover` value.
- **Any guard-fails case**: no field written, trivially preserved.

By the same induction as §6.1 (base case: `Init`, `gameover` may be `true` only if the
instance's `InitialMainGrid ∩ ForbiddenGrid ≠ ∅`, and `swapped = false` unconditionally at
`Init` — the implication holds regardless), `GameoverImplyNotSwapped` holds in every
reachable state. ∎

### 6.3 `HoldMonotone s s' : hold s ≠ None → Next e s = Some s' → hold s' ≠ None`

`hold` is written only by `hold_piece` (§5.3, step 3: `self.hold = Some(old_p)`), always
to `Some(_)` — never to `None` — and every other T3 method (`move_piece`, `rotate_piece`,
`fix_piece`, and hence `fall_step`) leaves `self.hold` untouched (§3.1–3.3). So for any
transition `e`: either `hold` is unwritten (its pre-state value, `≠ None` by hypothesis,
carries through unchanged) or it is written by `hold_piece` to `Some(_)` (trivially `≠
None`). Immediate case split, no induction needed beyond this single-step property (which
is exactly what `HoldMonotone`, a step invariant rather than a state invariant, asks
for). ∎

---

## 7. `Machine::new(p0, piece_source)` ≙ `Init p0`

`self.s2 := T2Machine::new(p0, piece_source)`; by `t2/proofs.md` §8, `α₂(self.s2) =
T2.Init p0`. The two remaining fields are written literal constants: `hold := None`,
`swapped := false` — matching `T3.v`'s `Init p`'s `hold := None; swapped := false`
field-for-field, with no computation and hence no ordering hazard. So `α₃(Machine::new(p0,
·)) = T3.Init p0` for every `p0` a caller supplies from `P::piece_all()`, matching Rocq's
`∀ p : Piece, Init p` — homomorphism condition 1 (§2). ∎

---

## 8. `check_axioms`/`check_invariants` correspondence

**`check_axioms`.** T3 emits none: every call site uses `t1::model::check_axioms::<P>()`
directly (`implementation.md` §7). `T3.v` states no `Axiom` block beyond `T1.v`'s own —
not a gap, `t1/proofs.md` §11's correspondence table already covers every conjunct that
exists, and §5.4 above shows `AxiomsRotGrid`/`AxiomsForbiddenGrid` (already checked there)
are exactly the facts `hold_piece`'s own spawn argument needs.

**`check_invariants`.** `t3::model::check_invariants` (i) calls
`t2::model::check_invariants(&s.s2)`, which by `t2/proofs.md` §9 checks exactly
`T2.Correct (s2 s)`'s conjuncts, and (ii)–(iii) assert `!swapped || hold.is_some()` and
`!gameover || !swapped` — exactly `SwappedImplyHoldSome s` and `GameoverImplyNotSwapped s`
(§6.1–6.2). Together these are exactly `T3.Correct s`'s three conjuncts (`T2.Correct (s2
s) ∧ SwappedImplyHoldSome s ∧ GameoverImplyNotSwapped s`) — no more, no fewer. ∎

---

## 9. Coverage

Every `T3.v` `Definition`/`Record` name introduced by T3 (i.e. everything beyond what
`t2/proofs.md` §10 already covers for `T2.v`) is accounted for above or in
`implementation.md`'s §3 naming map: `State`/`s2`/`hold`/`swapped` (§2), `gameover`/`p`
(helpers, not stored — §3, §5.1, §5.3, `implementation.md` §4-T3f), `score`/`level`/
`clearedLines` (T3-level read-through helpers, not emitted, `implementation.md` §3),
`Init` (§7), `Event`/`Next`/`NextT2Event`/`Event2` (§3–§5, mirroring `T1.v`'s/`T2.v`'s own
`Next` shape), `UnchangedT3Part` (§3.1–3.2, not emitted, realized as "delegate and leave
`hold`/`swapped` untouched"), `MovePiece`/`RotatePiece`/`FixPiece`/`FallStep`/`HoldPiece`
(§3–§5), `SwappedImplyHoldSome`/`GameoverImplyNotSwapped`/`Correct` (§6/§8),
`HoldMonotone`/`CorrectStep` (§6.3), `fₑ`/`fₛ`/`T3RefinesT2` (used throughout §3–§4 as the
justification for reusing `t2/proofs.md`'s action lemmas on `Event2` transitions only —
never emitted as Rust, and explicitly **not** invoked for `Hold`, per the scope note
above), `T3AllowsAllT2`/`RunT2`/`RunT3` (proof-only constructions with no `model.rs`
counterpart — they characterize `T3.v`'s relationship to `T2.v` in the Rocq development
itself, not a runtime behavior; `implementation.md` states no naming-map entry for them
because none is needed), `CorrectWithoutGameover`/`perfectClear` (helpers, `T3.v`'s own
thin wrappers around the `s2`-projected versions, no independent Rust counterpart needed
beyond what `t2::model`/`t1::model` already expose through `self.s2`). No `model.rs`
behavior relies on anything not accounted for above or, transitively, in `t2/proofs.md`
and `t1/proofs.md`. ∎
