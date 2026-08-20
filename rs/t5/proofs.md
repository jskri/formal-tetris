# proofs.md — refinement proof: `model.rs` ⊑ `T5.v`

Follows the `rocq-to-rust` skill's `proofs.md` skeleton (skill §6), specialized by §7's
wrapping-module rules: this file states only the **delta** over `t4/proofs.md`, reusing
`t4/model.rs ⊨ T4.v` (hence, transitively, `t3/model.rs ⊨ T3.v`, `t2/model.rs ⊨ T2.v`,
`t1/model.rs ⊨ T1.v`) in full for every `s4`-shaped fact. Order: scope (this note),
parameter/state mapping (§1–§2), each full-use action (§3), the disjunctive action (§4),
`drop_piece` argued as the representative no-use-then-full-use case (§5), the new invariant
(§6), `Init` (§7), `check_axioms`/`check_invariants` correspondence (§8), coverage (§9).

> **Scope.** `Drop` has no refinement claim in `T5.v` itself: `T5.v`'s own `Refinement`
> section states `fₑ : T4.Event → T4.Event := id` and `fₛ : T5.State → T4.State := s4`, and
> `T4RefinesT5`'s second conjunct is quantified over `NextT4Event`, **not** `Next` — i.e. over
> `Event4`-tagged transitions only. `Drop` is structurally excluded from the refinement claim,
> the same shape `t3/proofs.md` gives T3's own exclusion of `Hold` — not a gap this proof
> needs to work around, a fact this proof needs to state and then respect (§3–§5 below only
> ever invoke `T5.v`'s `NextT4Event` case, never `Drop`).
>
> As with every model in this tower, this is a **safety** argument only: `T4RefinesT5` has
> exactly two conjuncts (`Init` correspondence, `NextT4Event` step correspondence), no
> converse/completeness clause (Lynch & Vaandrager, *Information and Computation*
> 121(2):214–233, 1995, §3). Converse completeness is in any case false here for a second,
> independent reason beyond `Drop`'s exclusion: `t4/proofs.md`'s own scope note already
> establishes it false one layer down (`T3.FixPiece`'s unconstrained piece argument), and
> that non-completeness transfers unchanged through `fₛ = s4` — no new gap is introduced by
> T5, but none of T4's own is closed either.

All section/definition references without a file prefix are to `T5.v`; `Dn`/`D-Name`
references are to `implementation.md`'s decision register; `α`/unprefixed `Ln` refer to
`t1/proofs.md`; `α₂`/T2-prefixed `Ln` refer to `t2/proofs.md`; `α₃`/T3-prefixed `Ln` refer to
`t3/proofs.md`; `α₄`/T4-prefixed `Ln` refer to `t4/proofs.md`.

---

## 1. Parameter mapping

`T5.v` declares no `Parameter` of its own (confirmed by direct inspection of `T5.v` — no
`Parameter`/`Axiom` block anywhere in the file). The proof is generic over any `P:
t5::model::Params`, i.e. any `P: t4::model::Params` (`t5::model::Params: t4::model::Params`,
no new trait items, `implementation.md` §6.0) for which `t4::model::check_axioms::<P>()`
succeeds — exactly the same `P` `t4/proofs.md` §1 quantifies over.

---

## 2. State mapping α₅

```
α₅(rs) = {| s4 := α₄(rs.s4)
          ;  gy := rs.gy
          |}
```

`gy` maps directly — a plain `i64`/`ℤ` pair, no coercion, no bounded-structure encoding (skill
§2 doesn't apply here: `gy` is a scalar, not an array).

**Totality and well-definedness.** `α₄` is total on every `t4::model::Machine<P>` value
(`t4/proofs.md` §2). `rs.gy: i64` is always initialized for any `Machine<P>` reachable through
`Machine::new`/the six action methods (no `unsafe`, no partial construction anywhere in
`model.rs`), so `α₅` is total wherever `α₄` is.

**Homomorphism condition 1** is §7's `Init` correspondence. **Condition 2** (the commuting
square) is discharged only for `NextT4Event`-tagged transitions (§3–§5), matching
`T4RefinesT5`'s own restricted scope (the note above) — unlike `t4/proofs.md` §2's
unrestricted composition with `t3/proofs.md`, this file's restriction mirrors
`t3/proofs.md`'s own `Event2`-only composition with `t2/proofs.md`.

---

## 3. Full-use actions, plus one new obligation each

### 3.0 The shared `gy`-refresh obligation

Every one of `move_piece`/`rotate_piece`/`fix_piece`/`hold_piece` has the shape

```rust
let fired = self.s4.<action>(...);
if fired { self.update_shadow_y(); }
```

with `update_shadow_y(&mut self) { self.gy = shadow_y::<P>(&self.s4.s3.s2.s1); }`. Two facts,
established once here and cited by number in §3.1–§3.4:

**(i) `fired == false ⟹ self.gy` unchanged.** By inspection: the only write to `self.gy`
anywhere in `model.rs` is inside `update_shadow_y`, and every call site of it is guarded by
`if fired`. So the stuttering-step property `t1/proofs.md`–`t4/proofs.md` already establish
for `self.s4` (guard fails ⟹ zero mutation) extends verbatim to `self.gy`: on failure, the
entire call is a stutter at the T5 level, matching `T5.v`'s own `option_map (UpdateShadowY s)
(T4.<Action> ... (s4 s))` reaching its `None` case (`UpdateShadowY` is never applied).

**(ii) `fired == true ⟹ self.gy = shadow_y(post-state)`, definitionally.**
`update_shadow_y()` **is** the computation `ShadowY` denotes, called on `self.s4.s3.s2.s1`
*after* the delegated call has already mutated it — i.e. on the post-action state. This
matches `T5.v`'s `UpdateShadowY s s4' := {| s4 := s4'; gy := ShadowY s4' |}`, applied to the
same post-action `s4'` the delegated call produced, by construction (no intervening mutation
of `self.s4` between the delegated call and `update_shadow_y()`'s read of it).

`shadow_y`'s own correctness as a computation of `ShadowYImpl`/`ShadowY` — that the Rust loop
computes the same value as the Rocq `Fixpoint` for every reachable `s1` — is proved once,
independently of any action, in §6 below (`L-shadow_y`), and is imported by (ii) rather than
re-derived per call site.

### 3.1 `move_piece(&mut self, dy, dx) -> bool` ≙ `MovePiece (dy,dx)` — full use

`self.s4.move_piece(dy, dx)` is exactly `t4::model::Machine::move_piece`, already proved
(`t4/proofs.md` §3.1) to commute with `α₄` and `T4.MovePiece`. `T5.MovePiece dyx s =
option_map (UpdateShadowY s) (T4.MovePiece dyx (s4 s))`: the `s4` component tracks via the
cited lemma; the `gy` component tracks via §3.0(i)/(ii) applied to this call. ∎

### 3.2 `rotate_piece(&mut self, cw) -> bool` ≙ `RotatePiece cw` — full use

Identical shape to §3.1, composing with `t4/proofs.md` §3.2 instead of §3.1; `gy` via
§3.0(i)/(ii). ∎

### 3.3 `fix_piece(&mut self, bag_new) -> bool` ≙ `FixPiece bagNew` — full use

`self.s4.fix_piece(bag_new)` is exactly `t4::model::Machine::fix_piece`, proved (`t4/proofs.md`
§4) to commute with `α₄` and `T4.FixPiece`. `T5.FixPiece bagNew H s = option_map
(UpdateShadowY s) (T4.FixPiece bagNew H (s4 s))`: the `s4` component tracks via the cited
lemma (which already accounts for `bag`/`next` mutation being conditioned on success — no new
obligation here beyond what `t4/proofs.md` §4 established); `gy` via §3.0(i)/(ii). Note this
is a **full** use at the T5 level even though it was a **partial** use one layer down (T4
supplying the piece to T3) — the T5→T4 relationship for this action has no analogous new
guard or supplied argument of its own, only the `gy` refresh, which is exactly what "full use"
means at this layer (skill §7.1: classification is per use, not per action's history). ∎

### 3.4 `hold_piece(&mut self, bag_new) -> bool` ≙ `HoldPiece bagNew` — full use

Identical shape to §3.3, composing with `t4/proofs.md` §5 instead of §4; `gy` via
§3.0(i)/(ii). ∎

---

## 4. `fall_step(&mut self, bag_new) -> bool` ≙ `FallStep bagNew` — disjunctive

Rocq: `match MovePiece (-1,0) s with Some s' => Some s' | None => FixPiece bagNew H s end`
(`T5.v`, identical shape to every prior model's own `FallStep`). Rust:
```rust
if self.move_piece(-1, 0) { return true; }
self.fix_piece(bag_new)
```
**Mutual exclusivity**, inherited by composition through `t4/proofs.md` §4.1 and, beneath
that, `t3/proofs.md` §4, `t2/proofs.md` §5, `t1/proofs.md` §5: `self.move_piece(-1, 0)`
(§3.1) and `self.fix_piece(·)` (§3.3) share their guard at the innermost `t1::model::Machine`
layer — T2–T5 each add no new guard to either. So the same case split established three/four
layers down applies here: if `self.move_piece(-1,0)` returns `true`, `fall_step` returns
`true` immediately, matching Rocq's `Some s'` branch via §3.1's already-proved commutation
(`s4` **and** `gy` both, by §3.0); otherwise it falls through to `self.fix_piece(bag_new)`
(§3.3), matching Rocq's `None` branch falling through to `FixPiece bagNew H s` exactly. ∎

---

## 5. `drop_piece(&mut self, bag_new) -> bool` ≙ `DropPiece bagNew` — no-use relocation, full-use fix

`T5.v`: `DropPiece bagNew H s := FixPiece bagNew H (NewPieceYXState (gy s, px s) s)`. No T4 (or
lower) *action* appears in this definition before the piece is relocated —
`NewPieceYXState` is a state constructor (total, no guard), not an `Event`/`option`-returning
action — so the relocation step is a **no use** in skill §7.1's sense; the trailing
`FixPiece` call is the **full use** already covered by §3.3.

```rust
pub fn drop_piece(&mut self, bag_new: &[P::Piece]) -> bool {
    t4::model::assert_piece_set::<P>(bag_new);                                    // H
    if self.s4.s3.s2.s1.gameover { return false; }                                // guard
    let px = self.s4.s3.s2.s1.px;
    t1::model::new_piece_yx_state::<P>(self.gy, px, &mut self.s4.s3.s2.s1);       // relocation
    self.fix_piece(bag_new)                                                       // §3.3
}
```

**Guard.** `T5.v`'s `DropPiece` itself states no explicit guard beyond what `FixPiece`
requires — the single `self.s4.s3.s2.s1.gameover` check here is not a T5-level guard being
added but a precondition of the argument below (the relocation step must start from a state
where `LowestShadowY`'s implication is live). If `gameover` holds, `drop_piece` returns
`false`, matching a stuttering step; no state is touched (`assert_piece_set` is a pure
input-validity check, no mutation).

**Soundness of the relocation, given `¬gameover` at the pre-drop state.** Cite `LowestShadowY`
(`T5.v`) as an imported fact, established at `Init` (§7) and preserved by every T5 action
(§3.0(ii): `gy` always equals a fresh `shadow_y` computation of the current state, and
`shadow_y`'s own loop invariant, `L-shadow_y` §6, guarantees its result satisfies
`ValidPieceCannotGoDown` whenever the starting `valid(py)` holds — which
`t4::model::check_invariants`'s delegated `PieceOnFreeBlocks` conjunct supplies whenever
`¬gameover`, `t1/proofs.md` §6):
```
gameover(s4 s) = false → gy s ≤ py(s4 s) ∧ ValidPieceCannotGoDown s (gy s) ∧ …
```
i.e. `valid(gy)` and `¬valid(gy - 1)` both hold for the pre-drop `px`/`pr`/`mg`. Two
consequences:

1. **`t1::model::new_piece_yx_state`'s relocation preserves `PieceOccupiedInsideBounds` /
   `PieceOnFreeBlocks` at the relocated state.** `new_piece_yx_state` sets `py := gy`, `px :=
   px` (unchanged — passed explicitly, `implementation.md` §4-T5d), leaving `mg`/`p`/`pr`
   untouched. `valid(gy)` at the pre-drop `px`/`pr`/`mg` is exactly `L-valid`'s (`t1/proofs.md`
   §3) `occupied_inside ∧ ¬intersect` conjunction evaluated at the relocated `(py, px, pr) =
   (gy, px, pr)` — i.e. `PieceOccupiedInsideBounds`/`PieceOnFreeBlocks` both hold at the
   relocated state, by direct substitution.
2. **`t1::model::fix_piece`'s guard cannot subsequently reject.** `fix_piece`'s guard (via
   `L-can_move_piece`, `t1/proofs.md` §4) is `¬gameover ∧ ¬can_move_piece(-1,0,·)`, i.e.
   `¬gameover ∧ ¬valid(py - 1, px, pr)` at the current state. At the relocated state, `py - 1
   = gy - 1`, and `¬valid(gy - 1)` is exactly `LowestShadowY`'s second conjunct, already
   established above. `gameover` is unchanged by `new_piece_yx_state` (only `py`/`px` are
   written), so it remains `false`, the precondition this whole argument started from.

So `fix_piece`'s guard is satisfied at the relocated state by construction — no case where
the relocation is followed by a rejection exists, and no peek-then-commit ordering (contrast
`t4/proofs.md` §4's `fix_piece`) is needed: a single upfront `gameover` check on the pre-drop
state suffices, because the argument above shows that check is the *only* way `fix_piece`
could otherwise fail.

**The trailing `fix_piece` call.** Covered in full by §3.3 — its `s4` correspondence and its
own `gy`-refresh obligation are inherited, not re-argued: `fix_piece` reads the relocated
`self.s4.s3.s2.s1` (via `self.next.front()`/etc., transitively), and its post-state `gy`
recomputation (§3.0(ii)) gives the shadow of the newly-spawned piece — which is exactly what
`T5.v`'s composition `FixPiece bagNew H (NewPieceYXState (gy s, px s) s)` denotes: apply
`NewPieceYXState` first (a pure state transformation, matched above), then `FixPiece` on the
result (§3.3, applied to the relocated state as its "pre-state"). ∎

**Cap soundness — not applicable.** `drop_piece` introduces no new arithmetic and touches no
capped accumulator (`score`/`combo`/`total_cleared_lines`); it only relocates `py` and then
delegates to `fix_piece`, already covered by `t2/proofs.md` §5's cap argument.

---

## 6. `L-shadow_y`: `shadow_y::<P>(s1)` computes `ShadowY (s4 s)`

**Statement.** For every `t1::model::Machine<P>`-shaped `s1` reachable as
`self.s4.s3.s2.s1` for some reachable `Machine<P>`, `shadow_y::<P>(s1) = ShadowY α(s1)` (using
`α` from `t1/proofs.md` §2, applied to the innermost projection).

**Proof.** By induction on the loop's iteration count, equivalently on `ShadowYImpl`'s `fuel`
argument (identical measure on both sides — `fuel = py + PW - 1` initially, decremented by
exactly one per iteration/recursive call, on both the Rust loop and the Rocq `Fixpoint`, by
inspection of `shadow_y`'s definition against `ShadowYImpl`'s). At every step, the loop body's
condition (`!valid(s1.mg, s1.p, py - 1, s1.px, s1.pr)`) is, by `L-valid` (`t1/proofs.md` §3),
exactly the negation of `Valid (mg s) (p s) (py - 1, px s) (pr s)` — the same test
`ShadowYImpl`'s `if` branches on. Both sides break/return `py` on that test failing, and both
decrement `py`/`fuel` together and continue otherwise. Base case (`fuel = 0`): both sides
return the current `py` unconditionally (`ShadowYImpl`'s `O` case; the Rust `while` loop's
exit condition). By straightforward induction on this shared recursion structure, the two
compute the same result at every fuel level, hence at the initial one. ∎

**Loop invariant (used by §5).** Whenever the loop's starting `valid(s1.py, s1.px, s1.pr)`
holds (i.e. `PieceOnFreeBlocks` holds at the call site — supplied by `¬gameover` via
`t1/proofs.md` §6, as in §5 above), the returned `py` satisfies `ValidPieceCannotGoDown`:
`valid(py)` holds either because the loop never moved (the initial `py` already satisfies
`¬valid(py-1)`, the exit condition) or because the last executed iteration's `py -= 1`
assignment is immediately followed by a fuel/loop re-check whose failure is exactly
`¬valid(py-1)` at the new `py` — either way, the returned `py` is a fixed point of "one more
step down is invalid," which is `ValidPieceCannotGoDown`'s statement. `valid(py)` itself
(the first conjunct) holds by another induction on the same loop: `valid` is a loop invariant,
true initially (the hypothesis) and preserved by each step (`Valid mg p (py-1) px pr` is
exactly the condition guarding whether the step is taken at all, so every `py` value the loop
ever holds satisfies `valid`).

---

## 7. `Machine::new(bags_fn, piece_source)` ≙ `Init bags H`

```rust
let s4 = t4::model::Machine::new(bags_fn, piece_source); // spec: T4.Init bags H
let gy = shadow_y::<P>(&s4.s3.s2.s1);                     // spec: ShadowY s4
let m = Machine { s4, gy };
```

By `t4/proofs.md` §7, `α₄(s4) = T4.Init bags H` for the `bags_fn`/`piece_source` supplied.
`gy = shadow_y(&s4.s3.s2.s1)`; by `L-shadow_y` (§6), this equals `ShadowY α₄(s4) = ShadowY
(T4.Init bags H)`. Combined, `α₅(Machine::new(bags_fn, piece_source)) = {| s4 := T4.Init bags
H; gy := ShadowY (T4.Init bags H) |}` — matching `T5.v`'s `Init bags H := {| s4 := T4.Init
bags H; gy := ShadowY s4 |}` exactly, since `T5.v`'s `let s4 := T4.Init bags H` binds the same
value this call's `s4` variable does. Homomorphism condition 1 (§2). ∎

---

## 8. `check_axioms`/`check_invariants` correspondence

**`check_axioms`.** `T5.v` states no axiom at all (confirmed by direct inspection — no
`Axiom` block anywhere in the file, §1). `t5::model::check_axioms::<P>()` calls
`t4::model::check_axioms::<P>()` and asserts nothing further — exactly the empty-delta case
skill §7.4 describes ("if `B` introduces no new abstract parameters, `B`'s `check_axioms`
reduces to `A`'s"), realized here as literal pure delegation rather than a structural
trait-bound reduction (T5's `Params` trait carries no new item to make that distinction
matter, unlike T4's own `NEXT_LEN`-carrying case).

**`check_invariants`.** `t5::model::check_invariants::<P>(s)` (i) calls
`t4::model::check_invariants(&s.s4)`, which by `t4/proofs.md` §8 checks exactly `T4.Correct
(s4 s)`'s runtime-checkable conjuncts, and (ii) — gated on `!s.s4.s3.s2.s1.gameover` — asserts
`s.gy == shadow_y(&s.s4.s3.s2.s1)` and `s.gy <= s.s4.s3.s2.s1.py`. By `L-shadow_y` (§6), (ii)'s
first assertion is exactly `GyEqShadowY s`'s reading under `α₅` (§2); its second assertion is
`LowestShadowY`'s first conjunct (`gy s ≤ py (s4 s)`). `LowestShadowY`'s remaining conjunct,
`ValidPieceCannotGoDown s (gy s)` together with its universally-quantified minimality clause
(`∀ y, y ≤ py s → ValidPieceCannotGoDown s y → y ≤ gy s`), is **not** independently asserted at
runtime: the first is implied by `GyEqShadowY` combined with `L-shadow_y`'s loop invariant
(§6) whenever `s.gy` really does equal a fresh `shadow_y` computation (which (ii)'s first
assertion already checks), and the minimality clause is a property of `shadow_y`'s
*computation* (it descends until the first invalid row, hence finds the *largest* such `py`,
i.e. the minimal descent) rather than a separate fact about the stored `gy` value — so it has
no independent runtime-checkable content beyond what `L-shadow_y` already establishes
statically. This is the same "runtime check stands in only for the checkable part" pattern
`t4/proofs.md` §8 uses for `BagNextConsistent`'s omission, applied here to
`LowestShadowY`'s minimality clause.

The `!gameover` gate on (ii) mirrors `LowestShadowY`'s own precondition exactly (`T5.v`:
`gameover s = false → …`) — under `gameover = true`, `T5.v` makes no claim about `gy`'s
relationship to a fresh `shadow_y` computation, so checking it there would check a claim
`T5.v` itself doesn't state. ∎

---

## 9. Coverage

Every `T5.v` `Definition`/`Record` name is accounted for above or in `implementation.md`'s §3
naming map: `State`/`s4`/`gy` (§2), `ShadowYImpl`/`ShadowY` (§6, `L-shadow_y`), `Init` (§7),
`Event`/`Event4`/`Drop`/`Next`/`NextT4Event` (implicit, §3–§5, mirroring every prior model's
own `Next` shape — `NextT4Event`'s six cases are exactly §3's four full uses plus §4's
disjunctive `fall_step`, one level removed through `Next`'s own `Event4`/`Drop` split, which
has no Rust counterpart since `main.rs`'s action dispatch already routes to the right
method), `UnchangedT5Part` (§3.0(i), not emitted, realized as "leave `gy` untouched on
failure"), `UpdateShadowY` (§3.0, `update_shadow_y`), `MovePiece`/`RotatePiece`/`FixPiece`/
`FallStep`/`HoldPiece` (§3–§4), `NewPieceYXState` (T5-level, §5, realized inline via
`t1::model::new_piece_yx_state`), `DropPiece` (§5), `ValidPieceCannotGoDown`/
`LowestShadowY`/`GyEqShadowY`/`Correct` (§5, §6, §8), `CorrectStep` (transfers from
`t4/proofs.md`'s own step-invariant argument by composition through `fₛ = s4`, no new
content), `fₑ`/`fₛ`/`T4RefinesT5` (used throughout §3–§5 as the justification for reusing
`t4/proofs.md`'s action lemmas on `NextT4Event`-tagged transitions only — the scope note
above), `perfectClear`/`CorrectWithoutGameover`/`pyx`/`combo`/`totalClearedLines`/`swapped`/
`d` (helpers for refining models, not emitted, each a direct field projection through
`s4`/`s3`/`s2`, no independent proof content beyond composing the cited field's own T4-level
correspondence with `fₛ = s4`). No `model.rs` behavior relies on anything not accounted for
above or, transitively, in `t4/proofs.md`, `t3/proofs.md`, `t2/proofs.md`, and
`t1/proofs.md`. ∎
