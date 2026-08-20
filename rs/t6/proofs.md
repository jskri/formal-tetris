# proofs.md — refinement proof: `model.rs` ⊑ `T6.v`

Follows the `rocq-to-rust` skill's `proofs.md` skeleton (skill §6). `t6::model::Machine<P>`
being a type alias for `t5::model::Machine<P>` (`implementation.md` §1) collapses most of the
skeleton to "inherited, unchanged" — this file states the delta over `t5/proofs.md`
(transitively `t4/proofs.md`, `t3/proofs.md`, `t2/proofs.md`, `t1/proofs.md`) in full, and
gives its full attention to the one genuinely new argument: `rotate_kick_piece` (§5). Order:
scope (this note), parameter/state mapping (§1–§2), `Init` (§3), every `Event5`-tagged action
(§4), `RotateKickPiece` (§5), `check_axioms`/`check_invariants` (§6), coverage (§7).

> **Scope.** `RotateKick` has no refinement claim in `T6.v` itself: `T6.v`'s own `Refinement`
> section states `fₑ : T5.Event → T5.Event := id`, `fₛ : T6.State → T6.State := id`, and
> `T6RefinesT5`'s second conjunct is quantified over `NextT5Event`, **not** `Next` — i.e. over
> `Event5`-tagged transitions only. `T6.v`'s own prose is explicit about why: *"the wall kick
> mechanics is genuinely new: it has no counterpart in T5 and any T6 behavior that contains a
> wall kick cannot be mapped to a T5 behavior."* This is structural, the same shape
> `t3/proofs.md`'s exclusion of `Hold` and `t5/proofs.md`'s exclusion of `Drop` already take —
> not a gap this proof works around, a fact it states and then respects (§4–§5 below only ever
> invoke `T6.v`'s `NextT5Event` case for the *composing* half of an argument, never treating
> `RotateKick` as if it had a refinement obligation of its own).
>
> As with every model in this tower, this is a **safety** argument only — no converse/
> completeness clause (Lynch & Vaandrager, *Information and Computation* 121(2):214–233, 1995,
> §3). Non-completeness transfers unchanged from `t5/proofs.md`'s own scope note (`T3.FixPiece`'s
> unconstrained piece argument, four layers down); T6 introduces no new source of it, and closes
> none of the existing one either.

All section/definition references without a file prefix are to `T6.v`; `Dn`/`D-Name`
references are to `implementation.md`'s decision register; `α`/unprefixed `Ln` refer to
`t1/proofs.md`; `α₅`/T5-prefixed `Ln` refer to `t5/proofs.md`.

---

## 1. Parameter mapping

`T6.v` declares no `Parameter` of its own (confirmed by direct inspection — no `Parameter`/
`Axiom` block anywhere in the file). Identical to `t5/proofs.md` §1: the proof is generic over
any `P: t5::model::Params` for which `t4::model::check_axioms::<P>()` succeeds — the same `P`,
not merely an analogous one, since `t6::model::Params` **is** `t5::model::Params`
(`implementation.md` §6.0: no new trait, `pub use t5::model::Params;`).

---

## 2. State mapping α₆

```
α₆ = α₅
```

Not "defined to equal," but literally the same function applied to the same value: since
`Machine<P>` here is `t5::model::Machine<P>` (`implementation.md` §1), no Rust value of type
`t6::model::Machine<P>` exists that isn't already a `t5::model::Machine<P>` value, and no
projection step is needed to view one as the other. Every fact `t5/proofs.md` §2 establishes
about `α₅` — totality, well-definedness — holds of `α₆` for the same reason, without
restatement.

**Homomorphism condition 1** (`Init`) is §3. **Condition 2** (the commuting square) is
discharged only for `NextT5Event`-tagged transitions (§4), matching `T6RefinesT5`'s own
restricted scope (the note above); `RotateKick` (§5) is proved correct against `T6.v`'s
`RotateKickPiece` directly, not against this commuting square, exactly mirroring how
`t5/proofs.md` §5 argues `drop_piece` on its own terms rather than folding it into `t5/proofs.md`
§2's homomorphism condition.

---

## 3. `Init` — `T6.Init := T5.Init`

`t6::model` defines no `Machine::new` of its own (`implementation.md` §6.1) — by the alias,
every construction site uses `t5::model::Machine::<P>::new(...)` directly. `T6.v`'s own
`Definition Init := T5.Init` is a literal Rocq alias, not a wrapper computing something new
from `T5.Init`'s result. So homomorphism condition 1 needs no new argument: `α₆(m) = α₅(m) =
T5.Init bags H` for `m = t5::model::Machine::<P>::new(bags_fn, piece_source)`, by `t5/proofs.md`
§7 directly, and `T6.Init bags H = T5.Init bags H` by `T6.v`'s own definition. The two sides
agree because they are, respectively, the same Rust call and the same Rocq definition
`t5/proofs.md` §7 already covers. ∎

---

## 4. Every `Event5`-tagged action — full use, inherited without restatement

`move_piece`, `rotate_piece`, `fix_piece`, `fall_step`, `hold_piece`, `drop_piece` are not
redefined by `t6::model` (`implementation.md` §5: no free functions, no new methods beyond
`rotate_kick_piece`). Each is `t5::model::Machine<P>`'s own inherent method, reached on a
`t6::model::Machine<P>` value because the two types are one and the same (§2). `T6.v`'s
`NextT5Event e5 s := T5.Next e5 s` is, definitionally, exactly what `t5/proofs.md` §3–§5 already
prove each of these methods realizes. Nothing here composes two proofs or introduces a new
transfer argument — there is only one proof, `t5/proofs.md`'s, and it applies verbatim because
`α₆ = α₅` (§2) and the Rust methods are the identical methods, not delegating calls through a
wrapper. ∎

---

## 5. `rotate_kick_piece(&mut self, cw) -> bool` ≙ `RotateKickPiece cw`

```rust
fn rotate_kick_piece(&mut self, cw: bool) -> bool {
    let s1 = &self.s4.s3.s2.s1;
    if s1.gameover || t1::model::can_rotate_piece::<P>(cw, s1) {
        return false;
    }
    let (orig_py, orig_px) = (s1.py, s1.px);
    t1::model::new_piece_yx_state::<P>(orig_py, orig_px - 1, &mut self.s4.s3.s2.s1); // left
    let mut fired = self.rotate_piece(cw);
    if !fired {
        t1::model::new_piece_yx_state::<P>(orig_py, orig_px + 1, &mut self.s4.s3.s2.s1); // right
        fired = self.rotate_piece(cw);
    }
    if !fired {
        t1::model::new_piece_yx_state::<P>(orig_py, orig_px, &mut self.s4.s3.s2.s1); // restore
    }
    if t5::model::CHECK_INVARIANTS { t5::model::check_invariants(self); }
    fired
}
```

```
RotateKickPiece cw s :=
  if (¬gameover s) ∧ (¬plainRotFires) then
    match T5.RotatePiece cw (T5.NewPieceYXState (py s, px s - 1) s) with
    | Some s' => Some s'
    | None => T5.RotatePiece cw (T5.NewPieceYXState (py s, px s + 1) s)
    end
  else None
where plainRotFires := isSome (T5.RotatePiece cw s)
```

Per skill §7.1's classification: this is a **no-use** action — no T5/T4/… action is invoked as
a subterm before the exclusivity check, and the relocation steps (`new_piece_yx_state`) are
total state constructors, not guarded actions. The two `self.rotate_piece(cw)` calls *are*
genuine reuse, argued via §4 once the state each is called on is shown to correspond to the
right Rocq argument.

### 5.1 A frame lemma for `t1::model::new_piece_yx_state`, lifted through T2–T6

`t1/proofs.md` §10 establishes `new_piece_yx_state::<P>(py_new, px_new, s) ≙ NewPieceYXState
(py_new, px_new) s`, setting only `py`/`px`, leaving `mg`/`p`/`pr`/`gameover`/`cleared_lines`
untouched — a fact about `t1::model::Machine<P>`. Two things extend it to
`t6::model::Machine<P>` (= `t5::model::Machine<P>`):

1. **Frame, lifted.** The Rust call site here is `t1::model::new_piece_yx_state::<P>(orig_py,
   orig_px ± {-1,0,1}, &mut self.s4.s3.s2.s1)` — a mutable borrow of exactly the innermost T1
   sub-state, nothing else. No field of `self.s4.s3.hold`/`self.s4.next`/`self.s4.bag`/`self.gy`
   (or any T2–T5-introduced field) is reachable through that borrow, so none is touched. On the
   Rocq side, `T6.NewPieceYXState := T5.NewPieceYXState`, and by the same induction every prior
   layer's own helper alias (`T5.NewPieceYXState := T4.NewPieceYXState := … := T1.NewPieceYXState`,
   each layer's "helpers for refining models" section, e.g. `T6.v`'s own `Definition
   NewPieceYXState := T5.NewPieceYXState`), applied to a nested record only overwrites the
   named `py`/`px` path and leaves every field outside it — including every field T2–T6 added —
   as a literal copy of the input record's own value (Rocq's functional record update touches
   only the field(s) it names). Both sides therefore leave every field outside `py`/`px` — at
   *every* layer, not just T1's — unchanged.
2. **Unconditional overwrite, not a delta.** `new_piece_yx_state` sets `py := py_new; px :=
   px_new` outright, independent of the pre-call values. Two calls in sequence,
   `new_piece_yx_state(a, b, ·)` then `new_piece_yx_state(a, c, ·)` with nothing else touched in
   between, therefore leave `py = a, px = c` — the same as a single call to
   `new_piece_yx_state(a, c, ·)` from the original state. This is what makes "both kick attempts
   computed from `orig_px`, never chained" (`implementation.md` §4-T6b) correct *despite* the
   Rust code not explicitly reverting the first attempt's relocation before trying the second —
   the second relocation's own unconditional overwrite already erases the first's effect.

Write `s[py↦y, px↦x]` for "`s` with only its `py`/`px` fields set to `y, x`." By (1)–(2), for any
Rust value `v` reachable at the point `new_piece_yx_state(y, x, ·)` is called, whose only
difference from a reference state `s` is in `py`/`px` (or no difference at all), the call
produces exactly `α(s)[py↦y, px↦x]`, regardless of what `v`'s own `py`/`px` were.

### 5.2 Case: the exclusivity guard fails

Rust: `s1.gameover ∨ can_rotate_piece(cw, s1)` → `return false`, no field touched. By
`L-can_rotate_piece` (`t1/proofs.md`, added alongside the `can_rotate_piece` patch,
`implementation.md` §0.2): under `¬gameover`, this is exactly `plainRotFires`; combined with the
`gameover` disjunct via De Morgan, the Rust early-return condition is exactly the negation of
Rocq's `(¬gameover s) ∧ (¬plainRotFires)` guard. So `return false` fires iff `RotateKickPiece cw
s = None` via the `else` branch — a stuttering step (no field touched ⟹ `α₆` of the unchanged
state equals the Rocq pre-state).

### 5.3 Case: the guard holds, left kick fires

Let `s` be the pre-call state, `(orig_py, orig_px) = (s.py, s.px) = (py α(s), px α(s))`.
`new_piece_yx_state(orig_py, orig_px - 1, ·)` is called with nothing yet touched relative to
`s`, so by §5.1 it produces `α(self) = α(s)[py↦py s, px↦px s - 1] = T5.NewPieceYXState (py s, px
s - 1) s` (`NewPieceYXState`'s own definition is exactly this field overwrite). `self.rotate_piece(cw)`
is then called on this state; by §4 (`t5/proofs.md` §3.2, applied here since `α₆ = α₅`), if it
returns `true`, `self` afterward corresponds exactly to `T5.RotatePiece cw (T5.NewPieceYXState
(py s, px s - 1) s)`'s `Some` payload — precisely Rocq's `match`'s `Some s' => Some s'` arm,
taken because the scrutinee is `Some`. `fired = true`; the `if !fired` restore block is skipped
(both remaining ones); Rust returns `true`. Matches. ∎

### 5.4 Case: the guard holds, left kick fails, right kick fires

The left `self.rotate_piece(cw)` call fails. By the full-use stutter property (`t1/proofs.md`
§4.2, lifted through T2–T5's own full-use lemmas exactly as §4 above lifts the success case):
failure touches no field — in particular, `rotate_piece` only ever writes `pr` (on success), so
regardless of success or failure it never touches `py`/`px`. So immediately after the failed
left attempt, `self` differs from `s` in exactly one respect: `px = orig_px - 1` (set by the
left relocation, untouched by the failed rotation). Call this intermediate value `v`.

`new_piece_yx_state(orig_py, orig_px + 1, ·)` is now called on `v`. By §5.1(2) (unconditional
overwrite), the result is `α(s)[py↦py s, px↦px s + 1]` — *not* `v[py↦…, px↦…]` with `v`'s
already-modified `px` folded in anywhere; the overwrite is absolute, so `v`'s `px = orig_px - 1`
plays no role in the outcome. This equals `T5.NewPieceYXState (py s, px s + 1) s` exactly,
independent of the failed left attempt ever having happened — which is exactly why Rocq's own
right-kick argument, `T5.NewPieceYXState (py s, px s + 1) s`, is written relative to the
*original* `s`, not to some intermediate "`s` after the left attempt": Rocq has no such
intermediate (its `match` only ever evaluates the scrutinee `T5.RotatePiece cw
(T5.NewPieceYXState (py s, px s - 1) s)` and, on `None`, discards it entirely, never threading it
into the second branch) — and the Rust code, despite executing procedurally, arrives at the same
"discard and recompute from `s`" outcome via the overwrite semantics, not via an explicit
reset.

`self.rotate_piece(cw)` is then called on this state; if it returns `true`, by §4, `self`
afterward corresponds to `T5.RotatePiece cw (T5.NewPieceYXState (py s, px s + 1) s)`'s `Some`
payload — exactly Rocq's inner `match`'s `None => T5.RotatePiece cw (T5.NewPieceYXState (py s,
px s + 1) s)` arm (reached because the outer `match`'s scrutinee was `None`, matching the
Rust `if !fired` having been entered). `fired = true` on this second attempt; the final
restore block is skipped. Rust returns `true`. Matches. ∎

### 5.5 Case: the guard holds, both kicks fail

Continuing §5.4 up to the second `self.rotate_piece(cw)` call, but now it also fails. By the same
stutter property, this second failure touches nothing beyond what the second relocation already
set — so `self` at this point is `α(s)[py↦py s, px↦px s + 1]`, differing from `s` in exactly
`px = orig_px + 1`.

The final `new_piece_yx_state(orig_py, orig_px, ·)` is called. By §5.1(2), this overwrites
`py`/`px` to `(orig_py, orig_px)` unconditionally — i.e. to `(s.py, s.px)` themselves, since
`orig_py = s.py` and `orig_px = s.px` by definition. The result is `α(s)[py↦py s, px↦px s]`,
which is `α(s)` itself, field for field: every field outside `py`/`px` was already untouched
(§5.1(1), both relocations and both failed rotations), and `py`/`px` are now set back to their
original values. So `self = s`, byte for byte — not merely `α`-equivalent to `s`, the literal
same Rust value. `fired = false`; Rust returns `false`.

This restore is not defensive housekeeping — it is *required* for correctness. Without it,
`self` would be left at `α(s)[py↦py s, px↦px s + 1]` (the state after the failed right attempt),
which is not `α(s)`, and a `false`-returning method leaving a state that differs from its input
would violate the "guard fails ⟹ stutter" correspondence every model in this tower relies on
(skill §6.3) — Rocq's `else` branch and the inner `match`'s both-`None` sub-case both denote
`None`, i.e. **no transition at all**, which is only correctly realized by a Rust state
byte-identical to the pre-call one. With the restore in place, `self = s` exactly, matching
`RotateKickPiece cw s = None` via the inner `match` collapsing both its arms to `None`
(`T5.RotatePiece cw (T5.NewPieceYXState (py s, px s + 1) s) = None`, the hypothesis of this
case) and that `None` then being the outer `if`'s `then`-branch's value. ∎

### 5.6 `check_invariants` at the end

`t5::model::CHECK_INVARIANTS`-gated, calling `t5::model::check_invariants(self)` once, after
every relocation/rotation attempt has completed — never on an intermediate state. On the
`fired = true` paths (§5.3, §5.4), `self` is exactly the `Some` payload of a genuine
`self.rotate_piece(cw)` call, whose own success path already runs this same check internally
(`t5/implementation.md` §4-T5b) — redundant, not incorrect, the same "accepted redundancy" every
prior layer's own doubled checks already are (`t5/implementation.md` §4-T5d's `assert_piece_set`
note). On the `fired = false` path (§5.2, §5.5), `self = s`, and `T6.Correct s = T5.Correct s`
(`T6.v`'s own `Definition Correct (s : State) : Prop := T5.Correct s`) was already established
of `s` by whatever produced it — checking it again here is a no-op assertion, not a new
obligation. `T6.Correct` states nothing beyond `T5.Correct` (§1's parameter mapping already
established `t6::model::Params = t5::model::Params`; likewise here, no new invariant conjunct
exists for this check to miss).

---

## 6. `check_axioms`/`check_invariants` — no correspondence to state; inherited

`t6::model` defines neither. `T6.v` states no `Axiom` (confirmed by inspection) and `Correct :=
T5.Correct` verbatim — so there is nothing for a `t6::model::check_axioms`/`check_invariants` to
do beyond what `t5::model::check_axioms`/`t5::model::check_invariants` already do, and
`implementation.md` §7 correspondingly defines neither function at this layer: every call site
in `rotate_kick_piece` (§5.6) and everywhere else in `t6` reaches these by their `t5::model::`
path directly. `t5/proofs.md` §8 already establishes their correctness against `T5.v`; since
`T6.Correct = T5.Correct` and `T6.v` adds no axiom, that same correctness statement *is* the
correctness statement for `T6.Correct`/`T6`'s (nonexistent) new axiom set, with no translation
step in between. ∎

---

## 7. Coverage

Every `T6.v` name is accounted for above or in `implementation.md`'s §3 naming map: `State`
(§2, the alias itself), `Init` (§3), `RotateKickPiece` (§5), `Event`/`NextT5Event`/`Next`
(implicit, §4–§5, mirroring every prior model's own dispatch shape — `main.rs`'s action
dispatch already routes to the right method, `implementation.md` §15.2), `Correct`/`CorrectStep`
(§5.6, §6 — both verbatim `T5.v` aliases, no independent content), `fₑ`/`fₛ`/`T6RefinesT5`
(the scope note above and §2, as the restricted-composition justification for §4), `s5`,
`MovePiece`/`RotatePiece`/`FixPiece`/`HoldPiece` (T6's own aliases for T5's; §4), `mg`/`p`/`pyx`/
`pr`/`gameover`/`clearedLines`/`score`/`level`/`combo`/`perfectClear`/`totalClearedLines`/
`hold`/`swapped`/`d`/`gy`/`px` (helpers for refining models, not emitted, each a verbatim `T5.v`
alias — no independent proof content, composing whichever cited T1–T5-level correspondence
already covers the underlying field with `α₆ = α₅`), `UnchangedT6Part` (not emitted — the
"leave every field outside `py`/`px` alone" half of §5.1's frame lemma, stated inline rather
than as a standalone Rust definition, matching every prior model's own treatment of its
`UnchangedTnPart` counterpart), `NewPieceYXState` (T6-level alias for `T5.NewPieceYXState`; §5.1),
`CorrectWithoutGameover` (verbatim `T5.v` alias, not independently used by any argument above).
No `model.rs` behavior relies on anything not accounted for above or, transitively, in
`t5/proofs.md`, `t4/proofs.md`, `t3/proofs.md`, `t2/proofs.md`, and `t1/proofs.md`. ∎
