# proofs.md — refinement proof: `model.rs` ⊑ `T4.v`

Follows the `rocq-to-rust` skill's `proofs.md` skeleton (skill §6), specialized by §7's
wrapping-module rules: this file states only the **delta** over `t3/proofs.md`, reusing
`t3/model.rs ⊨ T3.v` (hence, transitively, `t2/model.rs ⊨ T2.v` and `t1/model.rs ⊨ T1.v`)
in full for every `s3`-shaped fact. Order: scope (this note), parameter/state mapping
(§1–§2), each full-use action (§3), the disjunctive action (§4), `fix_piece` argued in
full as the representative partial-use case (§4 folds this in), `hold_piece` argued with
one imported dependency (§5), the new invariants (§6), `Init` (§7),
`check_axioms`/`check_invariants` correspondence (§8), coverage (§9).

> **Scope, and what is different from every prior model in this tower.** `T4.v`'s own
> `T4RefinesT3` quantifies over **all** of `Event` — unlike `T3RefinesT2` (`t3/proofs.md`'s
> own scope note), which excludes `Hold` entirely, T4 refines T3 for every one of its five
> events, `Hold` included (`T4.v`'s `Refinement` section). So §3–§6 below all compose with
> `t3/proofs.md`, including `hold_piece` — no "no use, fresh argument" section is needed
> here the way `t3/proofs.md` §5 needed one for its own `hold_piece`.
>
> As with every model in this tower (`t1/proofs.md`–`t3/proofs.md`), this proof is a
> **safety** argument only: `RefineT4` has exactly two conjuncts (`InitRefineT4`,
> `NextRefineT4`), no converse/completeness clause. Lynch & Vaandrager (*Information and
> Computation* 121(2):214–233, 1995, §3) is the standard justification for why a forward
> simulation of this shape is sufficient for trace-inclusion safety properties; converse
> completeness is in any case false here, and non-vacuously so: `T3.FixPiece` accepts an
> arbitrary piece argument per call, admitting traces (e.g. "`Fix X` forever" for a fixed
> `X`) that no reachable `T4` state can produce once `bag`/`next` are forced into a
> `Piece`-bijection by `H`'s precondition — so the "T4 realizes every T3 behavior" converse
> is actively false, not merely unproved.

All section/definition references without a file prefix are to `T4.v`; `Dn`/`D-Name`
references are to `implementation.md`'s decision register; unprefixed `α`/`Ln` refer to
`t1/proofs.md`; `α₂`/T2-prefixed `Ln` refer to `t2/proofs.md`; `α₃`/T3-prefixed `Ln` refer
to `t3/proofs.md`.

---

## 1. Parameter mapping

`T4.v` adds exactly one abstract parameter beyond `T1.v`'s: `NextLen`, realized as
`Params::NEXT_LEN` (`implementation.md` §6.0). The proof is generic over any `P:
t4::model::Params` for which `t4::model::check_axioms::<P>()` succeeds — i.e. any `P: T3
Params` (the same `P` `t3/proofs.md` §1 quantifies over, since T3 adds no parameters of
its own) together with `NEXT_LEN > 0` and `|Piece| > 0` (§8 below).

`MaxBagLen` is **not** a second parameter to map: `T4.v`'s own definition forces
`MaxBagLen = |Piece|` for any finite `Piece` (`implementation.md` §3's pigeonhole
argument), so every occurrence of `MaxBagLen` below is read as `P::piece_all().len()`
throughout, with no separate mapping obligation.

---

## 2. State mapping α₄

```
α₄(rs4) = {| s3   := α₃(rs4.s3)
          ;  bag_  := λ i, if i < rs4.bag.len() then rs4.bag[i] else <arbitrary>
          ;  next_ := λ i, rs4.next[i]                                  (* i < NEXT_LEN *)
          ;  bagLen_ := rs4.bag.len()
          |}
```

`bag`/`next` map to the corresponding Rocq `ℕ → Piece` functions via the "array = bounded
total function" pattern (skill §2, already used for T1's grids and reused here rather than
re-derived): `α₄`'s `bag_`/`next_` are total functions on all of `ℕ`, as `T4.v`'s `Draw`
record requires, but only their values on `[0, bagLen_)`/`[0, NextLen)` respectively are
ever read by any `T4.v` definition — values outside those ranges are immaterial to every
proof obligation below, so the `<arbitrary>` filler for `bag_`'s out-of-range indices needs
no further justification (same status as `t1/proofs.md`'s own treatment of `mg`'s
out-of-`Full`-region cells).

**Totality and well-definedness.** `α₃` is total on every `t3::model::Machine<P>` value
(`t3/proofs.md` §2). `rs4.bag: Vec<P::Piece>` and `rs4.next: VecDeque<P::Piece>` are both
finite, in-memory, always-initialized Rust values for any `Machine<P>` reachable through
`Machine::new`/the five action methods (no `unsafe`, no partial construction anywhere in
`model.rs`), so `α₄` is total wherever `α₃` is.

**Homomorphism condition 1** is §7's `Init` correspondence. **Condition 2** (the commuting
square) is discharged for **every** `Event` below (§3–§5), unlike `t3/proofs.md` §2's
restriction to `Event2`-tagged transitions only — matching `T4RefinesT3`'s unrestricted
scope (the note above).

---

## 3. Full-use actions

### 3.1 `move_piece(&mut self, dy, dx) -> bool` ≙ `MovePiece (dy,dx)` — full use (skill §7.1)

`self.s3.move_piece(dy, dx)` is exactly `t3::model::Machine::move_piece`, already proved
(`t3/proofs.md` §3.1) to commute with `α₃` and `T3.MovePiece`. `T4.MovePiece dyx s =
option_map (UnchangedT4Part s) (T3.MovePiece dyx (s3 s))` — `UnchangedT4Part` copies
`bag_`/`next_`/`bagLen_` from the pre-state `s` unchanged. Since
`t4::model::Machine::move_piece` forwards to the T3 call and returns its result with no
write to `self.bag`/`self.next` anywhere in the method body, `α₄` commutes with this step
by direct composition with `t3/proofs.md` §3.1: the `s3` component tracks via the cited
lemma, and `bag`/`next` are unchanged on both sides by inspection. ∎

### 3.2 `rotate_piece(&mut self, cw) -> bool` ≙ `RotatePiece cw` — full use

Identical shape to §3.1, composing with `t3/proofs.md` §3.2 instead of §3.1:
`self.s3.rotate_piece(cw)` is forwarded and returned verbatim; `T4.RotatePiece cw =
option_map (UnchangedT4Part s) (T3.RotatePiece cw (s3 s))` leaves `bag_`/`next_`/`bagLen_`
unchanged on the Rocq side to match. ∎

---

## 4. `fix_piece(&mut self, bag_new) -> bool` ≙ `FixPiece bagNew` — partial use, piece supplied by T4

`T4.v`: `FixPiece bagNew H s := option_map (λ s3', {| s3 := s3'; bag_ := bag_ dd'; next_ :=
next_ dd'; bagLen_ := bagLen_ dd' |}) (T3.FixPiece (next s 0) (s3 s))`, where `dd' =
DrawNextPiece (draw s) bagNew` is computed **unconditionally** before the `option_map`
(`T4.v`'s `let`), and `H : PieceSet bagNew` is the call's precondition.

**Two things beyond what transfers from `t3/proofs.md` §3.3.**

**(a) The piece supplied is `next s 0`, definitionally.**
```rust
let p = *self.next.front().expect("next non-empty");
let fired = self.s3.fix_piece(p);
```
`self.next.front()` reads position 0 of `self.next`, i.e. `α₄(self).next_ 0`, before any
mutation of `self` — exactly `next s 0` at the pre-state, by §2's mapping. So the argument
`t4::model::Machine::fix_piece` passes to `self.s3.fix_piece` is, by construction, the same
value `T4.FixPiece`'s Rocq definition passes to `T3.FixPiece`.

**(b) Guard failure implies zero mutation of `bag`/`next` — needed to extend the
stuttering-step argument.** `T4.v`'s Rocq `let dd' := ...` computes the popped `Draw`
*unconditionally*, but `option_map` discards it entirely when the inner `T3.FixPiece` call
returns `None` — the `let` is a value binding, not an observable effect. A translation that
mutated `self.bag`/`self.next` before knowing whether `self.s3.fix_piece(p)` succeeds would
desync from every reachable `T4.v` state whenever `T3.FixPiece`'s guard fails (e.g. via
`fall_step` when `self.s3.s2.s1.gameover` is already `true`, §5). `model.rs` avoids this by
ordering the draw **after** confirming `fired`:
```rust
let fired = self.s3.fix_piece(p);
if !fired {
    return false;
}
self.draw_next_piece(bag_new);
```
So on guard failure, `self.s3.fix_piece(p)`'s own zero-mutation property (`t3/proofs.md`
§3.3's `fired = false` case, transferred via (a)'s argument that the piece passed matches)
combines with `self.bag`/`self.next` being syntactically unreached on this path to give:
the entire call is a stutter, `α₄(self)` unchanged, matching `option_map`'s behavior on
`T3.FixPiece`'s `None` — exactly the property `t1/proofs.md`–`t3/proofs.md`'s own
stuttering-step arguments need, now extended to T4's two new fields.

**Guard holds.** By `t3/proofs.md` §3.3, `α₃(self.s3)` after the inner call equals
`T3.FixPiece (next s 0) (s3 s)`'s `Some` payload. `self.draw_next_piece(bag_new)` then
performs exactly one `draw_once` (§4-of-`implementation.md`'s `DrawNextPiece` realization,
argued in full in §6 below), giving `α₄(self).{bag_,next_,bagLen_}` after the call equal to
`DrawNextPiece (draw s) bagNew`'s three projections — matching `dd'` exactly. Combined,
`α₄(self)` after the call equals `T4.FixPiece bagNew H s`'s `Some` payload. ∎

### 4.1 `fall_step(&mut self, bag_new) -> bool` ≙ `FallStep bagNew` — disjunctive

Rocq: `match MovePiece (-1,0) s with Some s' => Some s' | None => FixPiece bagNew H s end`
(`T4.v`, identical shape to `T2.v`'s/`T3.v`'s own `FallStep`). Rust:
```rust
if self.move_piece(-1, 0) { return true; }
self.fix_piece(bag_new)
```
**Mutual exclusivity**, inherited by composition through `t3/proofs.md` §4 and, beneath
that, `t2/proofs.md` §5 and `t1/proofs.md` §5: `self.move_piece(-1, 0)` (§3.1) and
`self.fix_piece(·)` (§4) share their guard at the innermost `t1::model::Machine` layer — T2,
T3, and T4 each add no new guard to either. So the same case split established two/three
layers down applies here: if `self.move_piece(-1,0)` returns `true`, `fall_step` returns
`true` immediately, matching Rocq's `Some s'` branch via §3.1's already-proved commutation;
otherwise it falls through to `self.fix_piece(bag_new)` (§4), matching Rocq's `None` branch
falling through to `FixPiece bagNew H s` exactly. ∎

---

## 5. `hold_piece(&mut self, bag_new) -> bool` ≙ `HoldPiece bagNew` — partial use, one imported dependency

`T4.v`: `hold s := (s3 s).hold` (a direct passthrough — `T4.v`'s `hold` accessor is
literally T3's own field, not recomputed), so `T3.HoldPiece`'s internal `match hold s with
Some p => p | None => p_new end` reads the *same* `Option` T4's own guard below tests.

```rust
pub fn hold_piece(&mut self, bag_new: &[P::Piece]) -> bool {
    assert_piece_set::<P>(bag_new);
    if self.s3.s2.s1.gameover {
        return false;
    }
    let p2 = match self.s3.hold {
        Some(h) => h,
        None => self.draw_next_piece(bag_new),
    };
    let fired = self.s3.hold_piece(p2);
    if !fired {
        return false;
    }
    if CHECK_INVARIANTS { check_invariants(self); }
    true
}
```

**Two claims, matching `implementation.md` §4-T4h.**

**(a) The `Some` (skip) branch matches the spec exactly, independent of any invariant.**
Since `hold s = (s3 s).hold` definitionally, whichever branch `t4::model::Machine::hold_piece`
takes on `self.s3.hold`, `T3.HoldPiece`'s own `match hold s with ... end` necessarily takes
the corresponding branch on the same value — no case-specific argument needed beyond the
definitional equality itself.

**(b) The `None` (commit) branch's draw cannot subsequently be rejected.** `T3.HoldPiece`'s
guard is `¬gameover ∧ ¬swapped` (`t3/proofs.md` §5.1). `¬gameover` is established by the
`if self.s3.s2.s1.gameover { return false; }` check three lines above, unconditionally, for
every execution reaching `self.draw_next_piece`. `¬swapped` is **imported**, not
re-derived: `t3/proofs.md` §6.1's `SwappedImplyHoldSome` (`swapped s ⟹ hold s ≠ None`),
contrapositive `hold s = None ⟹ ¬swapped s`, applies exactly to this branch (the `None`
arm is reached precisely when `self.s3.hold = None`, i.e. `hold s = None`). So both guard
conjuncts hold whenever `self.draw_next_piece(bag_new)` is called, meaning
`self.s3.hold_piece(p2)`'s own guard (`t3/proofs.md` §5.1, transferred unchanged — T4 adds
no new condition to it) is satisfied, and `fired` is `true` — the `if !fired { return
false; }` line is a defensive check on an unreachable branch in any state satisfying
`T3.Correct`, not a case this proof needs to discharge, since §6 below establishes
`T3.Correct` is maintained by every T4 transition. This is exactly `implementation.md`
§4-T4h's argument, restated here as the proof obligation it discharges.

**`s3`/`bag`/`next` after the call.** By (a)+(b) and `t3/proofs.md` §5.3's own commutation
for `self.s3.hold_piece`, `α₃(self.s3)` after the call equals `T3.HoldPiece p2 (s3 s)`'s
payload with `p2` matching Rocq's own `match`-selected value. `self.bag`/`self.next` are
mutated by `draw_next_piece` exactly when Rocq's `hold s = None` branch is taken (by (a)'s
definitional-equality argument) — i.e. exactly the same condition under which `T4.v`'s
`HoldPiece` definition itself calls `DrawNextPiece`. Combined with §4's already-proved
`draw_once` commutation (invoked identically here, via the same private
`draw_next_piece` wrapper), `α₄(self)` after the call equals `T4.HoldPiece bagNew H s`'s
`Some` payload. ∎

---

## 6. `TypeOK`/`BagNonEmpty`/`BagNextConsistent` preservation

No T3 analogue — needs its own induction, over `draw_once`'s two branches. This is the
argument §4 and §5 above both invoke by reference as "§4's already-proved `draw_once`
commutation"; stated once here rather than inline at each call site.

```rust
fn draw_once<P: Params>(bag: &mut Vec<P::Piece>, next: &mut VecDeque<P::Piece>, bag_new: &[P::Piece]) -> (P::Piece, bool) {
    let resetting = bag.len() == 1;
    let p = next.pop_front().expect(...);
    next.push_back(bag.pop().expect(...));
    if resetting { bag.clear(); bag.extend_from_slice(bag_new); }
    (p, resetting)
}
```

**No-reset branch (`resetting = false`, i.e. `bag.len() ≥ 2` on entry).** `bagLen_ > 1`
Rocq-side (`BagNonEmpty`'s strict form after excluding the `≤ 1` case), so
`DrawNextPiece`'s `bagSingle` branch is not taken; its else-branch sets `bagLen_' :=
bagLen_ - 1`, `next_' := ShiftNext next_ (bag_ (bagLen_-1))`, `bag_' := bag_` (unchanged).
`bag.pop()` removes and returns `bag`'s last live element — by `α₄`'s mapping, exactly
`bag_ (bagLen_ - 1)` — and `bag.len()` becomes `bagLen_ - 1` after, matching `bagLen_'`
directly; `bag_` itself (the Rust `Vec`'s remaining live prefix, positions `[0,
bagLen_-1)`) is untouched, matching `bag_' = bag_` on every index that still matters (i.e.
below the new, smaller `bagLen_'` — §2's mapping note on out-of-range indices makes the
Rust `Vec`'s further truncation immaterial). `next.pop_front()` + `next.push_back(popped)`
is exactly `ShiftNext`'s drop-index-0-append-tail on a length-`NEXT_LEN` sequence, by
inspection of both definitions. `TypeOK`'s two conjuncts on `bag_`/`next_`
(pairwise-distinct, `⊆ Piece`) are preserved since no new values are introduced — `next`'s
new last entry is `bag`'s old last entry, already a member of `Piece` and already distinct
from every other live `bag`/`next` entry by the pre-state's own `TypeOK`. `BagNonEmpty`
(`bagLen_ ≥ 1`) is preserved since `bagLen_ - 1 ≥ 1` exactly when `bagLen_ ≥ 2`, the
branch's own entry condition.

**Reset branch (`resetting = true`, i.e. `bag.len() = 1` on entry, `BagNonEmpty` excludes
`0`).** `DrawNextPiece`'s `bagSingle` branch: `bagLen_' := MaxBagLen`, `bag_' := bagNew`,
`next_'` as above (the `ShiftNext` step is unconditional, computed identically in both
branches — `T4.v`'s `let` structure makes this explicit, `implementation.md` §4-T4a
preserves the same ordering). `bag.clear(); bag.extend_from_slice(bag_new)` sets
`bag.len() = bag_new.len() = MaxBagLen` (by `H : PieceSet bagNew`'s length conjunct,
realized as `assert_piece_set`'s `arr.len() == all.len()` check, §8 below) and `bag`'s
content to `bag_new` verbatim — matching `bagLen_' = MaxBagLen`, `bag_' = bagNew` exactly.
`TypeOK` for the new `bag_'` holds because `H`'s remaining two conjuncts (pairwise-distinct,
`⊆ Piece`) are exactly `is_piece_set`'s other two checks, both asserted by
`assert_piece_set` before `draw_once` is ever reached (§4/§5's call sites both check `H`
first). `TypeOK` for `next_'` holds by the same argument as the no-reset branch (the
`ShiftNext` step is identical in both branches). `BagNonEmpty` holds since `MaxBagLen > 0`
is exactly `AxiomsMaxBagLen`, checked once by `check_axioms` before any `Machine<P>` is
constructed (§8).

`BagNextConsistent`'s `k = min(MaxBagLen - bagLen_, NextLen)` formula: in the no-reset
branch, `bagLen_` decreases by exactly 1 while `next_`'s newly-written tail entry is
precisely the value moved out of `bag_`'s old last live position — the pair `(bag_,
next_)`'s joint content is preserved element-for-element across the shift, so if
`BagNextConsistent` held for the pre-state's `k`, it holds for the post-state's `k+1` (one
more of `bag_`'s beyond-`bagLen_'` tail is now mirrored into `next_`, by construction of the
single `push_back` just performed). In the reset branch, `bagLen_' = MaxBagLen`, so `k' =
min(0, NextLen) = 0` — `BagNextConsistent` holds vacuously (no `i < 0`). ∎ (both branches)

By induction over `Machine::new`/`fix_piece`/`hold_piece`'s calls to `draw_once` (the only
call sites, §4/§5, `implementation.md` §5's "every `draw_once` call is one of these three"
observation), `TypeOK`/`BagNonEmpty`/`BagNextConsistent` hold in every reachable state.

**Note on `check_invariants`.** This section's `TypeOK`/`BagNonEmpty` conjuncts are exactly
what `t4::model::check_invariants` asserts at runtime (`implementation.md` §6.9); `next`'s
own well-formedness assertion there is the same `TypeOK` conjunct specialized to `next_`.
`BagNextConsistent` is **not** asserted at runtime (§6.9's own note) — the argument above is
`proofs.md`-only, needed for the refinement proof but not exposed as a runtime check, since
`bag_`'s full unbounded-function content (beyond the live `Vec` prefix) has no finite Rust
representation to check against in the first place (§2's mapping note).

---

## 7. `Machine::new(bags_fn, piece_source)` ≙ `Init bags H`

```rust
let checked_bags_fn = |i: u64| { let b = bags_fn(i); assert_piece_set::<P>(&b); b };
let (p, bag, next) = init_piece_and_draw::<P>(checked_bags_fn);
let m = Machine { s3: T3Machine::new(p, piece_source), bag, next };
```

`init_piece_and_draw` is `BuildInitNext` + `InitPieceAndDraw`'s literal loop translation
(`implementation.md` §4-T4b): its body's only state-mutating operation is `draw_once`,
proved to commute with `DrawNextPiece` in §6 above, called `NEXT_LEN + 1` times (`NEXT_LEN`
times in the loop, once more for the final draw), in the same order Rocq's `BuildNextInit`
recursion visits them — by induction on the loop count (base case: the loop's zero-length
prefix, trivially matching `BuildInitNext`'s own base case), the `(bag, next)` pair after
the loop equals `BuildInitNext`'s own result, and the one further `draw_once` call gives
`p` equal to `InitPieceAndDraw`'s selected piece, by §6's single-call commutation applied
to this specific call.

`H`'s per-index obligation (`T4.v`'s `Init` takes a single `H : PieceSet bagNew` per call to
`DrawNextPiece`/`BuildInitNext`, quantified implicitly over every index `BuildInitNext`'s
recursion visits) is realized as `checked_bags_fn`'s per-call `assert_piece_set`
(`implementation.md` §4-T4c) — every index `init_piece_and_draw` actually requests is
checked at the point of use, giving exactly the witness §6's reset-branch argument needs at
every reset this call sequence triggers.

`self.s3 := T3Machine::new(p, piece_source)`; by `t3/proofs.md` §7, `α₃(self.s3) =
T3.Init p`. Combined with the paragraph above, `α₄(Machine::new(bags_fn, piece_source)) =
T4.Init bags H` for the specific `p`/`bag`/`next` this call sequence produces — matching
Rocq's `Init bags H` exactly, since `T4.v`'s own `Init` is defined as this same
`InitPieceAndDraw` composition. Homomorphism condition 1 (§2). ∎

---

## 8. `check_axioms`/`check_invariants` correspondence

**`check_axioms`.** `T4.v` states exactly one axiom, `AxiomsMaxBagLen : MaxBagLen > 0`
(confirmed by direct inspection of `T4.v` — no `AxiomsNextLen` exists in the source,
`implementation.md` §6.8's note). `t4::model::check_axioms::<P>()` calls
`t1::model::check_axioms::<P>()` (covering every axiom `t1/proofs.md` §11 already
accounts for — T2/T3 add none of their own, `t2/proofs.md`/`t3/proofs.md` §8's own
correspondence sections), then asserts `!P::piece_all().is_empty()` — exactly
`AxiomsMaxBagLen` under `MaxBagLen = |Piece|` (§1). The further `P::NEXT_LEN > 0` assertion
in the same function is **not** a spec axiom (`implementation.md` §6.8 is explicit about
this) — it is the runtime precondition `next.front()`/`next.pop_front()` need to be
well-defined at all, stated separately in the function body specifically so it is never
mistaken for a `T4.v`-derived obligation in this proof or elsewhere.

**`check_invariants`.** `t4::model::check_invariants::<P>(s)` (i) calls
`t3::model::check_invariants(&s.s3)`, which by `t3/proofs.md` §8 checks exactly `T3.Correct
(s3 s)`'s conjuncts, and (ii)–(iv) assert `BagNonEmpty`, `bag`'s `TypeOK` conjuncts, and
`next`'s `TypeOK` conjuncts (§6 above). Together these are `T4.v`'s full state invariant
for `T4.Correct` restricted to what §6 characterizes as runtime-checkable — `T3.Correct (s3
s) ∧ TypeOK (draw s) ∧ BagNonEmpty (draw s)`, omitting only `BagNextConsistent` for the
reason §6's closing note states (no finite runtime representation of `bag_`'s
beyond-live-prefix content to check against), which remains a `proofs.md`-only conjunct
established by §6's induction rather than a runtime assertion. ∎

---

## 9. Coverage

Every `T4.v` `Definition`/`Record` name is accounted for above or in `implementation.md`'s
§3 naming map: `State`/`s3`/`bag_`/`next_`/`bagLen_`/`Draw` (§2), `NextLen`/`MaxBagLen`
(§1), `Bijective`/`PieceSet`/`H` (§4/§6/§7, realized as `is_piece_set`/`assert_piece_set`),
`ShiftNext` (§6, not emitted, realized inline), `DrawNextPiece` (§6), `BuildInitNext`/
`InitPieceAndDraw`/`Init` (§7), `Event`/`Next` (implicit, §3–§5, mirroring every prior
model's own `Next` shape), `UnchangedT4Part` (§3, not emitted, realized as "delegate and
leave `bag`/`next` untouched"), `MovePiece`/`RotatePiece`/`FixPiece`/`FallStep`/`HoldPiece`
(§3–§5), `TypeOK`/`BagNonEmpty`/`BagNextConsistent`/`Correct` (§6/§8), `fₑ`/`fₛ`/
`T4RefinesT3` (used throughout §3–§5 as the justification for reusing `t3/proofs.md`'s
action lemmas on **every** transition, unlike `t3/proofs.md`'s own `Event2`-restricted
reuse of `t2/proofs.md` — the scope note above). No `model.rs` behavior relies on anything
not accounted for above or, transitively, in `t3/proofs.md`, `t2/proofs.md`, and
`t1/proofs.md`. ∎
