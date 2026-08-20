# implementation.md — ImplementationInstructions for T4 (Rust)

Per-model instructions for the transformation

```
FormalModel (T4.v)  ×  ImplementationInstructions (this file)
      ── rocq-to-rust skill ──▶  Code (model.rs, view.rs, main.rs, instance.rs)
                                  ×  Proofs (proofs.md)  ×  Tests (tests/)
```

This file is the **T4-Rust-specific source of truth**, applying the `rocq-to-rust` skill's
general rules — in particular §7, "translating a module that wraps another" — to `T4.v`.
`t3/implementation.md` (and transitively `t2/implementation.md`/`t1/implementation.md`) are
the frozen sources of truth for everything T4 reuses unchanged; this file states only what
is specific to T4. Generated artifacts are never hand-edited: to change one, change this
file or `T4.v` and regenerate. All references to `T4.v`/`T3.v`/`T2.v`/`T1.v` are **by
definition name**.

## 0. Inputs, outputs, and what is frozen

Codegen-time inputs:
- `T4.v` — the abstract model (refines `T3.v` for every event — see §1).
- `T3.v`/`t3/implementation.md` (and transitively `T2.v`/`T1.v`) — reused in full.
- this file.
- the `rocq-to-rust` skill (cited as `skill §N`).

Runtime input (NOT codegen-time, NOT derived from `T4.v`):
- `t4/src/instance.rs` — implements `t4::model::Params` for `t1::instance::Tetris`, adding
  `NEXT_LEN` (§11, §13).

Outputs: `t4/src/model.rs`, `t4/src/view.rs`, `t4/src/main.rs`, `t4/src/instance.rs`,
`t4/Cargo.toml`, `t4/proofs.md`, `t4/tests/` (§9). A generation is **correct** iff
`model.rs` refines `T4.v` (established by `proofs.md`); the acceptance oracle (§10) is the
operational check that provides evidence for this, it is not itself the definition.

### 0.1 Files reused from `t1`/`t2`/`t3` unchanged (not regenerated, imported as path
dependencies)

| item | role in T4 |
|------|-----------|
| `t1::model::Params` | the parameter trait; `t4::model::Params` extends it (skill §7.4) — `NextLen` is T4's only new abstract parameter |
| `t3::model::Machine<P>` | the wrapped engine, reached as `self.s3` |
| `t3::model::{check_invariants}` | called directly, not re-implemented |
| `t2::view`/`t1::view` sub-procedures (`draw_panel`, `draw_banners`, `draw_grid`, `draw_background`, `draw_grid_lines`, `draw_piece`, `draw_game_over`, `draw_text_label`, `draw_block`, `panel_metrics`, `desired_panel_px`) | called directly by `t4::view`, exactly as `t3::view` already calls them |
| `t3::view::{Layout, compute_layout, draw_hold_box, Banner, RenderConstants}` | embedded/called by `t4::view` (§0.2 — requires a visibility patch) |
| `t1::instance::Tetris` | the concrete instance type; `t4::instance` adds a `t4::model::Params` impl for it rather than defining a new type (§11) |
| `t1::misc::{DAS_DELAY, ARR, window_conf, LogicalKeys, RepeatTimer, random_piece}` | `main.rs`-only primitives (§15.2 of `t1/implementation.md`); `t4/main.rs` imports them directly rather than re-declaring |
| `t3::misc::{Action, any_action_just_pressed}` | T3's six-variant `Action` (§15.1 of `t3/implementation.md`); reused verbatim (§15.1 below) since `T4.v` adds no new player-facing action |

`t4/src/model.rs` therefore contains exactly one new kind of state-machine logic: the
`bag`/`next` fields and the bag/preview mechanics (`DrawNextPiece`, `BuildInitNext`,
`InitPieceAndDraw`). Nothing in `t4` reimplements grid algebra, rotation, line clearing,
scoring, or the hold slot.

### 0.2 Required visibility on `t3/src/view.rs`

T4 needs `t3::view::Layout` (its fields), `t3::view::compute_layout`, and
`t3::view::draw_hold_box` to be `pub`, matching the convention `t2::view::Layout`/
`t1::view::Layout` already follow — a wrapper layer embeds them as its own `base`
(`t2/implementation.md` §14.2, `t3/implementation.md` §14.2). `t4::view::Layout` embeds
`t3::view::Layout` as `base`, and `t4::view::render` calls `t3::view::compute_layout`/
`draw_hold_box` directly (the same pattern `t3::view::render` already uses one layer down
on `t2::view`), rather than calling `t3::view::render()` as an opaque whole (which draws
only the left panel and returns nothing `t4` could splice a right panel into). Required
visibility, purely additive (no signature or behavior change):
- `pub struct Layout { pub base: t2::view::Layout, pub hold_label_y: f32, pub hold_box_top: f32, pub hold_box_size: f32, pub panel_top: f32 }`
- `pub fn compute_layout(...) -> Layout`
- `pub fn draw_hold_box<P: Params>(...)`

Also required, in `t2/src/view.rs`: `pub const PANEL_GRID_GAP_FRACTION` and
`pub fn desired_panel_px()`, so `t4::view` can size its right-side preview panel using the
identical gap fraction the left panel already uses (§14.2), instead of restating that
constant.

---

## 1. The refinement, and what it buys — and what it doesn't

`T4.State` embeds `T3.State` as `s3` and adds a `Draw` (`bag_`, `next_`).

Refinement mapping (`T4.v`'s `Refinement` section): `fₛ = s3 : T4.State → T3.State`. `fₑ`
maps every one of T4's five events into a T3 event, and is **state-dependent** for
`Fix`/`Fall`/`Hold` — the piece T3 needs is `next s 0`, read off the pre-transition state,
not carried in the T4 event itself (`T4.v`'s `fₑ` definition). Per skill §7.1's three-way
classification:

- **`move_piece`/`rotate_piece` — full uses.** `option_map (UnchangedT4Part s)` over the
  corresponding `T3` call (`T4.v`'s `MovePiece`/`RotatePiece`), `bag`/`next` untouched.
  `t3/proofs.md`'s action lemmas transfer unchanged.
- **`fix_piece` — partial use, with the piece supplied by T4.** Delegates to
  `T3.FixPiece (next s 0)` after popping/refilling the draw state (`T4.v`'s `FixPiece`).
  `t3/proofs.md`'s `fix_piece` argument transfers for the `s3` part; the new obligation is
  entirely about *which* piece is supplied (definitionally `next s 0`) and about
  `bag`/`next` mutation being conditioned on that call's success (§4-T4b).
- **`hold_piece` — partial use, plus one invariant-dependent hazard.** The
  `DrawNextPiece` call is skipped, not merely discarded, when `hold ≠ None` — safe only
  because `t3/proofs.md`'s `SwappedImplyHoldSome` (`swapped ⟹ hold ≠ None`) guarantees
  `hold = None ⟹ ¬swapped`, so T3's own guard can never reject a hold that reached the
  point of actually drawing (§4-T4c, imported rather than re-derived).

Unlike `t3/implementation.md` §1 (T3 wraps T2 for `Event2` only, `Hold` has no T2/T1
refinement claim at all), **T4 refines T3 for every one of its five events** — `T4.v`'s
`T4RefinesT3` quantifies over the whole `Event` type, not a restricted subset.

---

## 2. File layout & module shape

```
t4/
  Cargo.toml            # depends on t1, t2, t3 by path (workspace member)
  src/
    lib.rs               # pub mod instance; model; view — same role as t1's/t2's/t3's
    instance.rs           # impl t4::model::Params for t1::instance::Tetris (§11, §13)
    model.rs                # T4 engine: wraps t3::model::Machine, adds bag/next (§5–§7)
    view.rs                  # renderer: preview column (Next label, right panel) + t3's
                              #   hold box/grid/panel/banners (shifted only by symmetry, §14)
    main.rs                   # entry point: bag shuffle replaces single-piece randomness (§15)
  proofs.md              # refinement proof, delta over t3/proofs.md (§8)
  tests/
    test_instance.rs     # two fixture instances, NEXT_LEN = 3 and NEXT_LEN = 5 (§9)
    model_unit_test.rs
    model_properties_test.rs
    model_fuzz_test.rs
    oracle.rs             # executable T4.v reference (reuses t3's oracle for s3)
```

The workspace root (`Cargo.toml`, `members = ["t1", "t2", "t3", "t4"]`) is what makes
`t4/Cargo.toml`'s `t1`/`t2`/`t3` path dependencies resolve; `t1`, `t2`, `t3` remain
independently buildable, unmodified in behavior by T4's existence (only the two `pub`
visibility widenings of §0.2).

---

## 3. Naming map (`T4.v` → Rust)

Only T4-introduced names appear here; T1/T2/T3 names keep their own maps and are reached
through nested inner engines.

| `T4.v` | Rust |
|--------|------|
| `State` (record) | `t4::model::Machine<P>`; fields below |
| `s3` | `pub s3: t3::model::Machine<P>` |
| `Draw` (record) | flattened onto `Machine`, no nested struct — `bag`/`next` are ordinary fields directly on `t4::model::Machine<P>` |
| `bag_` | `pub bag: Vec<P::Piece>` — used as a stack (`.pop()`); no separate bound field |
| `bagLen_` | **not implemented** — `self.bag.len()` *is* it |
| `next_` | `pub next: VecDeque<P::Piece>` — length `P::NEXT_LEN`; `next_ 0` is `self.next.front()`. `VecDeque` rather than `Vec`: `ShiftNext` is a pop-front/push-back, and `VecDeque` gives that in O(1) instead of `Vec`'s O(n) `remove(0)` |
| `NextLen` | `Params::NEXT_LEN : i64` — a new trait item (§1 above, skill §7.4), a compile-time constant since every `Params` item here is compile-time |
| `MaxBagLen` | **not implemented as a separate parameter** — derived everywhere as `P::piece_all().len()`, avoiding a second source of truth for the piece-set's size |
| `Bijective`, `PieceSet` | `is_piece_set::<P>(arr: &[P::Piece]) -> bool` — length `== NUM_PIECES` + pairwise-distinct + `⊆ piece_all()`; bijectivity by pigeonhole |
| `H : PieceSet bagNew` | `assert_piece_set::<P>(arr)` — unconditional `assert!`, not gated by `CHECK_INVARIANTS` (this validates external input, it is not a maintained invariant of `Machine`'s own state — distinct from skill §4c's "invariant-maintained preconditions" rule) |
| `TypeOK` | not a single call in `check_invariants` — `bag` shrinks below `NUM_PIECES` mid-cycle, so `is_piece_set(bag)` is the wrong check; `check_invariants` asserts the representable analogue directly (§6.9) |
| `ShiftNext` | not emitted as a named function — realized inline as `next.pop_front(); next.push_back(p_new)` |
| `DrawNextPiece` | `draw_once::<P>(bag, next, bag_new)` (free function) / `Machine::draw_next_piece` (private method wrapping it) |
| `BuildInitNext` | `init_piece_and_draw`'s internal loop — not a separate emitted function, folded in (skill's `Fixpoint`→`for` idiom) |
| `InitPieceAndDraw`, `InitPiece` | `init_piece_and_draw::<P>(bags_fn)` (free function), called once from `Machine::new` |
| `Init` | `Machine::new(bags_fn, piece_source)` — `piece_source` has no `T4.v` counterpart (§6.1) |
| `Event` | implicit (five public `&mut self` methods, as T1–T3) |
| `UnchangedT4Part` | not emitted — realized by delegating then leaving `bag`/`next` untouched |
| `MovePiece`/`RotatePiece` | `Machine::move_piece(&mut self, dy, dx) -> bool` / `Machine::rotate_piece(&mut self, cw) -> bool` |
| `FixPiece` | `Machine::fix_piece(&mut self, bag_new: &[P::Piece]) -> bool` |
| `FallStep` | `Machine::fall_step(&mut self, bag_new: &[P::Piece]) -> bool` |
| `HoldPiece` | `Machine::hold_piece(&mut self, bag_new: &[P::Piece]) -> bool` |
| `Next` | not emitted — `main.rs`'s action dispatch already maps input → method |
| `BagNonEmpty` | not a runtime check on its own — a structural invariant of the stack representation, asserted as a cheap sanity check in `check_invariants` (§6.9) |
| `BagNextConsistent`, `Correct` | `proofs.md` only; not emitted |
| `fₑ`, `fₛ`, `InitRefineT3`, `NextRefineT3`, `RefineT3` | `proofs.md` only; not emitted |

---

## 4. Translation rules specific to T4

Every T1/T2/T3 rule (`t1/implementation.md` §4, `t2/implementation.md` §4,
`t3/implementation.md` §4) applies unchanged wherever T4 touches T1/T2/T3 state, reached
exclusively through `self.s3`'s methods. New T4-only points:

- **§4-T4a. `bag`/`next` as `Vec`/`VecDeque`, not function + bound.**
  ```rust
  // spec: DrawNextPiece d bagNew — mutates bag/next in place, returns (p, resetting)
  fn draw_once<P: Params>(
      bag: &mut Vec<P::Piece>,
      next: &mut VecDeque<P::Piece>,
      bag_new: &[P::Piece],
  ) -> (P::Piece, bool) {
      let resetting = bag.len() == 1;              // bagLen_ d <=? 1; BagNonEmpty ⟹ ≤1 ⟺ ==1
      let p = next.pop_front().expect("next non-empty (BuildInitNext/check_axioms)");
      next.push_back(bag.pop().expect("bag non-empty (BagNonEmpty)")); // ShiftNext ... (bag_ (bagLen_-1))
      if resetting {
          bag.clear();
          bag.extend_from_slice(bag_new);           // bagSingle branch: refill := bagNew
      }
      (p, resetting)
  }
  ```
  `resetting` is computed from `bag.len()` **before** the pop (matching `T4.v`'s
  `bagLen_ d <=? 1` reading the pre-state bound), the same ordering pitfall skill §4b warns
  about generally. `Machine::draw_next_piece` wraps this against `self.bag`/`self.next`,
  discarding `resetting` (only `init_piece_and_draw`'s bookkeeping needs it, §4-T4b).

- **§4-T4b. `init_piece_and_draw` — literal loop translation of `BuildInitNext` +
  `InitPieceAndDraw`.** Generic in `bags_fn`, not hardcoded to any particular bag-boundary
  count:
  ```rust
  fn init_piece_and_draw<P: Params>(
      mut bags_fn: impl FnMut(u64) -> Vec<P::Piece>,
  ) -> (P::Piece, Vec<P::Piece>, VecDeque<P::Piece>) {
      let mut bag = bags_fn(0);                      // length NUM_PIECES
      let filler = bag[0];                            // arbitrary — every next entry is
      let mut next: VecDeque<P::Piece> =               // overwritten within NEXT_LEN draws
          std::iter::repeat(filler).take(P::NEXT_LEN as usize).collect();
      let mut bag_idx: u64 = 1;
      for _ in 0..P::NEXT_LEN {
          let (_, resetting) = draw_once::<P>(&mut bag, &mut next, &bags_fn(bag_idx));
          if resetting {
              bag_idx += 1;
          }
      }
      let (p, _) = draw_once::<P>(&mut bag, &mut next, &bags_fn(bag_idx));
      (p, bag, next)
  }
  ```
  `bags_fn` must be **referentially consistent**: called more than once for the same index
  (every loop iteration shares a `bag_idx` until it advances) must return the *same*
  contents each time, matching `bags : ℕ → ℕ → Piece` being a pure function in Rocq. The
  type signature (`impl FnMut(u64) -> Vec<P::Piece>`) does not enforce this — the caller
  (`main.rs`'s memoizing closure, §15.2) is responsible.

- **§4-T4c. `H` — checked unconditionally, at every event boundary, before anything
  else.** `assert_piece_set::<P>` is called first in `fix_piece`, `fall_step` (via
  `fix_piece`'s re-check — accepted redundancy, `is_piece_set` is `O(NUM_PIECES)`),
  `hold_piece`, and inside `Machine::new`'s `bags_fn` wrapper. Each `Event` constructor in
  `T4.v` carries its own `H : PieceSet bagNew` precondition; checking independently at each
  call site is the direct realization of that, not an optimization opportunity to thread
  an "already checked" flag through.

- **§4-T4d. `fix_piece(bag_new)` — peek before the guard, commit only on success.**
  ```rust
  pub fn fix_piece(&mut self, bag_new: &[P::Piece]) -> bool {
      assert_piece_set::<P>(bag_new);                          // H
      let p = *self.next.front().expect("next non-empty");     // pure read — no mutation
      let fired = self.s3.fix_piece(p);                        // spec: T3.FixPiece (next s 0)
      if !fired {
          return false;           // zero mutation of bag/next — matches every other guard
      }
      self.draw_next_piece(bag_new);   // commit, now that fired is confirmed
      if CHECK_INVARIANTS {
          check_invariants(self);
      }
      true
  }
  ```
  `T4.v`'s `FixPiece` computes the popped `Draw` unconditionally via a Rocq `let` before
  `option_map`, but that's a value binding, not an observable effect: `option_map`
  discards it entirely on `None`. A stateful translation that mutated `bag`/`next` before
  knowing whether `self.s3.fix_piece(p)` succeeds would desync from every reachable `T4.v`
  state whenever `T3.FixPiece`'s own guard fails independently of `T4`'s call (e.g. via
  `fall_step` when `gameover` is already true) — the peek-then-commit ordering above avoids
  that, giving "guard fails ⟹ zero mutation" for `bag`/`next`, the property the
  stuttering-step arguments in `t1/proofs.md`–`t3/proofs.md` rely on and which `t4/proofs.md`
  must extend to these two new fields (§8).

- **§4-T4e. `fall_step(bag_new)`.** Disjoint-guard sequencing, identical shape to
  `t3::model::Machine::fall_step`:
  ```rust
  pub fn fall_step(&mut self, bag_new: &[P::Piece]) -> bool {
      if self.move_piece(-1, 0) {
          return true;
      }
      self.fix_piece(bag_new)   // re-checks bag_new (§4-T4c) — accepted redundancy
  }
  ```

- **§4-T4f. `move_piece`/`rotate_piece`.** One-line delegation to `self.s3`; `bag`/`next`
  untouched (full use, §1).

- **§4-T4g. `hold_piece(bag_new)`.**
  ```rust
  pub fn hold_piece(&mut self, bag_new: &[P::Piece]) -> bool {
      assert_piece_set::<P>(bag_new);                    // H
      if self.s3.s2.s1.gameover {
          return false;                                   // T4's own guard (T4.v's `if !gameover`)
      }
      let p2 = match self.s3.hold {
          Some(h) => h,
          None => self.draw_next_piece(bag_new),          // only branch that mutates bag/next
      };
      let fired = self.s3.hold_piece(p2);
      if !fired {
          return false;
      }
      if CHECK_INVARIANTS {
          check_invariants(self);
      }
      true
  }
  ```
  `self.s3.hold`/`self.s3.swapped` are read/written entirely inside `self.s3.hold_piece`
  (T3's own logic, `t3/implementation.md` §4-T3a-adjacent) — T4 does not duplicate T3's
  guard or field writes.

- **§4-T4h. Why `hold_piece` needs no further fix, unlike `fix_piece`.** Two separate
  claims:
  - **The `Some` (skip) branch matches the spec exactly, independent of any invariant.**
    `T4.v`'s `hold s := T3.hold (s3 s)` is a direct passthrough, so `T3.HoldPiece`'s
    internal `match hold s with Some p => p | None => p_new end` reads the *same* value
    `hold_piece` just tested — whichever branch T4 takes, T3 necessarily takes the
    corresponding one.
  - **The `None` (commit) branch cannot subsequently fail.** `T3.HoldPiece`'s guard is
    `¬gameover ∧ ¬swapped`. `¬gameover` is already established by the check three lines
    above. `¬swapped` is supplied by `t3/proofs.md`'s `SwappedImplyHoldSome`
    (`swapped ⟹ hold ≠ None`); its contrapositive, `hold = None ⟹ ¬swapped`, applies
    exactly in this branch. `t4/proofs.md` must cite this explicitly as an imported
    dependency (§8), not re-derive it.

---

## 5. Free functions emitted by `model.rs` (`T4.v` source order)

- `is_piece_set::<P>(arr: &[P::Piece]) -> bool` — realizes `Bijective`/`PieceSet` (§3).
- `assert_piece_set::<P>(arr: &[P::Piece])` — the runtime realization of `H`; `assert!`s
  unconditionally, independent of `CHECK_INVARIANTS` (§3).
- `draw_once::<P>(bag, next, bag_new) -> (P::Piece, bool)` — realizes `DrawNextPiece`,
  shared between `Machine::draw_next_piece` and `init_piece_and_draw`'s loop (§4-T4a/b).
- `init_piece_and_draw::<P>(bags_fn) -> (P::Piece, Vec<P::Piece>, VecDeque<P::Piece>)` —
  realizes `BuildInitNext` + `InitPieceAndDraw` (§4-T4b).

None of these are generic over the full `t4::model::Params` beyond what they read
(`P::NEXT_LEN`, `P::piece_all()`) — per skill §1's classification rule, no function here
needs anything from `t1::model::Params` beyond `Piece`'s associated type and
`piece_all()`, both inherited through the `Params: t1::model::Params` bound.

---

## 6. `t4::model::Params` and `t4::model::Machine<P>`

### 6.0 `Params` trait

```rust
// spec: NextLen (req-preview-len)
pub trait Params: t1::model::Params {
    const NEXT_LEN: i64;
}
```

Extends `t1::model::Params` directly (skill §7.4) — `T4.v` adds exactly one new abstract
parameter beyond `T1.v`'s (`MaxBagLen` is derived, not a parameter of its own, §3), so no
intermediate `T3Params`-style trait is introduced, matching `t3/implementation.md` §0.1's
own precedent of skipping such a trait when nothing new needs adding at that layer — here
something *does* need adding, so `t4::model::Params` is the first genuinely new trait in
this tower since `t1::model::Params` itself.

### 6.1 `Machine<P>` and constructor — `Init bags H` (`T4.v`)

```rust
pub struct Machine<P: Params> {
    pub s3: t3::model::Machine<P>,
    pub bag: Vec<P::Piece>,
    pub next: VecDeque<P::Piece>,
}

impl<P: Params> Machine<P> {
    /// spec: Init. `piece_source` has no `T4.v` counterpart — it exists purely to
    /// thread through to `t1::model::Machine::new`'s cosmetic initial-occupied-cell
    /// filler (`t1/implementation.md` §6.1), and is kept as its own parameter rather
    /// than folded into `bags_fn`: the two draw from unrelated domains (a single piece
    /// vs. a full bag permutation), and conflating them would make `bags_fn`'s contract
    /// (referential consistency per index, §4-T4b) harder to state cleanly.
    pub fn new(
        mut bags_fn: impl FnMut(u64) -> Vec<P::Piece>,
        piece_source: impl FnMut() -> P::Piece,
    ) -> Self {
        let checked_bags_fn = |i: u64| {
            let b = bags_fn(i);
            assert_piece_set::<P>(&b);   // H, realized per-index (§4-T4c)
            b
        };
        let (p, bag, next) = init_piece_and_draw::<P>(checked_bags_fn);
        let m = Machine {
            s3: t3::model::Machine::new(p, piece_source),   // spec: T3.Init p
            bag,
            next,
        };
        if CHECK_INVARIANTS {
            check_invariants(&m);
        }
        m
    }
    // ...
}
```

### 6.2–6.6 Actions

`move_piece`/`rotate_piece` — §4-T4f. `fix_piece` — §4-T4d. `fall_step` — §4-T4e.
`hold_piece` — §4-T4g, hazard note §4-T4h. Each of `fix_piece`/`hold_piece` runs
`check_invariants` when `CHECK_INVARIANTS` is set, matching every other public method;
`move_piece`/`rotate_piece` do **not** re-run it themselves (they delegate to
`self.s3.move_piece`/`rotate_piece`, which already runs `t3`'s own `check_invariants`
internally — running `t4`'s superset check again here would be redundant work on a hot,
unguarded path with no new field to verify, since `bag`/`next` are untouched by these two).

### 6.7 Read-through access

No new getters beyond what `t3::model::Machine`'s own public fields already expose
(`s3.gameover` is `s3.s2.s1.gameover`, etc., same nesting T3 itself uses, `t3/
implementation.md` §3's own convention) — `main.rs`/`view.rs` read `machine.s3.…` directly.

### 6.8 `check_axioms::<P>()`

```rust
/// spec: AxiomsMaxBagLen (`T4.v`'s *only* stated axiom — grep of `T4.v` confirms a
/// single `Axiom` block, no separate `AxiomsNextLen`). Composes
/// `t1::model::check_axioms::<P>()` (skill §7.4's "new items, delegate for the rest").
pub fn check_axioms<P: Params>() {
    t1::model::check_axioms::<P>();
    // AxiomsMaxBagLen: MaxBagLen > 0, MaxBagLen derived as NUM_PIECES (§3).
    assert!(
        !P::piece_all().is_empty(),
        "AxiomsMaxBagLen: NUM_PIECES (= |Piece|) must be > 0"
    );
    // NEXT_LEN > 0 is NOT a T4.v axiom — it is an implementation-level requirement
    // (next.front() must be Some at every fix_piece/fall_step/hold_piece call).
    // Stated here, separately from the assertion above, so the two are never
    // conflated as both being spec-derived.
    assert!(P::NEXT_LEN > 0, "NEXT_LEN must be > 0 (implementation requirement, not a T4.v axiom)");
}
```

Gated by `t4::model`'s own `pub const CHECK_AXIOMS: bool = true;` (§7), called once by
`main.rs` before the first `Machine<P>` is constructed, same convention `t1`/`t2`/
`t3::model` each follow for their own axiom sets.

### 6.9 `check_invariants::<P>(s)`

```rust
/// spec: `TypeOK`'s representable analogue, `BagNonEmpty`, plus `next`'s
/// well-formedness — layered on `t3::model::check_invariants`. Every conjunct is
/// `assert!`, not `debug_assert!` (independent of `--release`, per `t1/implementation.md`
/// D7's own reasoning, carried forward unchanged).
pub fn check_invariants<P: Params>(s: &Machine<P>) {
    t3::model::check_invariants(&s.s3);
    let num_pieces = P::piece_all().len();
    assert!(!s.bag.is_empty(), "BagNonEmpty failed");
    assert!(s.bag.len() <= num_pieces, "bag length bound failed");
    assert!(
        (0..s.bag.len()).all(|i| (i + 1..s.bag.len()).all(|j| s.bag[i] != s.bag[j])),
        "bag elements not pairwise distinct"
    );
    assert!(s.bag.iter().all(|p| P::piece_all().contains(p)), "bag ⊆ Piece failed");
    assert!(s.next.len() == P::NEXT_LEN as usize, "next length failed");
    assert!(s.next.iter().all(|p| P::piece_all().contains(p)), "next ⊆ Piece failed");
}
```

`TypeOK` is a claim about the unbounded Rocq `bag` function on `[0, MaxBagLen)`; `bag`
shrinks below `NUM_PIECES` mid-cycle (the common case), so `is_piece_set(&s.bag)` would
misfire whenever `s.bag.len() < num_pieces` — the four asserts above are the finite-prefix
invariant a valid piece set's prefix actually maintains.

### 6.10 `draw_next_piece` — private wrapper

```rust
impl<P: Params> Machine<P> {
    fn draw_next_piece(&mut self, bag_new: &[P::Piece]) -> P::Piece {
        draw_once::<P>(&mut self.bag, &mut self.next, bag_new).0
    }
}
```
Single-call-site-per-public-method pattern (skill §1's "state-but-non-action definitions →
private methods"); `resetting` discarded here, needed only inside `init_piece_and_draw`.

---

## 7. `t4::model`'s constants

```rust
pub const CHECK_AXIOMS: bool = true;        // module-level, as t1/t2/t3::model
pub const CHECK_INVARIANTS: bool = false;   // module-level, as t1/t2/t3::model
```
`CHECK_AXIOMS` gates the `check_axioms::<P>()` call in `main.rs` (§6.8); T4 states one
axiom (`AxiomsMaxBagLen`), so the flag is `true` here, same as `t1`/`t2`/`t3::model`.

---

## 8. `proofs.md` (scope)

Delta over `t3/proofs.md`.

1. **Scope.** Safety only. `RefineT3` has exactly two conjuncts (`InitRefineT3`,
   `NextRefineT3`) — no `None`-preservation clause, same Lynch & Vaandrager (*Information
   and Computation* 121(2):214–233, 1995, §3) justification `t3/proofs.md` already gives:
   only start/step conditions are required for a
   forward-simulation safety argument, and the converse (behavioral completeness) is
   actively false here — `T3.Fix` accepts an arbitrary piece per call, admitting traces
   ("`Fix X` forever") no reachable T4 state can produce once `bag` is forced to biject
   with `Piece`. Reference this, don't re-derive it.
2. **α.** `α_T4(rs) = { s3 := α_T3(rs.s3); bag := rs.bag; next := rs.next }` — apply
   `t3/proofs.md`'s `α_T3` to the embedded machine; `bag`/`next` map to the corresponding
   Rocq `ℕ → Piece` functions via the "array = bounded total function" pattern (skill §2,
   already used for T1's grids) — `Vec` index for `bag`, `VecDeque` position-from-front for
   `next`.
3. **`move_piece`/`rotate_piece` — full-use transfer**, one line each (§1, §4-T4f).
4. **`fix_piece`/`fall_step` — full-use transfer with a supplied piece, plus a
   stuttering-step obligation.** Two things beyond what transfers from `t3/proofs.md`: (a)
   the piece passed to `self.s3.fix_piece` equals `next s 0` at the pre-state —
   definitional (`self.next.front()` *is* the read of index 0, taken before any mutation);
   (b) guard failure implies zero mutation of `bag`/`next` — true by construction of
   §4-T4d's peek-then-commit ordering, needed to extend the stuttering-step argument
   `t1/proofs.md`–`t3/proofs.md` rely on to T4's own new fields.
5. **`hold_piece` — full-use transfer, plus two imported dependencies.** (a) The `Some`
   (skip) branch matches `T3.HoldPiece`'s own branch on the same field, independent of any
   T3 invariant. (b) The `None` (commit) branch's mutation can never precede a subsequent
   rejection: cite `t3/proofs.md`'s `SwappedImplyHoldSome`, contrapositive
   `hold = None ⟹ ¬swapped`, combined with the local `¬gameover` check. Both points argued
   in full at §4-T4h; state them here as imported facts.
6. **`TypeOK`/`BagNonEmpty`/`BagNextConsistent` preservation.** No T3 analogue; needs its
   own induction over `draw_once`'s two branches (reset / no-reset), checked against
   `BagNextConsistent`'s `k = min(MaxBagLen - bagLen, NextLen)` formula in each case.
   `TypeOK` preservation across a reset additionally needs `H`'s `PieceSet bagNew` —
   `assert_piece_set` (a runtime check) stands in for the Rocq proof term; state plainly
   that the obligation is *conditional on the check having passed*.
7. **`Init`.** `InitRefineT3` needs `T4.v`'s `unfold Init, InitPiece, InitPieceAndDraw;
   destruct (BuildInitNext ...)` to force both call sites' pair-destructuring to the same
   term before `reflexivity` applies — the Rust-side analogue is that `init_piece_and_draw`
   is called exactly once in `Machine::new` and its `p` is what seeds `t3::model::Machine`,
   so there is no Rust equivalent of the definitional-unfolding friction.
8. **Cap soundness — not applicable** (T4 introduces no new arithmetic on `score`/`combo`/
   `total_cleared_lines`).

---

## 9. Tests (`tests/`)

Mirror T3's suite (`t3/implementation.md`-equivalent §9) on the same fixture family, plus
T4-specific coverage.

- **`test_instance.rs`** — two fixture types, both built on the existing 2-piece
  `Piece::{Bar, Corner}` grid/rotation data (`t1/tests/test_instance.rs`, `include!`d, not
  copied):
  - `TestInstance` — `NEXT_LEN = 3`: short, hand-traceable, crosses exactly one bag
    boundary per `NEXT_LEN`-length draw sequence (`NUM_PIECES = 2`). Used by
    `model_unit_test.rs`/`oracle.rs` for exact golden-vector assertions.
  - `TestInstanceWide` — `NEXT_LEN = 5`: crosses at least two bag boundaries per full
    preview cycle. Used by `model_properties_test.rs`/`model_fuzz_test.rs`, so the
    property/fuzz suite exercises the reset branch of `draw_once` (§4-T4a) repeatedly
    within a single instance's lifetime, not just once at startup.
  Both `impl t4::model::Params` for the same underlying `TestInstance` piece/grid data —
  only `NEXT_LEN` differs, so `TestInstanceWide` is a thin second type, not a duplicated
  fixture (same `Piece` enum, rotation tables, grid dimensions).
- **`oracle.rs`** — reuses `t3`'s oracle for `s3`; independently hand-rolls
  `draw_once`/`init_piece_and_draw`-equivalents (a shared bug between translation and
  helper should still surface as a mismatch).
- **`model_unit_test.rs`** — golden vectors, hand-verified on `TestInstance`
  (`NEXT_LEN = 3`, `NUM_PIECES = 2`), the same method `T4.v`'s own worked-trace comments
  use (simulate `draw_once`/`init_piece_and_draw` by hand, assert the exact sequence):
  - `is_piece_set`/`assert_piece_set`: a malformed `bag_new` (wrong length, a duplicate)
    panics; a valid one doesn't.
  - Initial population: given two known bags, the resulting `bag`/`next`/current piece
    match hand-computed values (mirroring `BuildInitNext`'s own worked trace, on
    `TestInstance`, not `T4.v`'s 3-piece example).
  - `hold_piece`'s skip-vs-discard: firing a hold when `hold ≠ None` leaves `bag`/`next`
    byte-identical to before the call.
  - `fix_piece`'s guard-fail case (§4-T4d): calling `fix_piece` when the underlying
    `T3.FixPiece` guard is not satisfied leaves `bag`/`next` byte-identical to before the
    call — the property the peek-then-commit ordering exists to guarantee.
  - `fix_piece`/`fall_step` consume exactly one piece from `next` per *successful* call.
- **`model_properties_test.rs`** — `proptest`, on `TestInstanceWide`: `TypeOK`,
  `BagNonEmpty`, `BagNextConsistent` hold after every step (including across bag resets);
  `T3.Correct`'s conjuncts (delegated) hold after every step; differential oracle over
  every field, including `next`.
- **`model_fuzz_test.rs`** — same shape as T1–T3's: N seeds × M steps on
  `TestInstanceWide`, using the shared `Prng` fixture (`t1/tests/test_instance.rs`) to
  generate `bag_new`/`bags_fn` inputs via a real Fisher–Yates shuffle, structural + the new
  invariants + oracle differential.

---

## 10. Acceptance oracle

A regeneration is correct iff:
1. Every `T4.v` definition with a §3 mapping is realised; every "not emitted" entry is
   absent.
2. `model.rs` constructs the T3 engine via `t3::model::Machine::new`/its action methods
   and never reimplements any T1/T2/T3 free function.
3. `tests/` passes on both fixtures: unit + fuzz fully; properties under `proptest`.
4. The differential oracle agrees with `model.rs` on every field, including `next`, over
   every generated trace.
5. `assert_piece_set` is called, unconditionally, at the top of `fix_piece`, `fall_step`,
   `hold_piece`, and inside `Machine::new`'s `bags_fn` wrapper.
6. `hold_piece` never calls `draw_next_piece` when `self.s3.hold.is_some()`.
7. `fix_piece` reads `self.next.front()` before calling `self.s3.fix_piece`, and calls
   `self.draw_next_piece` only after that call is confirmed to have fired.
8. `check_invariants` asserts `TypeOK`'s representable analogue plus `BagNonEmpty`/`next`
   well-formedness, delegating to `t3::model::check_invariants` rather than reimplementing
   it.
9. `check_axioms::<P>()` calls `t1::model::check_axioms::<P>()` and asserts exactly
   `AxiomsMaxBagLen`'s derived form — no unstated extra spec axiom (§6.8's note on
   `AxiomsNextLen` not existing in `T4.v`).

---

## 11. Instantiation (`instance.rs`)

```rust
pub use t3::instance::{piece_color, Piece, Tetris};

impl t4::model::Params for t1::instance::Tetris {
    const NEXT_LEN: i64 = 6;
}
```
Legal under Rust's orphan rule: `Params` is local to the `t4` crate, so implementing it for
the foreign `Tetris` type is permitted regardless of `Tetris`'s crate of origin. `NextLen`
is a genuine new abstract parameter (`T4.v`'s `NextLen` parameter), not derivable from
`Piece` the way `MaxBagLen` is (§3), so it has no choice but to be supplied here — value
`6`, a reasonable preview depth for the real instance's 7-piece set.

---

## 12. Generator determinism rules

Inherit `t1/implementation.md` §12 / `t2/implementation.md` §12 / `t3/implementation.md`
§12's "reuse over restatement" verbatim, with the one addition of §0.2's `pub` widenings —
those are visibility-only, not behavior changes, so they don't reopen `t1`'s/`t2`'s/`t3`'s
own determinism guarantees.

---

## 13. `instance.rs` parameters

`NEXT_LEN = 6` (§11). Everything else inherited from `t1::instance::Tetris`'s existing
`Params` impl, untouched.

---

## 14. `view.rs` — renderer (preview column + `t3`'s hold box/grid/panel/banners)

`t4::view` does not redefine anything `t3::view`/`t2::view`/`t1::view` already provide
(§0.1); the caller-supplied `piece_color` closure convention (`t1/implementation.md`
§14.5) carries through unchanged. What's genuinely T4's own: `effective_row_range`,
`draw_preview`, and `compute_layout`'s right-panel geometry.

### 14.1 Public API

Same signature shape as `t3::view::render`, generic over `P: Params` (this crate's own
trait, so `P::NEXT_LEN` is directly available — no `RenderConstants` field needed for it,
since Rust's per-type `const` already carries it through the same `P` every other geometry
function here is already generic over).

```rust
pub use t3::view::RenderConstants;   // byte-identical fields, reused per §12
```

### 14.2 Two-panel geometry — symmetric margin, not a halved canvas budget

Rust's
`t1::view::compute_layout` sizes the grid **first**, against the full window, and
`t2::view`'s left panel is carved out of whatever margin that centering leaves
(`t1::view::Layout.origin_x`). Since the grid is horizontally centered, the right margin
is provably equal to `origin_x`:
```
right_margin = screen_width() - (origin_x + wm * cell_size)
             = screen_width() - ((screen_width() - wm*cell_size)/2 + wm*cell_size)
             = (screen_width() - wm*cell_size)/2 = origin_x
```
So the right (preview) panel can reuse the **same** `panel_width` already computed for the
left panel — no separate reservation, no patch to `t1::view`'s or `t2::view`'s sizing
math, and no restated `PANEL_FRACTION`/`PANEL_MIN_PX`/`PANEL_MAX_PX`:
```rust
fn compute_layout<P: Params>(constants: &RenderConstants) -> Layout {
    let base = t3::view::compute_layout(constants);        // pub (§0.2)
    let (min_row, max_row) = effective_row_range::<P>();
    let effective_rows = (max_row - min_row + 1) as f32;
    let panel_width = base.base.panel_width;                // same width, right side
    let m = t2::view::panel_metrics(panel_width);
    let cell_size = base.base.base.cell_size;
    let preview_cell_size = cell_size.min((panel_width - 2.0 * m.margin_x) / constants.pw as f32);
    let preview_gap = preview_cell_size;
    let preview_box_size = effective_rows * preview_cell_size;
    let top_gap = (constants.pw as f32 - 1.0 - max_row as f32) * preview_cell_size;
    let preview_label_y = m.margin_y;
    let preview_box_top = m.margin_y + m.label_font as f32 + top_gap;
    let available_h = constants.hm as f32 * cell_size - m.margin_y - m.label_font as f32 - top_gap - m.margin_y;
    let per_slot = preview_box_size + preview_gap;
    let preview_count = (((available_h + preview_gap) / per_slot).floor().max(0.0) as usize)
        .min(P::NEXT_LEN as usize);
    let desired = t2::view::desired_panel_px();             // pub (§0.2)
    let gap = desired * t2::view::PANEL_GRID_GAP_FRACTION;  // pub (§0.2) — same fraction as the left panel
    let right_origin = base.base.base.origin_x + constants.wm as f32 * cell_size + gap;
    Layout {
        base, right_origin, preview_label_y, preview_box_top,
        preview_cell_size, preview_gap, preview_box_size, preview_count,
        min_row, max_row,
    }
}
```
`Layout`'s fields stay private (module-internal) — T4 is not (yet) itself wrapped by
anything, so there's no present need to export further.

### 14.3 `effective_row_range::<P>()`

```rust
/// Union of occupied rows across every piece type at rotation 0. AxiomsRotGrid
/// (t1::model::check_axioms) guarantees every piece has ≥1 occupied cell at every
/// rotation, so min_row/max_row are always well-defined here.
fn effective_row_range<P: t1::model::Params>() -> (i64, i64) {
    let mut min_row = P::PW;
    let mut max_row = -1i64;
    for &p in P::piece_all() {
        let rg = P::rot_grid(p, 0);
        for y in 0..P::PW as usize {
            for x in 0..P::PW as usize {
                if rg[y][x].is_some() {
                    min_row = min_row.min(y as i64);
                    max_row = max_row.max(y as i64);
                }
            }
        }
    }
    (min_row, max_row)
}
```
Bound on `t1::model::Params` only (not `t4::model::Params`), since it reads no `NEXT_LEN`
— per skill §1's minimum-generic-bound rule.

### 14.4 `draw_preview`

```rust
/// spec: req-preview-len/pop, view-only rendering. Borderless — only piece blocks
/// are drawn, no strokeRect, unlike the hold box (t3/implementation.md §14.4).
/// Truncation past `layout.preview_count` is silent, matching the hold box's own
/// clip/clamp precedent rather than a new failure-visibility convention.
fn draw_preview<P: Params>(
    constants: &RenderConstants,
    layout: &Layout,
    next: &VecDeque<P::Piece>,
    piece_color: &impl Fn(P::Piece) -> [f32; 4],
    font: Option<&Font>,
) {
    let m = t2::view::panel_metrics(layout.base.base.panel_width);
    let x = layout.right_origin + m.margin_x;
    t2::view::draw_text_label("Next", x, layout.preview_label_y, m.label_font, t2::view::LABEL_COLOR, font);

    for (i, &p) in next.iter().take(layout.preview_count).enumerate() {
        let rg = P::rot_grid(p, 0);   // always rotation 0, as the hold box
        let [r, g, b, a] = piece_color(p);
        let color = Color::new(r, g, b, a);
        let box_y = layout.preview_box_top + i as f32 * (layout.preview_box_size + layout.preview_gap);
        for y in 0..constants.pw as usize {
            for xx in 0..constants.pw as usize {
                if rg[y][xx].is_none() {
                    continue;   // exact-sentinel test, not truthiness
                }
                let cx = x + xx as f32 * layout.preview_cell_size;
                let cy = box_y + (layout.max_row - y as i64) as f32 * layout.preview_cell_size;
                t2::view::draw_block(cx, cy, layout.preview_cell_size, color);
            }
        }
    }
}
```
A **uniform** slot height (`layout.preview_box_size`, the global max over all piece types
via `effective_row_range`), not a per-piece variable one — a per-piece height would make
`preview_count` depend on which pieces are actually queued, a jumpy, frame-to-frame
varying layout; every other geometry quantity here is a pure function of `constants`/`P`
alone.

### 14.5 Call order inside `render`

```rust
pub fn render<P: Params>(
    constants: &RenderConstants,
    machine: &Machine<P>,
    piece_color: impl Fn(P::Piece) -> [f32; 4],
    banner: Option<&t3::view::Banner>,
    font: Option<&Font>,
) {
    let layout = compute_layout::<P>(constants);
    clear_background(t2::view::BG_COLOR);
    t3::view::draw_hold_box(constants, &layout.base, &machine.s3, &piece_color, font);   // pub (§0.2)
    let below_level_y = t2::view::draw_panel(&layout.base.base, &machine.s3.s2, layout.base.panel_top, font);
    t2::view::draw_banners(&layout.base.base, below_level_y, banner, font);
    draw_preview::<P>(constants, &layout, &machine.next, &piece_color, font);
    t2::view::draw_grid(&machine.s3.s2.s1.mg, constants, &layout.base.base.base, &piece_color);
    t2::view::draw_background(constants, &layout.base.base.base);
    t2::view::draw_grid_lines(constants, &layout.base.base.base);
    t2::view::draw_piece(&machine.s3.s2, constants, &layout.base.base.base, &piece_color);
    if machine.s3.s2.s1.gameover {
        t2::view::draw_game_over(constants, &layout.base.base, font);
    }
}
```
`layout.base.base.base` is `t1::view::Layout` — expected depth-4 nesting
(`t4::view::Layout.base` = `t3::view::Layout`, `.base` = `t2::view::Layout`, `.base` =
`t1::view::Layout`), one level deeper than T3's own `layout.base.base`, consistent with one
more wrapping layer. `draw_preview` is called between `draw_banners` and `draw_grid`: whole-
canvas clear (`clear_background`, not `t1::view::draw_background`, the forbidden-zone tint —
see that file's own doc-comment disambiguation, `t1/implementation.md`) → hold box → panel →
banners → preview column → locked blocks → forbidden-zone tint → grid lines → falling piece
→ game-over overlay if applicable.

---

## 15. `main.rs` — entry point

Extends `t3/implementation.md` §15's shape. `Action` itself is `t3::misc::Action`
(`t3/implementation.md` §15.1), reused verbatim — `T4.v` adds no new player-facing action,
only changes what `Down`/`Hold` (and the per-tick fall) supply as their piece-source
argument, which is `fire`'s concern (§15.3), not `Action`'s.

### 15.1 `shuffle_bag` — replaces `random_piece` at every T4 action call site

```rust
/// spec: req-preview-init's "fair" randomization source. Fisher–Yates over the full
/// `P::piece_all()` (length NUM_PIECES) — produces a fresh permutation, not a single
/// piece. `random_piece::<P>()` (`t1::misc`'s, §15.2 of `t1/implementation.md`) is kept
/// only for `Machine::new`'s `piece_source` parameter (§6.1) — nothing in T4's own
/// actions needs a single uniformly-random piece.
fn shuffle_bag<P: Params>() -> Vec<P::Piece> {
    let mut a: Vec<P::Piece> = P::piece_all().to_vec();
    for i in (1..a.len()).rev() {
        let j = macroquad::rand::gen_range(0usize, i + 1);
        a.swap(i, j);
    }
    a
}
```

### 15.2 `make_bags_fn` — `bags_fn` construction for `Machine::new`

```rust
/// spec: §4-T4b's referential-consistency requirement, satisfied by memoization.
/// A fresh closure per game (called at startup and at every restart) — not a
/// module-level cache, so bags never leak across restarts.
fn make_bags_fn<P: Params>() -> impl FnMut(u64) -> Vec<P::Piece> {
    let mut bags: Vec<Vec<P::Piece>> = Vec::new();
    move |i: u64| {
        let i = i as usize;
        while bags.len() <= i {
            bags.push(shuffle_bag::<P>());
        }
        bags[i].clone()
    }
}
```

### 15.3 `fire` — `bag_new` replaces `p_new`

```rust
fn fire<P: Params>(action: Action, machine: &mut Machine<P>) {
    match action {
        Action::Left => { machine.move_piece(0, -1); }
        Action::Right => { machine.move_piece(0, 1); }
        Action::Down => { machine.fall_step(&shuffle_bag::<P>()); }
        Action::Cw => { machine.rotate_piece(true); }
        Action::Ccw => { machine.rotate_piece(false); }
        Action::Hold => { machine.hold_piece(&shuffle_bag::<P>()); }
    }
}
```
A free function, not a method on `Action` (`t1::misc`'s own note, §15.2 of
`t1/implementation.md`, on why `Action` excludes `fire`): `t4::model::Machine::fall_step`/
`hold_piece` take `&[P::Piece]`, not `P::Piece` (§6.2–6.6), so `t4/main.rs`'s `fire` cannot
be the same function as `t3/main.rs`'s even though both switch on the same `t3::misc::
Action`. A fresh `shuffle_bag::<P>()` per call — most calls discard it
(`self.bag.len() > 1`), an accepted cost: shuffling is cheap relative to a frame's own
work, and computing it unconditionally is simpler than threading a "will this actually
draw" check through every call site first. The per-tick gravity fall likewise calls
`machine.fall_step(&shuffle_bag::<Instance>())`.

### 15.4 No `assert_piece_set` catch — uncaught by design

Nothing in `main.rs` wraps a `fix_piece`/`fall_step`/`hold_piece`/`Machine::new` call in a
`std::panic::catch_unwind`. An `assert_piece_set` failure (which, given `shuffle_bag`'s
correctness, should never actually fire) propagates as a normal Rust panic — full
backtrace (with `RUST_BACKTRACE=1`), no swallowed-and-continued session.

### 15.5 Everything else

`window_conf`, `LogicalKeys`, `RepeatTimer`, `random_piece`, `DAS_DELAY`/`ARR` are
`t1::misc`'s; `Action`/`any_action_just_pressed` are `t3::misc`'s (§0.1 above) — all
imported, none re-declared. `process_input`'s DAS/ARR engine, `RunState`/`after_action`
(level-change rescheduling, banner capture/expiry), restart-on-gameover, and font loading
are `t4/main.rs`'s own, carrying over unchanged in shape from `t3/implementation.md` §15 —
generic over `t4::model::Machine<P>` instead of `t3::model::Machine<P>`, since `fire` and
`process_input` must call the T4 wrapper's methods, and a T4-restart goes through
`Machine::new(make_bags_fn::<P>(), random_piece::<P>)` rather than `t3::model::Machine::new`
directly. `process_input` is not itself shared via any `misc` module — `t1/implementation.md`
§15.5's note on why applies here most directly: it's `t4::model::Machine`'s own
`fall_step`/`hold_piece` signature (§6.2–6.6) that rules out a shared dispatch trait.
