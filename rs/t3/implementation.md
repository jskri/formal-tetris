# implementation.md — ImplementationInstructions for T3 (Rust)

Per-model instructions for the transformation

```
FormalModel (T3.v)  ×  ImplementationInstructions (this file)
      ── rocq-to-rust skill ──▶  Code (model.rs, view.rs, main.rs, instance.rs)
                                  ×  Proofs (proofs.md)  ×  Tests (tests/)
```

This file is the **T3-Rust-specific source of truth**, applying the `rocq-to-rust` skill's
general rules — in particular §7, "translating a module that wraps another" — to `T3.v`.
`t2/implementation.md` and `t1/implementation.md` are the frozen sources of truth for
everything T3 reuses unchanged; this file states only what is specific to T3. Generated
artifacts are never hand-edited: to change one, change this file or `T3.v` and regenerate.
All references to `T3.v`/`T2.v`/`T1.v` are **by definition name**, so renaming/reordering in
any of the three models is caught by the coverage check (§10), not silently mismatched line
numbers.

## 0. Inputs, outputs, and what is frozen

Codegen-time inputs:
- `T3.v` — the abstract model (refines `T2.v` for `Event2` events only — see §1).
- `T2.v`/`t2/implementation.md` and `T1.v`/`t1/implementation.md` — reused in full.
- this file.
- the `rocq-to-rust` skill (cited as `skill §N`).

Runtime input (NOT codegen-time, NOT derived from `T3.v`):
- `t3/src/instance.rs` — re-exports `t1::instance`'s `Params` implementation (§11, §13):
  `T3.v` introduces no new abstract parameters, so there is nothing new to instantiate.

Outputs: `t3/src/model.rs`, `t3/src/view.rs`, `t3/src/main.rs`, `t3/src/instance.rs`,
`t3/Cargo.toml`, `t3/proofs.md`, `t3/tests/` (§9). A generation is **correct** iff
`model.rs` refines `T3.v` (established by `proofs.md`); the acceptance oracle (§10) is the
operational check that provides evidence for this, it is not itself the definition.

### 0.1 Files reused from `t1`/`t2` unchanged (not regenerated, imported as path dependencies)

| item | role in T3 |
|------|-----------|
| `t1::model::Params` | the parameter trait; `t3::model::Machine<P>` bounds on it directly — no `T3Params` wrapper trait exists, since neither T2 nor T3 add parameters (skill §7.4) |
| `t1::model::Machine<P>` | the innermost engine, reached as `self.s2.s1` |
| `t1::model::new_piece_state::<P>` | `HoldPiece`'s one piece of non-trivial logic (§4-T3a) — already present in `t1::model`: no prerequisite patch to `t1/model.rs` is needed here, since `new_piece_state` mutates a `&mut Machine<P>` in place and was already emitted as one of T1's "helpers for refining models", `t1/implementation.md` §6, with no call site inside `T1.v`/`T1Proofs.v`'s own actions but a full `proofs.md` lemma nonetheless |
| `t2::model::Params` (alias of `t1::model::Params`) / `t2::model::Machine<P>` | the middle engine; `t3::model::Machine<P>` holds one as its `s2` field |
| `t2::model::{check_invariants}` | called directly, not re-implemented |
| `t1::instance::Tetris` | the concrete `Params` impl; re-exported through `t2::instance` and then `t3::instance` (§11) |
| `t1::misc::{DAS_DELAY, ARR, window_conf, LogicalKeys, RepeatTimer, random_piece}` | `main.rs`-only primitives (§15.2 of `t1/implementation.md`); `t3/main.rs` imports them directly rather than re-declaring |

`t3/src/model.rs` therefore contains exactly one new kind of logic: the `hold`/`swapped`
fields and `HoldPiece`'s field-update sequence. There is exactly one copy of the T1 and T2
engines in the workspace; nothing in `t3` reimplements grid algebra, rotation, line
clearing, or scoring.

---

## 1. The refinement, and what it buys — and what it doesn't

`T3.State` embeds `T2.State` as `s2` and adds `hold : option Piece`, `swapped : bool`.

Refinement mapping (`T3.v`'s `Refinement` section): `fₑ = id : T2.Event → T2.Event`,
`fₛ = s2 : T3.State → T2.State`. **The refinement holds only for `Event2` events**
(`T3.v`'s own `T3RefinesT2` definition quantifies only over `T2.Event`, wrapped by
`Event2`) — `Hold` has **no** T2/T1 refinement claim at all. Consequence, per skill §7.1's
three-way classification:

- **`move_piece`, `rotate_piece` — full uses.** `T3.MovePiece`/`RotatePiece` are
  `option_map (UnchangedT3Part s)` over the corresponding `T2` call, nothing else —
  `hold`/`swapped` are left alone, not even re-written to the same value. `T2`'s own action
  proofs (`t2/proofs.md`) transfer unchanged.
- **`fix_piece` — partial use.** `T3.FixPiece` delegates to `T2.FixPiece` *and* writes
  `swapped := false` (req-hold-limit) — `hold` is left alone. Only the `swapped` write is
  new; `t2/proofs.md`'s `fix_piece` argument transfers for the `s2` part.
- **`hold_piece` — no use.** No `T2` or `T1` *action* is invoked at all
  (`new_piece_state` is a free function, not an action — using it doesn't make this a
  "use" in the skill's sense, skill §7.1). `T1.Correct`/`T2.Correct`/`LevelCorrect`
  preservation across `Hold` must be argued fresh (§8.5), not inherited.

---

## 2. File layout & module shape

```
t3/
  Cargo.toml            # depends on t1, t2 by path (workspace member)
  src/
    lib.rs               # pub mod instance; misc; model; view — same role as t1's/t2's lib.rs
    instance.rs          # re-exports t2::instance's Params impl (§11, §13)
    model.rs              # T3 engine: wraps t2::model::Machine, adds hold/swapped (§5–§7)
    view.rs                # renderer: hold box (new) + t2's panel/banners (shifted) + grid (§14)
    misc.rs                # T3's six-variant Action (`Hold` added), reused by t4/main.rs (§15.1)
    main.rs                 # entry point: hold/swap action, fall speed and banner timing
                             # inherited from t2's shape (§15)
  proofs.md              # refinement proof, delta over t2/proofs.md (§8)
  tests/
    test_instance.rs     # test fixture — include!s t1's (T3 has no new params)
    model_unit_test.rs
    model_properties_test.rs
    model_fuzz_test.rs
    oracle.rs             # executable T3.v reference (reuses t2's oracle for s2)
```

The workspace root (`Cargo.toml`, `members = ["t1", "t2", "t3"]`) is what makes
`t3/Cargo.toml`'s `t1 = { path = "../t1" }` / `t2 = { path = "../t2" }` dependencies
resolve; `t1` and `t2` remain independently buildable, unmodified by T3's existence.

---

## 3. Naming map (`T3.v` → Rust)

Only T3-introduced names appear here; T1/T2 names keep their own maps and are reached
through nested inner engines.

| `T3.v` | Rust |
|--------|------|
| `State` (record) | `t3::model::Machine<P>`; fields below |
| `s2` | `pub s2: t2::model::Machine<P>` |
| `hold` | `pub hold: Option<P::Piece>` |
| `swapped` | `pub swapped: bool` |
| `gameover` (helper) | not a stored field — read as `self.s2.s1.gameover` at call sites, same convention `t2/implementation.md` §6.6 uses for its own `gameover` |
| `p` (helper) | not emitted as a method — single internal call site (`hold_piece`'s step 1), inlined as `self.s2.s1.p` |
| `Init` | `Machine::new` |
| `Event` | implicit (five public `&mut self` methods, as in T1/T2) |
| `UnchangedT3Part` | not emitted — realized by delegating then leaving `hold`/`swapped` untouched |
| `MovePiece` | `Machine::move_piece(&mut self, dy, dx) -> bool` |
| `RotatePiece` | `Machine::rotate_piece(&mut self, cw) -> bool` |
| `FixPiece` | `Machine::fix_piece(&mut self, p_new) -> bool` |
| `FallStep` | `Machine::fall_step(&mut self, p_new) -> bool` |
| `HoldPiece` | `Machine::hold_piece(&mut self, p_new) -> bool` |
| `NewPieceState` | not redefined — reached as `t1::model::new_piece_state::<P>` (§4-T3a) |
| `NextT2Event`, `Next` | not emitted — `main.rs`'s action dispatch already maps input → method |
| `fₑ`, `fₛ` | not emitted |
| `score`, `level`, `clearedLines` (T3-level read-through helpers) | `proofs.md` only; not emitted as functions — call sites read the underlying fields directly (`self.s2.score`, etc.) |
| `SwappedImplyHoldSome`, `GameoverImplyNotSwapped`, `Correct`, `NonDecreasingScore`, `NonDecreasingLevel`, `ScoreRisesOnClear`, `HoldMonotone`, `CorrectStep` | `proofs.md` only; not emitted |

---

## 4. Translation rules specific to T3

Every T1/T2 rule (`t1/implementation.md` §4, `t2/implementation.md` §4) applies unchanged
wherever T3 touches T1/T2 state, reached exclusively through `self.s2`'s methods. New
T3-only points:

- **§4-T3a — `new_piece_state` is reached through `t1::model`, not redefined.**
  `HoldPiece`'s call to `NewPieceState p2 (s1 s2_)` (`T3.v`) is realized as
  `t1::model::new_piece_state::<P>(p2, &mut self.s2.s1)` — an in-place mutation of the
  innermost `Machine<P>` (§0.1), matching D13's "fusion is mandatory, no fresh allocation
  into a uniquely-owned field" rule already applied throughout T1. Per "reuse over
  restatement" (`t2/implementation.md` §12): this logic is *owned* by `T1.v`, so if
  `T1.v`'s spawn rule ever changes, only `t1::model` needs updating, and every wrapper
  inherits the fix — the same rationale `t2/implementation.md` §4-T2a gives for reusing
  `t1::model`'s own `cleared_lines` field instead of re-deriving it.
- **§4-T3b — `move_piece`/`rotate_piece` are one-line delegations to `self.s2`;**
  `hold`/`swapped` untouched (full use, §1).
- **§4-T3c — `fix_piece` delegates to `self.s2.fix_piece(p_new)`, then sets
  `self.swapped = false`** from the post-call state (req-hold-limit: holding is allowed
  again after fixing); `hold` untouched (partial use, §1).
- **§4-T3d — `fall_step`** — same disjoint-guard sequencing as T1/T2 (skill §6.4): try
  `move_piece(-1, 0)`, else `fix_piece(p_new)`.
- **§4-T3e — `hold_piece`** — the only non-trivial T3 logic, kept at code level (same
  rationale `t2/implementation.md` §6.4 gives for `fix_piece`: the exact field-write
  ordering *is* the content, not just prose):
  ```rust
  // spec: HoldPiece
  pub fn hold_piece(&mut self, p_new: P::Piece) -> bool {
      if !(!self.s2.s1.gameover && !self.swapped) {
          return false; // real guard (req-hold-limit)
      }
      let p2 = self.hold.unwrap_or(p_new);              // req-hold-swap / req-hold-empty
      let old_p = self.s2.s1.p;                          // 1: read BEFORE overwritten
      t1::model::new_piece_state::<P>(p2, &mut self.s2.s1); // spec: NewPieceState p2 (s1 s2_) — in place
      self.hold = Some(old_p);                            // 2: req-hold
      self.swapped = true;                                 // 3: req-hold-limit
      if CHECK_INVARIANTS {
          check_invariants(self);
      }
      true
  }
  ```
  **Ordering note (skill §4b):** step 1 reads `self.s2.s1.p` before `new_piece_state`
  overwrites it — the one hazard, mirroring `T3.v`'s `hold := Some (p s)` reading the
  pre-state `p s`, not the value `NewPieceState` just wrote. Because `new_piece_state`
  mutates in place (§0.1, §4-T3a), `old_p` **must** be captured in a local binding before
  the call — there is no post-call state left to read it from afterward, since
  `new_piece_state` writes in place rather than returning a fresh value. `score`/`level`/
  `combo`/`perfect_clear`/`total_cleared_lines` (on `self.s2`) are not touched at all,
  matching `T3.v`'s own `T2.UnchangedT2Part` use inside `HoldPiece` — no field of `self.s2`
  other than `s1` is written.
- **§4-T3f — `p` (the `T3.v` helper)** has one call site (§4-T3e step 1) and is inlined
  there as `self.s2.s1.p`, not emitted as a named method — not worth a wrapper for a
  single internal read (contrast with `t2/implementation.md` §6.6's `gameover`, which
  `main.rs` also needs at several call sites but which likewise gets no wrapper, per that
  section's own rationale: Rust has no property-getter sugar that would make a wrapper
  read any more naturally than the direct field chain does).

---

## 5. Free functions emitted by `model.rs` (`T3.v` source order)

None. `T3.v` defines no non-state free function of its own (`UnchangedT3Part` is a
state-constructor helper, not emitted — same "not emitted, realized by delegating"
treatment `t2/implementation.md` gives `UpdateS1`). `model.rs` reaches `new_piece_state`
via `t1::model::new_piece_state::<P>` (§4-T3a) — not redefined.

---

## 6. `t3::model::Machine<P: Params>`

```rust
pub struct Machine<P: Params> {
    pub s2: t2::model::Machine<P>,   // spec: s2
    pub hold: Option<P::Piece>,       // spec: hold
    pub swapped: bool,                // spec: swapped
}
```

No `PhantomData<P>` marker: `s2: t2::model::Machine<P>` already mentions `P`. `Params`
here is `t1::model::Params`, imported and used directly (§0.1) — there is no
`t2::model::Params`/`t3::model::Params` trait to speak of, since neither wrapper layer
adds a parameter (skill §7.4).

### 6.1 Constructor — `Init p` (`T3.v`)

```rust
// spec: Init
pub fn new(p0: P::Piece, piece_source: impl FnMut() -> P::Piece) -> Self {
    Machine {
        s2: t2::model::Machine::new(p0, piece_source), // spec: T2.Init p
        hold: None,                                     // spec: None
        swapped: false,
    }
}
```

### 6.2 `move_piece(dy, dx)` — `MovePiece` (`T3.v`) — full use

```rust
// spec: MovePiece — delegate; hold/swapped untouched
pub fn move_piece(&mut self, dy: i64, dx: i64) -> bool {
    self.s2.move_piece(dy, dx)
}
```

### 6.3 `rotate_piece(cw)` — `RotatePiece` (`T3.v`) — full use

```rust
// spec: RotatePiece — delegate; hold/swapped untouched
pub fn rotate_piece(&mut self, cw: bool) -> bool {
    self.s2.rotate_piece(cw)
}
```

### 6.4 `fix_piece(p_new)` — `FixPiece` (`T3.v`) — partial use

```rust
// spec: FixPiece
pub fn fix_piece(&mut self, p_new: P::Piece) -> bool {
    let fired = self.s2.fix_piece(p_new); // spec: T2.FixPiece — mutates self.s2 in place
    if !fired {
        return false;
    }
    self.swapped = false; // req-hold-limit: holding is allowed again after fixing
    if CHECK_INVARIANTS {
        check_invariants(self);
    }
    true
}
```

### 6.5 `fall_step(p_new)` — `FallStep` (`T3.v`)

```rust
// spec: FallStep
pub fn fall_step(&mut self, p_new: P::Piece) -> bool {
    if self.move_piece(-1, 0) {
        return true; // spec: T3.MovePiece (-1) 0 — delegate
    }
    self.fix_piece(p_new) // spec: T3.FixPiece — full §6.4 logic
}
```

Guards are mutually exclusive exactly as in T1/T2 (skill §6.4): the inner move-branch and
fix-branch never both fire.

### 6.6 `hold_piece(p_new)` — `HoldPiece` (`T3.v`) — see §4-T3e for the frozen body.

### 6.7 `gameover`, `level`, `total_cleared_lines`, `combo`, `perfect_clear`, `score` —
controller reads, not stored T3 fields

As `t2/implementation.md` §6.6: no wrapper methods. `main.rs` reads
`machine.s2.s1.gameover`, `machine.s2.level`, `machine.s2.total_cleared_lines`,
`machine.s2.combo`, `machine.s2.perfect_clear`, `machine.s2.score` directly. `t1::Machine`
itself is reached one hop further than in `t2::main`, matching the extra layer of
nesting — no flattening accessor is introduced for it, since Rust's field-chain syntax
(`self.s2.s1.p`) already reads as directly as a wrapper method would; Rust callers hold
`&Machine<P>` directly, with no copied plain-data snapshot layer to flatten for.

### 6.8 `check_invariants` (default off, per `t1/implementation.md` D7)

```rust
// spec: T3.Correct's two new conjuncts (SwappedImplyHoldSome, GameoverImplyNotSwapped),
// on top of T2's Correct — delegates for everything s2-shaped.
pub fn check_invariants<P: Params>(s: &Machine<P>) {
    t2::model::check_invariants(&s.s2);
    debug_assert!(!s.swapped || s.hold.is_some());       // SwappedImplyHoldSome
    debug_assert!(!s.s2.s1.gameover || !s.swapped);       // GameoverImplyNotSwapped
    // `hold ∈ Piece ∪ {None}` is a type-level fact of `Option<P::Piece>` (skill §4h,
    // same category as T1's D8) — no runtime assertion needed, unlike a representation
    // that could hold an out-of-range sentinel.
}
```

---

## 7. `check_axioms`

`T3.v` adds no `Axiom` block, so `t3::model::check_axioms::<P>()` asserts nothing of its
own; it calls `t2::model::check_axioms::<P>()` and returns (which in turn calls
`t1::model::check_axioms::<P>()`, §7 of `t2/implementation.md`). `t3::model` also declares
its own `pub const CHECK_AXIOMS: bool = true;` (module-level, alongside `CHECK_INVARIANTS`,
§0.1), and `main.rs` gates on `model::CHECK_AXIOMS`/`model::check_axioms::<Instance>()` —
`t3::model`'s own items — once, before constructing any `Machine<P>`.

---

## 8. `proofs.md` (scope)

1. **Scope.** Safety only (no liveness). Additionally, structurally (not just "out of
   `main.rs`-scope" the way fall-speed/banners are): `Hold` has **no** refinement claim in
   `T3.v` itself (§1) — this isn't a codegen choice to argue around, it's what the model
   states.
2. **α.** `α_T3(rs) = { s2 := α_T2(rs.s2); hold := rs.hold; swapped := rs.swapped }` —
   apply `t2/proofs.md`'s `α_T2` to the embedded inner machine; `hold`/`swapped` map
   directly (`Option<P::Piece>` under the same `Piece` coercion T1's `α` already uses /
   plain `bool`, no further coercion).
3. **`move_piece`/`rotate_piece` — full-use transfer**, one line each (§1).
4. **`fix_piece` — partial-use transfer** for the `s2` part; `swapped := false` is the
   only new field write (§4-T3c), trivially matches `T3.FixPiece`'s explicit field.
5. **`hold_piece` — no-use, full fresh argument:**
   - Guard: `!self.s2.s1.gameover && !self.swapped` — both native T3 reads, matching
     `T3.v`'s own `HoldPiece` guard, `! (gameover s) && ! (swapped s)`.
   - **`T1.Correct (s1 (s2 s))` preservation across `Hold`.** Checking `T1.v`'s five
     `Correct` conjuncts against what `new_piece_state` actually touches (`p, py, px, pr`
     only — confirmed by its definition, `t1/src/model.rs`): `TypeOK`, `Gameover`,
     `NoFullLine` are **trivial** (`mg`/`gameover` pass through unchanged — `new_piece_state`
     never assigns them, §0.1). `PieceOccupiedInsideBounds`/`PieceOnFreeBlocks` are the
     only two that need `AxiomsRotGrid`'s `FullyContainedIn (RotGrid p 0) (InitialY p)
     (InitialX p) ForbiddenGrid FY FX` (stated `∀ p : Piece` — so it applies to `p2`
     regardless of which piece that turns out to be) combined with `AxiomsForbiddenGrid`'s
     `BBoxInsideBBox` — the *same* lemma `T1Proofs.v` already uses for `Init`'s and
     `FixPiece`'s spawn (`t1/proofs.md`), re-invoked here, not re-derived. This is the same
     obligation `t1/proofs.md`'s own `L-new_piece_state` lemma already discharges for
     `new_piece_state` in isolation — T3's obligation here is only that `hold_piece` calls
     it with a `p2` that is genuinely `∈ Piece` (guaranteed: `p2` is either `self.hold`'s
     stored piece, itself `∈ Piece` by `SwappedImplyHoldSome`'s type, or the caller-supplied
     `p_new : P::Piece`).
   - **`LevelCorrect (s2 s)` preservation** — trivial: `score`/`level`/`combo`/
     `perfect_clear`/`total_cleared_lines` are untouched (`T3.v`'s own `HoldPiece` builds
     the new `s2` via `T2.UnchangedT2Part`), so both sides of `LevelCorrect`'s equation are
     literally unchanged.
   - **`SwappedImplyHoldSome`/`GameoverImplyNotSwapped` preservation** — case analysis over
     all five T3 transitions: `Hold` sets `hold := Some(old_p)` and `swapped := true` in
     the same call, satisfying `SwappedImplyHoldSome` directly; `Hold`'s guard
     `!gameover` combined with `gameover` being untouched by `new_piece_state` keeps
     `GameoverImplyNotSwapped` vacuous on this branch (`gameover` can't newly become `true`
     here). `Move`/`Rotate` leave both fields untouched. `Fix` sets `swapped := false`,
     satisfying both implications vacuously regardless of `hold`/`gameover`.
   - **`HoldMonotone`** — `hold` is written only by `hold_piece`, always to `Some(...)`
     (never `None`); every other action leaves it untouched. Trivial induction.
   - **Ordering** — §4-T3e's numbered comment is the content of this obligation:
     `old_p` is bound to a local **before** `new_piece_state` mutates `self.s2.s1` in
     place, so the read genuinely observes the pre-state `p`, not a value the same call
     already overwrote.
6. **Cap/overflow soundness — not applicable.** `Hold` introduces no new arithmetic and
   touches none of the three saturating accumulators (`score`, `combo`,
   `total_cleared_lines`) — no new obligation beyond `t2/proofs.md` §8.4, which already
   covers every path that *does* touch them (`fix_piece`, unaffected by T3).
7. **`Init`.** `Machine::new(p0, piece_source)` ≙ `Init p0` (`T3.v`), field-by-field:
   `s2 = t2::model::Machine::new(p0, piece_source)` ≙ `T2.Init p0`; `hold = None` ≙
   `None`; `swapped = false` ≙ `false`.
8. **Each action — summary.** `move_piece`/`rotate_piece`: one-line delegation, full use
   (§3 above). `fix_piece`: partial use (§4 above). `fall_step`: disjoint-guard
   sequencing, as T1/T2. `hold_piece`: no-use, full argument (§5 above).

---

## 9. Tests (`tests/`)

Mirror T2's suite shape (`t2/implementation.md` §9) on T1's fixture (`PW=3`, two pieces
`Bar`/`Corner`, a 6×5 board, `t1/tests/test_instance.rs`) — plus T3-specific coverage.

- `test_instance.rs` — `include!(concat!(env!("CARGO_MANIFEST_DIR"),
  "/../t1/tests/test_instance.rs"))`, exactly `t2/tests/test_instance.rs`'s own pattern:
  `T3.v` introduces no new parameters, so there is nothing to add on top and the fixture
  keeps exactly one physical copy in the workspace.
- `model_unit_test.rs` — golden vectors for `hold_piece`, built on a `bar_at_rest`-style
  direct-field-write helper (`Machine`'s public fields, same D-Rust2 rationale T1's/T2's
  own unit tests already use):
  - hold when `hold == None` uses `p_new` (req-hold-empty): new current piece is `p_new`,
    `hold` becomes the old current piece, `swapped` becomes `true`.
  - hold when `hold == Some(x)` swaps (req-hold-swap): new current piece is `x`, `hold`
    becomes the old current piece.
  - a second hold attempt before an intervening fix fails (req-hold-limit): stutter, no
    field changes, return value `false`.
  - a fix resets `swapped`, re-enabling hold (req-hold-limit "after fixing").
  - hold is blocked when `gameover`.
  - **narrow-blast-radius check**: a firing hold changes only `p, py, px, pr` (of the
    inner `s1`) and `hold, swapped` (of T3) — `mg`, `s1.gameover`, `s1.cleared_lines`,
    `score`, `level`, `combo`, `perfect_clear`, `total_cleared_lines` are byte-identical
    before/after (`assert_eq!` on each, not a struct-level `PartialEq` derive, to keep the
    failure diagnostic per-field).
  - spawn position: `py`/`px`/`pr` after a hold equal `P::initial_y(p2)`/
    `P::initial_x(p2)`/`0`, exactly as a fix's respawn — but without a grid change or
    score/level update.
- `model_properties_test.rs` — `proptest`, generic-free (fixed to the fixture instance):
  `SwappedImplyHoldSome`, `GameoverImplyNotSwapped`, `HoldMonotone` hold after every step;
  `T2.Correct`'s conjuncts (delegated via `t2::model::check_invariants`) hold after every
  step including `Hold`; the narrow-blast-radius property above, generalized over random
  pre-states; differential oracle over every state component (§9 below).
- `model_fuzz_test.rs` — same dependency-free PRNG-driven shape as T1's/T2's: `N` seeds ×
  `M` steps, structural + the three new invariants + oracle differential, generic over the
  same fixture, no new dependency.
- `oracle.rs` — a from-scratch reimplementation of `hold`/`swapped` only (not the `s2`
  half: `t2/tests/oracle.rs` already differentially checks T2's fields against its own
  independent reimplementation, and `t1/tests/oracle.rs` does the same for T1's grid
  algebra beneath that — re-doing either here would test an already-tested engine a
  second time, not anything new). Reads `s2.s1.p`/`s2.s1.gameover` from the `Machine<P>`
  under test as ground truth for the guard/old-piece capture — exactly as
  `t3::model::Machine::hold_piece` itself does (§4-T3e) — and implements its own small
  `new_piece_state`-equivalent, hand-rolled — **not** calling `t1::model::new_piece_state`
  — for the same independence reason `t2/tests/oracle.rs` hand-rolls its saturating-add
  helper instead of calling `t2::model`'s: a bug shared between the translation and a
  helper it reuses should still surface as a mismatch here.

The SRS grids in `t1::instance` are validated by `t1::model::check_axioms` at startup (§7),
not by these suites — the same boundary as T1/T2.

---

## 10. Acceptance oracle (definition of correct regeneration)

A regeneration is correct iff:
1. Every `T3.v` definition with a §3 mapping is realized with the mapped name/behavior;
   every "not emitted" entry is absent.
2. `model.rs` constructs the T2 engine via `t2::model::Machine` and never reimplements a
   T1/T2 free function or duplicates `t1::model`/`t2::model` — in particular,
   `new_piece_state` is reached via `t1::model::new_piece_state::<P>`, not reimplemented
   (§4-T3a).
3. `tests/` passes on the fixture: unit + fuzz fully; properties under `proptest`.
4. The differential oracle (`oracle.rs`) agrees with `model.rs` on `hold`/`swapped` over
   every generated trace, on top of `t2::tests::oracle`'s own agreement on the `s2`
   component.
5. `hold_piece` reads `self.s2.s1.p` into a local **before** calling
   `t1::model::new_piece_state`, which mutates `self.s2.s1` in place (§4-T3e ordering).
6. `check_invariants` asserts both new T3 conjuncts (§6.8), delegating to
   `t2::model::check_invariants` rather than reimplementing it.

---

## 11. Instantiation (`t3/src/instance.rs`)

```rust
pub use t2::instance::{piece_color, Piece, Tetris};
```

`T3.v` introduces no abstract parameters, so `instance.rs` re-exports `t2::instance`'s
items (themselves a re-export of `t1::instance`'s) rather than restating them.
`t1::model::check_axioms::<Tetris>()` (§7) validates the underlying grids/piece set at
construction time, exactly as it does for T1/T2.

---

## 12. Generator determinism rules

Inherit `t1/implementation.md` §12 and `t2/implementation.md` §12's "reuse over
restatement" verbatim.

---

## 13. `instance.rs` parameters

None beyond T1's. See §11. (Section kept for parallelism with `t1/implementation.md` §13
and `t2/implementation.md` §13; intentionally empty of new content.)

---

## 14. `view.rs` — renderer (hold box + shifted panel + T2's grid/banners)

### 14.1 Public API

```rust
pub use t2::view::RenderConstants; // reached through t2's own re-export, not t1's
                                     // directly — see the import-boundary note below
pub use t2::view::Banner; // byte-identical (combo, perfect_clear, t)

pub fn render<P: Params>(
    constants: &RenderConstants,
    machine: &Machine<P>,
    piece_color: impl Fn(P::Piece) -> [f32; 4],
    banner: Option<&Banner>,
    font: Option<&Font>,
) { … }
```

`view.rs` imports nothing from `instance.rs` (same decoupling as `t1::view`/`t2::view`),
and — unlike `model.rs`, which imports `t1::model` directly for the `Params` trait bound
and `new_piece_state` (§0.1, no `T3Params` wrapper exists), and `main.rs`, which imports
`t1::model` only for the `Params` trait bound (`CHECK_AXIOMS`/`check_axioms` are
`t3::model`'s own, §7) —
`view.rs` reaches rendering exclusively through `t2::view`, never `t1::view` directly,
even though `t2::view` itself reuses `t1::view` underneath (§14.1 of
`t2/implementation.md`): `t3::model` wraps `t2::model`, not `t1::model`, directly, and
this file mirrors that boundary. Every draw call below is `t2::view`'s own `pub` API,
called on `&machine.s2`/`&layout.base` (skill §7); grid-only procedures (`draw_block`,
`draw_grid`, `draw_background`, `draw_grid_lines`, `draw_piece`) narrow one level further,
to `&layout.base.base` — `t2::view::Layout`'s own embedded `t1::view::Layout` — since none
of them read panel geometry. `font` is loaded once by `main.rs` and passed in by
reference every frame; `render` never loads or owns it.

### 14.2 Layout / scaling — hold box geometry

The grid and panel column are exactly `t2::view::compute_layout`'s own `Layout`, embedded
unmodified as `base`; the hold box is carved out of the **top** of that same panel column,
at the panel's own scale, not an independently sized box:

```rust
struct Layout {
    base: t2::view::Layout,
    hold_label_y: f32,  // y where the "Hold" text baseline sits
    hold_box_top: f32,  // y where the hold box's border starts
    hold_box_size: f32, // side length of the (square) hold box
    panel_top: f32,     // y where SCORE/LEVEL/banners start — below the hold box
}

fn compute_layout(constants: &t1::view::RenderConstants) -> Layout {
    let base = t2::view::compute_layout(constants);
    let m = t2::view::panel_metrics(base.panel_width);
    let hold_label_y = m.margin_y + m.label_font as f32;
    let hold_box_top = hold_label_y + m.label_font as f32 * 0.4;
    let hold_box_size = (constants.pw as f32 * base.base.cell_size).min(base.panel_width - 2.0 * m.margin_x);
    let panel_top = hold_box_top + hold_box_size + m.margin_y;
    Layout { base, hold_label_y, hold_box_top, hold_box_size, panel_top }
}
```

`hold_box_size` is clamped against `panel_width` (`t2/implementation.md` §14.2's own
narrow-viewport flag: `panel_width` and `cell_size` are computed independently, so on a
narrow viewport a `pw`-cell-wide box can exceed the panel). Computed **once** per frame in
`compute_layout` and threaded into `draw_hold_box`/`draw_panel`/`draw_banners` — one
shared layout, not three independent recomputations.

### 14.3 Coordinate transform

`t1::view::cell_origin` stays private to `t1::view` (§14.1 of `t1/implementation.md`) —
`t2::view` never redefined it, and neither does this file; the hold box uses its own
local transform (§14.4) instead, since it draws at
`hold_box_size / pw` scale rather than the grid's `cell_size`.

### 14.4 `draw_hold_box(constants, layout, machine, piece_color, font)`

```
- t2::view::draw_text_label "Hold" at (layout.base.panel_left + panel_metrics.margin_x, layout.hold_label_y), label_font, t2::view::LABEL_COLOR.
- stroke a square border at (layout.base.panel_left + panel_metrics.margin_x, layout.hold_box_top), side layout.hold_box_size.
  Colour #555555 normally; when machine.swapped, draw at reduced alpha (both border and
  piece fill below) — dimmed to signal "not available this piece", restored afterward.
- if let Some(held) = machine.hold:
    rg = P::rot_grid(held, 0)   // always rotation 0 in the hold box
    hb_cell = layout.hold_box_size / constants.pw as f32
    for y, x in [0, pw):
      if rg[y][x].is_none() { continue; }        // exact sentinel test (D1), not truthiness
      cx = box_left + x as f32 * hb_cell
      cy = layout.hold_box_top + (pw - 1 - y) as f32 * hb_cell   // same bottom-up flip as draw_piece
      t2::view::draw_block(cx, cy, hb_cell, piece_color(held))
```

`panel_metrics` and `draw_text_label`/`draw_block` are `t2::view`'s own (§14.1); this
function is the only place in `t3::view` that calls them directly rather than through
`draw_panel`/`draw_banners`, since the hold box has no `t2::view` counterpart to delegate
to as a whole.

### 14.5 `draw_panel`/`draw_banners` — reused from `t2::view`, shifted down

Not redefined. `render` calls `t2::view::draw_panel(&layout.base, &machine.s2, layout.panel_top, font)`
and `t2::view::draw_banners(&layout.base, below_level_y, banner, font)` directly:
`draw_panel`'s `top` parameter (§14.1 of `t2/implementation.md`) is exactly what lets this
crate start the SCORE block at `layout.panel_top` (below the hold box) instead of the
panel's own top margin, without needing its own copy of the function.

### 14.6 Piece colour parameter

As `t1/implementation.md`/`t2/implementation.md` §14.5: a `piece_color` closure
parameter, no default baked into `view.rs`.

### 14.7 Call order inside `render`

```
1. clear_background(t2::view::BG_COLOR)          (whole canvas, t1's/t2's own convention)
2. draw_hold_box                                    (label + box, top of panel — t3-only)
3. t2::view::draw_panel(&layout.base, &machine.s2, layout.panel_top, font)
4. t2::view::draw_banners(&layout.base, below_level_y, banner, font)
5. t2::view::draw_grid(&machine.s2.s1.mg, constants, &layout.base.base, &piece_color)
6. t2::view::draw_background(constants, &layout.base.base)
7. t2::view::draw_grid_lines(constants, &layout.base.base)
8. t2::view::draw_piece(&machine.s2, constants, &layout.base.base, &piece_color)
9. if machine.s2.s1.gameover: t2::view::draw_game_over(constants, &layout.base, font)
```

Steps 3–4 and 9 take `t2::view::Layout` (`&layout.base`, since `draw_panel`/`draw_banners`/
`draw_game_over` read panel geometry); steps 5–8 take its embedded `t1::view::Layout`
(`&layout.base.base`, since none of the four read anything beyond grid geometry) — both
called unchanged; only steps 1 (constant lookup) and 2 (new procedure) are `t3`-specific.

---

## 15. `main.rs`/`misc.rs` — entry point and the `Hold` action

Extends `t2/implementation.md` §15's shape (fall-speed curve, `RunState`, `after_action`,
restart). `LogicalKeys`/`RepeatTimer`/`window_conf`/`random_piece`/`DAS_DELAY`/`ARR` are
`t1::misc`'s (§15.2 of `t1/implementation.md`, §0.1 above), imported unchanged. `Action`
itself is **not** `t1::misc::Action`: `T3.v` adds a sixth event, `Hold`, so `t3::misc`
defines its own six-variant `Action` (§15.1 below), reusing `t1::misc::LogicalKeys` for
everything that doesn't depend on the variant set. Only `fire`/`process_input` are
crate-local, generic over `t3::model::Machine<P>` — `fire` calls the T3 wrapper's methods
(`move_piece`/`rotate_piece`/`fall_step`/`hold_piece` on `Machine<P>`, not on
`Machine<P>.s2` directly — so a T3-restart still goes through `t3::model::Machine::new`),
same reason `t1::misc::Action` and `t3::misc::Action` both exclude `fire` as a method.

### 15.1 `t3::misc` — the six-variant `Action`

```rust
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Action {
    Left, Right, Down, Cw, Ccw, Hold,
}
```

`Hold` is bound to the physical space bar (keyboard) and gamepad button index `3`,
**non-repeating** — the same class as `Cw`/`Ccw`
(`t1/implementation.md` §15.2's `Action` table), not `Left`/`Right`/`Down`: holding the
key down must not repeat-fire, since `req-hold-limit` already makes a second attempt
before an intervening fix a no-op, but repeat-firing would still be the wrong input model
(a deliberate, discrete choice each time, not a held direction).

`t3::misc` carries `Action`'s variants, `ALL`, `repeats`, `key`, `gamepad_button`,
`is_held`, `just_pressed`, and `any_action_just_pressed` — every method `t1::misc::Action`
has, minus `fire` (§15 above), plus the `Hold` case each of those methods now switches on.
`t4/main.rs` reuses this module directly rather than declaring its own six-variant
`Action` a second time (`t4/implementation.md` §15.1): `T4.v` adds no new player-facing
action, only changing what `Down`/`Hold` supply as their piece-source argument, which is
`fire`'s concern, not `Action`'s.

### 15.2 Everything else

`fire`'s dispatch:

```rust
Action::Hold => machine.hold_piece(random_piece::<P>()),
```

is the only new arm over `t2/implementation.md` §15's `fire` (`t1/implementation.md`
§15.5's original, generic over `t1::model::Machine<P>`). `RunState`/`after_action` (level-
change rescheduling, banner capture, banner expiry) and restart-on-gameover carry over
unchanged in shape from `t2/implementation.md` §15.1–§15.3 — `Hold`'s effect routes
through `after_action` exactly like every other action, even though it changes none of the
fields `after_action` inspects (`level`, `total_cleared_lines`) — cheap, and keeps every
action path going through the one hook. `process_input` itself is `t3/main.rs`'s own, not
shared via any `misc` module (`t1/implementation.md` §15.5's note on why: `T4.v`'s
`fall_step`/`hold_piece` take a bag, so no trait spans every `ti::model::Machine<P>`).

### 15.3 Font

As `t2/implementation.md` §15.9: the embedded `assets/JetBrainsMono-Regular.ttf`,
`include_bytes!`'d and loaded once before the frame loop, passed to every `view::render`
call as `Some(&font)`. `assets/` lives once at the workspace root, not inside `t3/`;
`include_bytes!`'s path is relative to `src/main.rs`, so `../../assets/JetBrainsMono-Regular.ttf`
reaches the same shared file every other crate's `main.rs` reaches.
