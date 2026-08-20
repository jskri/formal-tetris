# implementation.md — ImplementationInstructions for T5 (Rust)

Per-model instructions for the transformation

```
FormalModel (T5.v)  ×  ImplementationInstructions (this file)
      ── rocq-to-rust skill ──▶  Code (model.rs, view.rs, main.rs, instance.rs, misc.rs)
                                  ×  Proofs (proofs.md)  ×  Tests (tests/)
```

This file is the **T5-Rust-specific source of truth**, applying the `rocq-to-rust` skill's
general rules — in particular §7, "translating a module that wraps another" — to `T5.v`.
`t4/implementation.md` (and transitively `t3/implementation.md`/`t2/implementation.md`/
`t1/implementation.md`) are the frozen sources of truth for everything T5 reuses unchanged;
this file states only what is specific to T5. Generated artifacts are never hand-edited: to
change one, change this file or `T5.v` and regenerate. All references to
`T5.v`/`T4.v`/`T3.v`/`T2.v`/`T1.v` are **by definition name**.

## 0. Inputs, outputs, and what is frozen

Codegen-time inputs:
- `T5.v` — the abstract model (refines `T4.v` for `Event4` events only — see §1).
- `T4.v`/`t4/implementation.md` (and transitively `T3.v`/`T2.v`/`T1.v`) — reused in full.
- this file.
- the `rocq-to-rust` skill (cited as `skill §N`).

Runtime input (NOT codegen-time, NOT derived from `T5.v`):
- `t5/src/instance.rs` — implements `t5::model::Params` for `t1::instance::Tetris` (§11,
  §13). The impl body is empty: `T5.v` declares no `Parameter` of its own.

Outputs: `t5/src/model.rs`, `t5/src/view.rs`, `t5/src/main.rs`, `t5/src/misc.rs`,
`t5/src/instance.rs`, `t5/Cargo.toml`, `t5/proofs.md`, `t5/tests/` (§9). A generation is
**correct** iff `model.rs` refines `T5.v` (established by `proofs.md`); the acceptance oracle
(§10) is the operational check that provides evidence for this, it is not itself the
definition.

### 0.1 Files reused from `t1`/`t2`/`t3`/`t4` unchanged (not regenerated, imported as path
dependencies)

| item | role in T5 |
|------|-----------|
| `t4::model::Params` | the parameter trait; `t5::model::Params` extends it (skill §7.4) — `T5.v` adds no new abstract parameter |
| `t4::model::Machine<P>` | the wrapped engine, reached as `self.s4` |
| `t4::model::{check_invariants, check_axioms, assert_piece_set}` | called directly, not re-implemented |
| `t1::model::{valid, new_piece_yx_state}` | read the shadow / relocate the piece — both already exist in `rs_t1_src_model.rs`, no patch needed |
| `t2::view`/`t1::view` sub-procedures (`draw_panel`, `draw_banners`, `draw_grid`, `draw_background`, `draw_grid_lines`, `draw_piece`, `draw_game_over`, `draw_text_label`, `draw_block`, `panel_metrics`, `desired_panel_px`) | called directly by `t5::view`, exactly as `t4::view` already calls them |
| `t3::view::{Layout, compute_layout, draw_hold_box, Banner, RenderConstants}` | embedded/called by `t5::view`, exactly as `t4::view` already does |
| `t4::view::{Layout, compute_layout, draw_preview}` | embedded/called by `t5::view` (§0.2 — requires a visibility patch, the same kind `t4/implementation.md` §0.2 applied to `t3::view`) |
| `t1::instance::Tetris` | the concrete instance type; `t5::instance` adds a `t5::model::Params` impl for it rather than defining a new type (§11) |
| `t1::misc::{DAS_DELAY, ARR, window_conf, LogicalKeys, RepeatTimer, random_piece}` | `main.rs`-only primitives; `t5/main.rs` imports them directly |
| `t3::misc::Action` | **not** reused as-is (unlike T4, which reused it verbatim) — T5 adds a genuinely new player action (`Drop`), so `t5::misc::Action` is a fresh 7-variant redefinition (§15.1), the same treatment `t3::misc::Action` gives a game action absent from `t1::misc::Action` |

`t5/src/model.rs` therefore contains exactly one new kind of state-machine logic: the `gy`
field and its recomputation (`shadow_y`, `update_shadow_y`, `drop_piece`'s relocation).
Nothing in `t5` reimplements grid algebra, rotation, line clearing, scoring, the hold slot,
or the bag/preview mechanism.

### 0.2 Prerequisite patch to `t4/src/view.rs`

`t4::view::Layout`, `t4::view::compute_layout`, and `t4::view::draw_preview` are currently
private (no `pub` on the struct, either `fn`, confirmed against `rs_t4_src_view.rs`) —
`t4::view` is not itself wrapped by anything below T5, so, per `t4/implementation.md` §0.2's
own precedent (`t3::view::Layout` is widened for exactly the same reason: T4 needs to splice
into T3's render pipeline), the same widening is required one layer further up. T5
needs to insert `draw_ghost` between `draw_grid_lines` and `draw_piece` inside its own
`render`, which means calling `t4::view`'s geometry and preview-drawing directly rather than
treating `t4::view::render()` as an opaque whole (calling it as a whole would draw the active
piece and the game-over overlay before T5 ever got a chance to draw the ghost underneath
them). Required patch, purely additive (no signature or behavior change):
- `pub struct Layout { pub base: t3::view::Layout, pub right_origin: f32, pub preview_label_y: f32, pub preview_box_top: f32, pub preview_cell_size: f32, pub preview_gap: f32, pub preview_box_size: f32, pub preview_count: usize, pub min_row: i64, pub max_row: i64 }`
- `pub fn compute_layout<P: Params>(...) -> Layout`
- `pub fn draw_preview<P: Params>(...)`

No patch to `t4::model` or `t3::view`/`t2::view`/`t1::view` is needed — everything below
`t4::view` is already `pub` for `t4::view`'s own sake (`t4/implementation.md` §0.2), and T5's
new logic never touches the bag/preview state itself, only reads it (`machine.s4.next`) for
rendering purposes already exposed via the field being `pub`.

---

## 1. The refinement, and what it buys

`T5.State` embeds `T4.State` as `s4` and adds `gy : ℤ`, the y-coordinate of the current
piece's shadow/ghost (x/rotation are shared with the active piece — `T5.v`'s own header
comment — so only `y` is new state).

Refinement mapping (`T5.v`'s `Definition fₑ : T4.Event → T4.Event := id.` and `Definition fₛ:
T5.State → T4.State := s4.`): `fₑ = id`, `fₛ = s4`. **The refinement holds only for
`Event4` events** (`T5.v`'s own comment: "The refinement holds only when excluding Drop, i.e.
it holds on T4 events.") — `Drop` has no T4/T3/T2/T1 refinement claim at all, the same shape
as T3's exclusion of `Hold`. Per skill §7.1's three-way classification:

- **`move_piece`, `rotate_piece`, `fix_piece`, `hold_piece` — full uses.** Each is
  `option_map (UpdateShadowY s) (T4.<Action> ... (s4 s))` in `T5.v` — the underlying T4 call
  is untouched; the only addition is recomputing `gy` from the post-action state, itself a
  pure function of that state, not new guard logic. `t4/proofs.md`'s action lemmas transfer
  unchanged for the `s4` part; the new obligation is `gy` matching a fresh `shadow_y`
  computation, argued once (§8.3) and inherited by all four.
- **`fall_step`** delegates to `move_piece`/`fix_piece`, both already covered — disjoint-guard
  sequencing, unchanged in shape from every prior model in this tower.
- **`drop_piece` — no use for the relocation, full use for the trailing fix.** No T4 (or
  lower) *action* is invoked before the piece is relocated — `NewPieceYXState` is a state
  constructor, not an action, so there is nothing to delegate to there. `drop_piece` then
  calls `fix_piece`, a genuine T5 action already covered by the full-use case above.

---

## 2. File layout & module shape

```
t5/
  Cargo.toml            # depends on t1, t2, t3, t4 by path (workspace member)
  src/
    lib.rs               # pub mod instance; misc; model; view — same role as t1's/t3's
    misc.rs               # NEW: Action (7 variants — T3's six plus Drop, §15.1)
    instance.rs            # impl t5::model::Params for t1::instance::Tetris (§11, §13)
    model.rs                 # T5 engine: wraps t4::model::Machine, adds gy (§5–§7)
    view.rs                   # renderer: ghost piece (new) + t4's grid/panels/preview (§14)
    main.rs                    # entry point: DROP action, Up/D-pad-up (§15)
  proofs.md              # refinement proof, delta over t4/proofs.md (§8)
  tests/
    test_instance.rs     # include!'s t4's fixture verbatim (§9) — no new Params item needed
    model_unit_test.rs
    model_properties_test.rs
    model_fuzz_test.rs
    oracle.rs             # executable T5.v reference (reuses t4's oracle for s4)
```

The workspace root's `Cargo.toml` gains `"t5"` in `members`; `t1`–`t4` remain independently
buildable, unmodified in behavior by T5's existence (only the `pub` visibility widening of
§0.2).

---

## 3. Naming map (`T5.v` → Rust)

Only T5-introduced names appear here; T1–T4 names keep their own maps and are reached through
nested inner engines.

| `T5.v` | Rust |
|--------|------|
| `State` (record) | `t5::model::Machine<P>`; fields below |
| `s4` | `pub s4: t4::model::Machine<P>` |
| `gy` | `pub gy: i64` — plain field, no wrapper struct (T5's own, not nested) |
| `ShadowYImpl` / `ShadowY` | `shadow_y::<P>(s1: &t1::model::Machine<P>) -> i64` — combined into one function, iterative rather than recursive (skill: a `Fixpoint` on a strictly-decreasing measure becomes a loop — the measure is an explicit fuel count, not `py` itself, since `py` can legitimately go negative) |
| `Init` | `Machine::new(bags_fn, piece_source)` |
| `Event` | implicit (public `&mut self` methods, as T1–T4) |
| `UnchangedT5Part` | not emitted — realized by leaving `gy` untouched on a failed delegated call |
| `UpdateShadowY` | `update_shadow_y(&mut self)` — private method, called only when the delegated action fired (§4-T5b) |
| `MovePiece` | `Machine::move_piece(&mut self, dy, dx) -> bool` |
| `RotatePiece` | `Machine::rotate_piece(&mut self, cw) -> bool` |
| `FixPiece` | `Machine::fix_piece(&mut self, bag_new: &[P::Piece]) -> bool` |
| `FallStep` | `Machine::fall_step(&mut self, bag_new: &[P::Piece]) -> bool` |
| `HoldPiece` | `Machine::hold_piece(&mut self, bag_new: &[P::Piece]) -> bool` |
| `NewPieceYXState` (T5-level) | not emitted as a standalone function — realized at `drop_piece`'s one call site as a direct call to `t1::model::new_piece_yx_state` (§4-T5d) |
| `DropPiece` | `Machine::drop_piece(&mut self, bag_new: &[P::Piece]) -> bool` |
| `NextT4Event`, `Next` | not emitted — `main.rs`'s action dispatch already maps input → method |
| `fₑ`, `fₛ`, `T4RefinesT5` | `proofs.md` only; not emitted |
| `mg`, `p`, `py`, `px`, `pr`, `gameover`, `clearedLines`, `score`, `level`, `hold`, `perfectClear`, `pyx`, `combo`, `totalClearedLines`, `swapped`, `d` (T5-level accessors) | not emitted — each is a direct field read through `machine.s4.s3.s2.s1.…`/`machine.s4.s3.s2.…`/etc., same convention `t4/implementation.md` §6.7 already follows for its own layer |
| `ValidPieceCannotGoDown`, `LowestShadowY`, `GyEqShadowY`, `Correct`, `CorrectStep`, `CorrectWithoutGameover` | `proofs.md` only; not emitted |

---

## 4. Translation rules specific to T5

Every T1–T4 rule applies unchanged wherever T5 touches T1–T4 state, reached exclusively
through `self.s4`'s methods and fields. New T5-only points:

- **§4-T5a. `shadow_y::<P>(s1)` — iterative, combining `ShadowYImpl`+`ShadowY`,
  fuel-bounded.**
  ```rust
  // spec: ShadowYImpl + ShadowY — req-piece-shadow
  fn shadow_y<P: t1::model::Params>(s1: &t1::model::Machine<P>) -> i64 {
      let mut py = s1.py;
      let mut fuel = py + P::PW - 1;
      while fuel > 0 {
          if !t1::model::valid::<P>(&s1.mg, s1.p, py - 1, s1.px, s1.pr) {
              break;
          }
          py -= 1;
          fuel -= 1;
      }
      py
  }
  ```
  Generic only over `t1::model::Params` (skill §1's minimum-bound rule — this function reads
  no `t4::model::Params` item), and takes a `&t1::model::Machine<P>` rather than
  `&t5::model::Machine<P>` for the same reason. The recursion measure is **fuel, not `py`
  itself** — `py` can legitimately go negative, down to `-(PW-1)`: a piece is anchored in a
  fixed `PW×PW` rotation grid specifically so that rotating doesn't offset `py`/`px`, and
  `AxiomsRotGrid` only guarantees *some* occupied cell exists (`T1.v`), not that it sits at
  local row 0 — a piece whose only occupied cells sit near the top of its own bounding box
  can have its anchor go correspondingly negative while every occupied cell stays inside the
  main grid. Capping the search at `py > 0` would stop too early for such pieces/rotations:
  `valid(0)`/`valid(-1)`/etc. can genuinely hold, and `t1::model::move_piece`/`fix_piece`
  (unbounded, `i64`-typed) correctly permit descending further. `AxiomsRotGrid`'s guarantee
  forces `valid(py)` false once `py ≤ -PW`, so `fuel = py + PW - 1` is an exact bound: it is
  consumed by one unit per row descended, and the invariant `fuel = py_current + PW - 1` holds
  throughout, so by the time `fuel` reaches 0, `py` has reached exactly `-(PW-1)` — the true
  floor — without needing to check that row explicitly.
- **§4-T5b. `move_piece`/`rotate_piece`/`fix_piece`/`hold_piece` — full uses, each
  recomputing `gy` only on success.**
  ```rust
  pub fn move_piece(&mut self, dy: i64, dx: i64) -> bool {
      let fired = self.s4.move_piece(dy, dx);
      if fired {
          self.update_shadow_y();
      }
      if CHECK_INVARIANTS {
          check_invariants(self);
      }
      fired
  }
  ```
  (`rotate_piece`, `fix_piece`, `hold_piece` follow the identical shape, delegating to
  `self.s4.rotate_piece`/`fix_piece`/`hold_piece` respectively.) `update_shadow_y()`
  recomputes `self.gy` from the post-action `self.s4.s3.s2.s1` — a plain field write, not a
  guard. Guard failure (`fired == false`) leaves `gy` untouched, extending "guard fails ⟹
  zero mutation" to T5's own field: `option_map`'s `None` case in `T5.v` never reaches
  `UpdateShadowY` either, so this is not a new obligation, just the existing one carried one
  level deeper. Recomputing on a pure vertical move (`dy=-1, dx=0`, `fall_step`'s own use) is
  redundant but not wrong — `shadow_y` doesn't depend on `py`, only on `mg`/`p`/`px`/`pr`
  (visible from §4-T5a: the loop's *result* depends on where `valid` first fails while
  descending from the start point, not on which valid start point was used) — so recomputing
  unconditionally is simpler than special-casing by direction, and always correct.
- **§4-T5c. `fall_step(bag_new)`.** Unchanged shape from T1–T4:
  ```rust
  pub fn fall_step(&mut self, bag_new: &[P::Piece]) -> bool {
      if self.move_piece(-1, 0) {
          return true;
      }
      self.fix_piece(bag_new)
  }
  ```
  No `check_invariants` call of its own — both branches it can take already run one, matching
  `t4::model::Machine::fall_step`'s own convention.
- **§4-T5d. `drop_piece(bag_new)` — single upfront guard, no peek-then-commit.**
  ```rust
  pub fn drop_piece(&mut self, bag_new: &[P::Piece]) -> bool {
      t4::model::assert_piece_set::<P>(bag_new); // H
      if self.s4.s3.s2.s1.gameover {
          return false; // the only guard this method makes — req-flow
      }
      let px = self.s4.s3.s2.s1.px;
      // spec: NewPieceYXState (gy s, px s) s — req-piece-drop
      t1::model::new_piece_yx_state::<P>(self.gy, px, &mut self.s4.s3.s2.s1);
      self.fix_piece(bag_new) // guaranteed to fire — see proofs.md §8.5
  }
  ```
  Unlike `t4::model::fix_piece`, which needed a peek-then-commit ordering because no
  invariant guaranteed its underlying `T3.FixPiece` call would succeed, a single upfront check
  suffices here: `LowestShadowY` (`T5.v`) states `gameover(s4 s) = false → gy s ≤ py(s4 s) ∧
  ValidPieceCannotGoDown s (gy s) ∧ …` — i.e. whenever `¬gameover` holds *before* the drop,
  `valid(gy)` and `¬valid(gy-1)` both hold for the *current* `px`/`pr`/`mg`. Relocating `py`
  to `gy` therefore preserves `t1::model`'s `PieceOccupiedInsideBounds`/`PieceOnFreeBlocks`
  (via `valid(gy)`), and `t1::model::fix_piece`'s own guard (`¬gameover ∧
  ¬can_move_piece(-1,0,…)`, i.e. `¬valid(py-1,…)`) is exactly `¬valid(gy-1)` at the relocated
  state — already established. No case where the relocation is followed by a rejection
  exists, so no peek-then-commit restructuring is needed (contrast `t4/implementation.md`
  §4-T4d). `new_piece_yx_state` overrides *both* coordinates unconditionally
  (`rs_t1_src_model.rs`), so `px` is read and passed explicitly to keep the column unchanged —
  passing a literal here would reset the piece's column on every hard drop.
  `t4::model::fix_piece` re-asserts `bag_new` internally (its own §4-T4c convention); the
  assertion here is accepted redundancy, the same the tower already accepts in `fall_step`.

---

## 5. Free functions emitted by `model.rs` (`T5.v` source order)

- `shadow_y::<P: t1::model::Params>(s1: &t1::model::Machine<P>) -> i64` — §4-T5a.

None of the T4 free functions (`is_piece_set`, `assert_piece_set`, `draw_once`,
`init_piece_and_draw`) are re-emitted or re-exported at the T5 layer; `drop_piece` calls
`t4::model::assert_piece_set` directly, by its `t4::model::` path.

---

## 6. `t5::model::Params` and `t5::model::Machine<P>`

### 6.0 `Params` trait

```rust
// spec: T5.v declares no Parameter of its own.
pub trait Params: t4::model::Params {}
```

Extends `t4::model::Params` directly (skill §7.4), adding no new trait items. Per §11, a
concrete instance type opts in with an explicit, empty `impl t5::model::Params for
t1::instance::Tetris {}` — the same mechanical shape every other layer's `instance.rs` uses,
rather than a blanket `impl<P: t4::model::Params> Params for P {}` — so that "is `t5`-ready"
stays an explicit, per-type fact like it is at every other layer, even though here it happens
to have an empty body.

### 6.1 `Machine<P>` and constructor — `Init bags H` (`T5.v`)

```rust
pub struct Machine<P: Params> {
    pub s4: t4::model::Machine<P>,
    pub gy: i64, // spec: gy — req-piece-shadow
}

impl<P: Params> Machine<P> {
    /// spec: Init
    pub fn new(
        bags_fn: impl FnMut(u64) -> Vec<P::Piece>,
        piece_source: impl FnMut() -> P::Piece,
    ) -> Self {
        let s4 = t4::model::Machine::new(bags_fn, piece_source); // spec: T4.Init bags H
        let gy = shadow_y::<P>(&s4.s3.s2.s1); // spec: ShadowY s4
        let m = Machine { s4, gy };
        if CHECK_INVARIANTS {
            check_invariants(&m);
        }
        m
    }
    // ...
}
```

### 6.2–6.5 Actions

`move_piece`/`rotate_piece`/`fix_piece`/`hold_piece` — §4-T5b. `fall_step` — §4-T5c.
`drop_piece` — §4-T5d.

### 6.6 Read-through access

No new getters beyond what `t4::model::Machine`'s own public fields already expose (`s4.bag`,
`s4.next`, `s4.s3.hold`, `s4.s3.s2.level`, `s4.s3.s2.s1.gameover`, etc., same nesting T4
itself uses) — `main.rs`/`view.rs` read `machine.s4.…` (or `machine.gy` for the one new
field) directly.

### 6.7 `check_axioms::<P>()`

```rust
/// spec: `T5.v` states no `Axiom` of its own. Pure delegation.
pub fn check_axioms<P: Params>() {
    t4::model::check_axioms::<P>();
}
```

Gated by `t5::model`'s own `pub const CHECK_AXIOMS: bool = true;` (§7), called once by
`main.rs` before the first `Machine<P>` is constructed, same convention every prior layer
follows — including `t3::model`, whose own axiom set is likewise empty and which still
defines and gates this the same way.

### 6.8 `check_invariants::<P>(s)`

```rust
/// spec: `LowestShadowY`, `GyEqShadowY` — layered on `t4::model::check_invariants`.
/// Both gated on `!gameover`, mirroring `LowestShadowY`'s own precondition: a
/// freshly-spawned piece under `gameover = true` isn't guaranteed `valid` at its own
/// position, so checking `GyEqShadowY` there would be checking a claim about a state
/// `T5.v`'s own invariant doesn't constrain, even though `GyEqShadowY` itself is stated
/// unconditionally in `T5.v`.
pub fn check_invariants<P: Params>(s: &Machine<P>) {
    t4::model::check_invariants(&s.s4);
    if !s.s4.s3.s2.s1.gameover {
        let expected = shadow_y::<P>(&s.s4.s3.s2.s1);
        assert!(s.gy == expected, "GyEqShadowY failed");
        assert!(s.gy <= s.s4.s3.s2.s1.py, "LowestShadowY: gy <= py failed");
    }
}
```

### 6.9 `update_shadow_y`

```rust
impl<P: Params> Machine<P> {
    pub fn update_shadow_y(&mut self) {
        self.gy = shadow_y::<P>(&self.s4.s3.s2.s1);
    }
}
```
`pub`, not module-private (skill §1's private-by-default rule for state-but-non-action
definitions, escalated here for a genuine external need): a wrapping module that mutates `mg`
directly, outside any action `t5::model` itself defines, needs to recompute the shadow
afterward — the same recomputation this method already performs after each of §4-T5b's four
wrappers below.

---

## 7. `t5::model`'s constants

```rust
pub const CHECK_AXIOMS: bool = true;        // module-level, as t1–t4::model
pub const CHECK_INVARIANTS: bool = false;   // module-level, as t1–t4::model
```

---

## 8. `proofs.md` (scope)

Delta over `t4/proofs.md`.

1. **Scope.** Safety only. `Drop` has no refinement claim in `T5.v` itself (§1) —
   structural, not a codegen choice, same as `t3/proofs.md`'s treatment of `Hold` and
   `t4/proofs.md`'s own scope note.
2. **α₅.** `α₅(rs) = { s4 := α₄(rs.s4); gy := rs.gy }` — `gy` maps directly (a plain integer,
   no coercion), applying `t4/proofs.md`'s `α₄` to the embedded machine.
3. **`move_piece`/`rotate_piece`/`fix_piece`/`hold_piece` — full-use transfer, plus one new
   obligation each: `gy` after a successful call equals `shadow_y` of the post-call state.**
   Definitional, not inductive — `update_shadow_y()` *is* that computation, called exactly
   when `T5.v`'s `option_map` would reach `UpdateShadowY`. The stuttering-step property
   (guard fails ⟹ zero mutation) extends to `gy` for the same reason: the failure path never
   calls `update_shadow_y()`.
4. **`fall_step`** — disjoint-guard sequencing, unaffected, as T1–T4.
5. **`drop_piece` — no-use for the relocation step, full use for the trailing fix.**
   - **Guard:** the single `gameover` check.
   - **Soundness of the relocation, given `¬gameover` at the pre-drop state:** cite
     `LowestShadowY` as an imported fact — `gy s ≤ py(s4 s)`, `ValidPieceCannotGoDown s (gy
     s)` (i.e. `valid(gy)` and `¬valid(gy-1)`), both conditional on `¬gameover(s4 s)`,
     established at `Init` and preserved by every T5 action (item 3 above shows `gy` always
     equals a fresh `shadow_y` computation, and `shadow_y`'s own loop invariant — proved
     separately, not re-derived here — guarantees its result satisfies
     `ValidPieceCannotGoDown` whenever the starting `valid(py)` holds, which
     `t4::model::check_invariants`'s delegated `PieceOnFreeBlocks` supplies whenever
     `¬gameover`). `t1::model::new_piece_yx_state`'s relocation therefore preserves
     `PieceOccupiedInsideBounds`/`PieceOnFreeBlocks` at the relocated state (via
     `valid(gy)`), and the relocated state's `py - 1` is exactly `gy - 1`, so
     `t1::model::fix_piece`'s guard (`¬gameover ∧ ¬can_move_piece(-1,0,…)`) is exactly
     `¬valid(gy-1)` — already established. No case where the relocation is followed by a
     rejection exists; no peek-then-commit ordering is needed (contrast `t4/proofs.md` §4).
   - **The trailing `fix_piece` call** is covered by item 3 above — its own `gy`-refresh
     obligation is inherited, not re-argued.
6. **Cap soundness — not applicable.** `drop_piece` introduces no new arithmetic and touches
   no capped accumulator; it only relocates `py` and then delegates to `fix_piece`, already
   covered by `t2/proofs.md` §5.
7. **`Init`.** `Machine::new(bags_fn, piece_source)` ≙ `Init bags H` (`T5.v`): `self.s4 =
   t4::model::Machine::new(...)` ≙ `T4.Init bags H`; `self.gy = shadow_y(...)` ≙ `ShadowY
   s4`, by definition.
8. **Each action — summary.** `move_piece`/`rotate_piece`/`fix_piece`/`hold_piece`: full use,
   `gy`-refresh-on-success (item 3). `fall_step`: disjoint-guard sequencing (item 4).
   `drop_piece`: no-use relocation + full-use fix, single upfront guard sufficient given
   `LowestShadowY` (item 5).

---

## 9. Tests (`tests/`)

Mirror T4's suite (`t4/implementation.md` §9) on the same fixture family, plus T5-specific
coverage.

- **`test_instance.rs`** — `include!(concat!(env!("CARGO_MANIFEST_DIR"),
  "/../t4/tests/test_instance.rs"));`, giving `TestInstance` (`NEXT_LEN = 3`) and
  `TestInstanceWide` (`NEXT_LEN = 5`) unchanged. `T5.v` introduces no new `Params` item, so
  both already satisfy `t5::model::Params` once the explicit `impl t5::model::Params for
  TestInstance {}` / `impl t5::model::Params for TestInstanceWide {}` are added alongside the
  include — same mechanical shape as `instance.rs`'s own (§6.0, §11).
- **`oracle.rs`** — reuses `t4`'s oracle for `s4`; independently hand-rolls a `shadow_y`/
  `drop_piece` equivalent (own loop, own field mutation, not importing `model.rs`/
  `t1::model` — same independence discipline as every prior oracle).
- **`model_unit_test.rs`** — golden vectors on `TestInstance`:
  - **Overhang board, hand-crafted:** a board where the piece's column has a locked shelf a
    few rows up and open space beneath it, down to the true floor (which may be below row 0
    — see the next bullet). `shadow_y` must return the shelf-top row, not the true floor
    beneath it — test this directly, not just the unobstructed case.
  - **Unobstructed-column floor, per piece type:** on an empty column, `shadow_y` must equal
    `-(min_row of that piece's rotation-0 grid)`, not `0` — verified against `TestInstance`'s
    real piece/rotation data. Test every piece type in `Piece`, not just one.
  - `shadow_y` unaffected by a pure vertical move: compute it, `move_piece(-1,0)`, recompute
    — same value, even when that value is negative.
  - `shadow_y` changes after a horizontal move or a rotation, when the new column/orientation
    has a different floor/obstruction.
  - `drop_piece` locks the piece at exactly `gy` (not `py`), and fires whenever `¬gameover`,
    regardless of how far above the floor the piece currently sits — including from spawn,
    where the true floor can be several rows below `0`.
  - `drop_piece` blocked by `gameover`, leaving `s4`/`gy` byte-identical to before the call.
  - narrow-blast-radius: a successful `drop_piece` changes exactly what a `fix_piece` at row
    `gy` would change, plus `gy` itself (refreshed for the new piece) — nothing else.
- **`model_properties_test.rs`** — `proptest`, on `TestInstanceWide`: `gy` always equals a
  fresh `shadow_y` computation after every step (when `¬gameover`); `gy ≤ py` always; `gy ≥
  -(PW-1)` always (the fuel bound); differential oracle over every snapshot field, across all
  seven action kinds (T4's five plus `drop_piece`).
- **`model_fuzz_test.rs`** — long random traces including `drop_piece`, `gy` invariant
  checked every step via `CHECK_INVARIANTS`, differential oracle, adversarial
  `assert_piece_set` inputs (delegated, no new axioms to test directly).

---

## 10. Acceptance oracle

A regeneration is correct iff:
1. Every `T5.v` definition with a §3 mapping is realised; every "not emitted" entry is
   absent.
2. `model.rs` constructs the T4 engine via `t4::model::Machine::new`/its action methods and
   never reimplements any T1–T4 free function.
3. `tests/` passes on both fixtures: unit + fuzz fully; properties under `proptest`.
4. The differential oracle agrees with `model.rs` on every field, including `gy`, over every
   generated trace.
5. `move_piece`/`rotate_piece`/`fix_piece`/`hold_piece` each call `update_shadow_y()` if and
   only if the delegated T4 call fired.
6. `drop_piece` performs exactly one `gameover` check, before relocating `py`/`px`, and never
   defers/re-checks after relocation.
7. `check_invariants` recomputes `shadow_y` and compares against `gy`, gated on `!gameover`.
8. `check_axioms::<P>()` delegates to `t4::model::check_axioms::<P>()` and asserts nothing
   further — `T5.v` states no axiom of its own.
9. The `t4::view` visibility patch (§0.2) is present and additive-only.

---

## 11. Instantiation (`instance.rs`)

```rust
pub use t4::instance::{piece_color, Piece, Tetris};

impl crate::model::Params for Tetris {}
```

Legal under Rust's orphan rule, same as every prior layer's own `instance.rs`
(`t4/implementation.md` §11). The impl body is empty — `T5.v` declares no `Parameter` of its
own, so there is nothing to supply beyond the trait bound itself (§6.0).

---

## 12. Generator determinism rules

Inherit `t1/implementation.md` §12 / … / `t4/implementation.md` §12's "reuse over
restatement" verbatim, with the one addition of §0.2's `pub` widening — visibility-only, not
a behavior change, so it doesn't reopen `t1`–`t4`'s own determinism guarantees.

---

## 13. `instance.rs` parameters

None beyond `t4`'s (`NEXT_LEN = 6`, unchanged). See §11.

---

## 14. `view.rs` — renderer (ghost piece + `t4`'s grid/panels/preview)

`t5::view` does not redefine anything `t4::view`/`t3::view`/`t2::view`/`t1::view` already
provides (§0.1, §0.2); the caller-supplied `piece_color` closure convention carries through
unchanged. `draw_ghost` is the only genuinely new function here — it needs `machine.gy`, a
field that doesn't exist at any inner layer.

### 14.1 Public API

```rust
pub use t4::view::RenderConstants; // byte-identical fields, reused per §12

pub fn render<P: Params>(
    constants: &RenderConstants,
    machine: &Machine<P>,
    piece_color: impl Fn(P::Piece) -> [f32; 4],
    banner: Option<&t3::view::Banner>,
    font: Option<&Font>,
) {
    // ... §14.4
}
```
Same signature shape as `t4::view::render`, generic over `P: Params` (this crate's own
trait). Returns `()` — no caller before a future model needs a return value, so none is added
speculatively here.

### 14.2 Ghost transparency

```rust
const GHOST_ALPHA: f32 = 0.25;
```
A starting value, not a measured-optimal one — same caveat every prior layer's own cosmetic
constants carry.

### 14.3 `draw_ghost`

```rust
/// spec: view-only rendering of `gy`/`px`/`pr`/`p`'s ghost projection — no `T5.v`
/// counterpart. Same coordinate transform as `t1::view::draw_piece`, inlined rather than
/// reusing it directly: `draw_piece` reads `py` off its `Machine` argument with no
/// parameterization for an alternate row source, so a fresh function (reading `gy` instead)
/// is the direct realization here, the same way `t4::view::draw_preview` already inlines its
/// own cell-origin math rather than reaching `t1::view`'s private `cell_origin`.
/// req-piece-shadow. `pub` (like `compute_layout`/`draw_preview` before it)
/// so a downstream caller can compose its own render pass from these
/// primitives instead of going through `render`.
pub fn draw_ghost<P: Params>(
    constants: &RenderConstants,
    layout: &t1::view::Layout,
    machine: &Machine<P>,
    piece_color: &impl Fn(P::Piece) -> [f32; 4],
) {
    let s1 = &machine.s4.s3.s2.s1;
    let pg = P::rot_grid(s1.p, s1.pr);
    let [r, g, b, a] = piece_color(s1.p);
    let color = Color::new(r, g, b, a * GHOST_ALPHA);
    for dy in 0..constants.pw {
        for dx in 0..constants.pw {
            if pg[dy as usize][dx as usize].is_none() {
                continue; // exact-sentinel test, not truthiness
            }
            let (y, x) = (machine.gy + dy, s1.px + dx);
            if y < 0 || y >= constants.hm || x < 0 || x >= constants.wm {
                continue;
            }
            let cx = layout.origin_x + x as f32 * layout.cell_size;
            let cy = layout.origin_y + (constants.hm - 1 - y) as f32 * layout.cell_size;
            t2::view::draw_block(cx, cy, layout.cell_size, color);
        }
    }
}
```
Same piece color as the active piece — only the alpha differs. No special-casing for `gy ==
py` (piece already resting on its shadow): the opaque active piece, drawn afterward, fully
covers the ghost in that case; branching to skip the ghost draw would save one loop's worth
of (invisible) fills at the cost of an extra condition on every frame, not worth it.

### 14.4 Call order inside `render`

```rust
pub fn render<P: Params>(
    constants: &RenderConstants,
    machine: &Machine<P>,
    piece_color: impl Fn(P::Piece) -> [f32; 4],
    banner: Option<&t3::view::Banner>,
    font: Option<&Font>,
) {
    let layout = t4::view::compute_layout::<P>(constants); // pub per §0.2
    clear_background(t2::view::BG_COLOR);
    t3::view::draw_hold_box(constants, &layout.base, &machine.s4.s3, &piece_color, font);
    let below_level_y =
        t2::view::draw_panel(&layout.base.base, &machine.s4.s3.s2, layout.base.panel_top, font);
    t2::view::draw_banners(&layout.base.base, below_level_y, banner, font);
    t4::view::draw_preview::<P>(constants, &layout, &machine.s4.next, &piece_color, font); // pub per §0.2
    t2::view::draw_grid(&machine.s4.s3.s2.s1.mg, constants, &layout.base.base.base, &piece_color);
    t2::view::draw_background(constants, &layout.base.base.base);
    t2::view::draw_grid_lines(constants, &layout.base.base.base);
    draw_ghost::<P>(constants, &layout.base.base.base, machine, &piece_color); // new — between grid lines and piece
    t2::view::draw_piece(&machine.s4.s3.s2, constants, &layout.base.base.base, &piece_color);
    if machine.s4.s3.s2.s1.gameover {
        t2::view::draw_game_over(constants, &layout.base.base, font);
    }
}
```
`layout.base.base.base` is `t1::view::Layout` — depth-4 nesting (`t5::view::Layout` doesn't
exist as its own type; `render` uses `t4::view::Layout` directly, whose own `.base.base.base`
already reaches `t1::view::Layout` — one level of nesting is saved here relative to what a
`t5::view::Layout` wrapper would have needed, since `draw_ghost` needs no new geometry field
of its own beyond what `t4::view::Layout`'s existing chain already provides). `draw_ghost` is
called between `draw_grid_lines` and `draw_piece`: whole-canvas clear (`clear_background`,
not `t1::view::draw_background`, the forbidden-zone tint — see `t1/implementation.md`'s own
disambiguation, carried forward unchanged through every layer) → hold box → panel → banners
→ preview column → locked blocks → forbidden-zone tint → grid lines → ghost piece (new) →
falling piece → game-over overlay if applicable.

---

## 15. `main.rs` — entry point

Extends `t4/implementation.md` §15's shape. Unlike T4 (which reused `t3::misc::Action`
verbatim, adding no new player-facing action), T5 adds `Drop`, so `Action` itself is new here.

### 15.1 `t5::misc::Action` — seven variants, `Drop` added, no repeat

```rust
// spec: §15 — T3's six variants plus Drop (req-piece-drop).
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Action {
    Left,
    Right,
    Down,
    Cw,
    Ccw,
    Hold,
    Drop,
}

impl Action {
    pub const ALL: [Action; 7] = [
        Action::Left, Action::Right, Action::Down,
        Action::Cw, Action::Ccw, Action::Hold, Action::Drop,
    ];

    /// `Drop` is non-repeating — a hard drop is a single decisive action, the same class
    /// as `Hold`/`Cw`/`Ccw`, not a held/repeated one.
    pub fn repeats(self) -> bool {
        matches!(self, Action::Left | Action::Right | Action::Down)
    }

    pub fn key(self, logical: &LogicalKeys) -> Option<KeyCode> {
        match self {
            Action::Left => Some(KeyCode::Left),
            Action::Right => Some(KeyCode::Right),
            Action::Down => Some(KeyCode::Down),
            Action::Cw => logical.cw,
            Action::Ccw => logical.ccw,
            Action::Hold => Some(KeyCode::Space),
            Action::Drop => Some(KeyCode::Up),
        }
    }

    pub fn gamepad_button(self) -> Button {
        match self {
            Action::Left => Button::DPadLeft,
            Action::Right => Button::DPadRight,
            Action::Down => Button::DPadDown,
            Action::Cw => Button::East,
            Action::Ccw => Button::South,
            Action::Hold => Button::North,
            Action::Drop => Button::DPadUp,
        }
    }

    pub fn is_held(self, logical: &LogicalKeys, pad: Option<Gamepad<'_>>) -> bool {
        self.key(logical).is_some_and(is_key_down) || pad.is_some_and(|p| p.is_pressed(self.gamepad_button()))
    }

    pub fn just_pressed(self, logical: &LogicalKeys, pad: Option<Gamepad<'_>>) -> bool {
        self.key(logical).is_some_and(is_key_pressed) || pad.is_some_and(|p| p.is_pressed(self.gamepad_button()))
    }
}

pub fn any_action_just_pressed(logical: &LogicalKeys, pad: Option<Gamepad<'_>>) -> bool {
    Action::ALL.iter().any(|a| a.just_pressed(logical, pad))
}
```
`Button::DPadUp` — the existing entries (`DPadLeft`/`DPadRight`/`DPadDown` for
left/right/down) already use gilrs's D-pad buttons for the repeating directional actions, so
`DPadUp` is the consistent choice for the one new non-repeating action, not a new convention.
No conflict with the face buttons already bound (`East`/`South`/`North`).

### 15.2 `ACTIONS`/`fire` — `Drop` added

```rust
fn fire<P: Params>(action: Action, machine: &mut Machine<P>) {
    match action {
        Action::Left => { machine.move_piece(0, -1); }
        Action::Right => { machine.move_piece(0, 1); }
        Action::Down => { machine.fall_step(&shuffle_bag::<P>()); }
        Action::Cw => { machine.rotate_piece(true); }
        Action::Ccw => { machine.rotate_piece(false); }
        Action::Hold => { machine.hold_piece(&shuffle_bag::<P>()); }
        Action::Drop => { machine.drop_piece(&shuffle_bag::<P>()); }
    }
}
```
A free function, not a method on `Action` (`t1::misc`'s own note, carried forward): `t5::
model::Machine::fall_step`/`hold_piece`/`drop_piece` all take `&[P::Piece]`, so `t5/main.rs`'s
`fire` cannot be shared with any prior crate's even though the underlying `Action` enum is
similar in shape.

### 15.3 `shuffle_bag`/`make_bags_fn` — duplicated locally, unchanged in shape

`shuffle_bag::<P>()` and `make_bags_fn::<P>()` are copied from `t4/implementation.md`
§15.1/§15.2 verbatim (adjusted only to `t5::model::Params`'s bound) — `main.rs` is a binary,
not part of any crate's public library surface, so each layer's `main.rs` re-declares these
rather than importing them from the previous layer's binary (the same duplication `t4/main.rs`
already accepts relative to `t3/main.rs`).

### 15.4 Everything else

`window_conf`, `LogicalKeys`, `RepeatTimer`, `random_piece`, `DAS_DELAY`/`ARR` are
`t1::misc`'s, imported directly. `fall_period`, `RunState`, `after_action`, `process_input`'s
DAS/ARR engine, restart-on-gameover, and font loading are `t5/main.rs`'s own, carrying over
unchanged in shape from `t4/implementation.md` §15 — generic over `t5::model::Machine<P>`
instead of `t4::model::Machine<P>`, reading `machine.s4.s3.s2.…` (one hop deeper than T4's own
`machine.s3.s2.…`) wherever T2-level fields (`level`, `total_cleared_lines`, `combo`,
`perfect_clear`, `gameover`) are needed, and dispatching through `t5::misc::Action`/`fire`
(§15.1/§15.2) instead of `t3::misc::Action`. A T5-restart goes through
`Machine::new(make_bags_fn::<P>(), random_piece::<P>)`, `t5::model::Machine::new`'s own
signature, unchanged from T4's in shape. `process_input` is not itself shared via any `misc`
module, for the same reason `t1/implementation.md` §15.5 gives: it dispatches through this
layer's own `Machine`'s method signatures, which rules out a shared dispatch trait.

### 15.5 `index.html` equivalent

Not applicable — `main.rs` is the entry point directly (macroquad's `#[macroquad::main]`), no
separate HTML shell exists in the Rust translation at any layer.
