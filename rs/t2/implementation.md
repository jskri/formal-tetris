# implementation.md — ImplementationInstructions for T2 (Rust)

Per-model instructions for the transformation

```
FormalModel (T2.v)  ×  ImplementationInstructions (this file)
      ── rocq-to-rust skill ──▶  Code (model.rs, view.rs, main.rs, instance.rs)
                                  ×  Proofs (proofs.md)  ×  Tests (tests/)
```

This file is the **T2-Rust-specific source of truth**, applying the `rocq-to-rust` skill's
general rules — in particular §7, "translating a module that wraps another" — to `T2.v`.
`t1/implementation.md` is the frozen source of truth for everything T2 reuses unchanged;
this file states only what is specific to T2. Generated artifacts are never hand-edited: to
change one, change this file or `T2.v` and regenerate. All references to `T2.v`/`T1.v` are
**by definition name**, so renaming/reordering in either model is caught by the coverage
check (§10), not silently mismatched line numbers.

## 0. Inputs, outputs, and what is frozen

Codegen-time inputs:
- `T2.v` — the abstract model (refines `T1.v` via the mapping `f = (fₑ, fₛ)`).
- `T1.v` and `t1/implementation.md` — the refined model and its frozen instructions, reused
  in full (§0.1).
- this file.
- the `rocq-to-rust` skill (cited as `skill §N`).

Runtime input (NOT codegen-time, NOT derived from `T2.v`):
- `t2/src/instance.rs` — re-exports `t1::instance`'s `Params` implementation (§11, §13):
  `T2.v` introduces no new abstract parameters, so there is nothing new to instantiate.

Outputs: `t2/src/model.rs`, `t2/src/view.rs`, `t2/src/main.rs`, `t2/src/instance.rs`,
`t2/Cargo.toml`, `t2/proofs.md`, `t2/tests/` (§9). A generation is **correct** iff
`model.rs` refines `T2.v` (established by `proofs.md`); the acceptance oracle (§10) is the
operational check that provides evidence for this, it is not itself the definition —
regeneration determinism (skill §12 / t1 §12) is what governs equivalence between
independent runs of the transformation.

### 0.1 Files reused from `t1` unchanged (not regenerated, imported as a path dependency)

| item | role in T2 |
|------|-----------|
| `t1::model::Params` | the parameter trait; `t2::model::Machine<P>` bounds on it directly — no `T2Params` wrapper trait exists, since T2 adds no parameters (skill §7.4) |
| `t1::model::Machine<P>` | the inner engine; `t2::model::Machine<P>` holds one as its `s1` field |
| `t1::model::{check_axioms, check_invariants, type_ok}` | `check_invariants`/`type_ok` called directly, not re-implemented; `check_axioms` is wrapped (§7), not called directly |
| `t1::model`'s grid free functions (`intersect`, `occupied_inside`, `is_full_row`, …) | reached only through `t1::model::Machine`'s own methods; `t2/src/model.rs` never calls them directly and never duplicates one |
| `t1::instance::Tetris` | the concrete `Params` impl; re-exported by `t2::instance` (§11) |
| `t1::misc::{DAS_DELAY, ARR, window_conf, LogicalKeys, RepeatTimer, random_piece, Action, any_action_just_pressed}` | `main.rs`-only primitives (§15.2 of `t1/implementation.md`); `t2/main.rs` imports them directly rather than re-declaring, and defines only its own `fire`/`process_input`/`RunState`/`after_action` (§15) |

`t2/src/model.rs` therefore contains exactly one new kind of logic: the five T2 scalar
fields and `FixPiece`'s extra arithmetic. There is exactly one copy of the T1 engine in the
workspace (the `t1` crate); nothing in `t2` reimplements grid algebra, rotation, or line
clearing.

---

## 1. The refinement, and what it buys

`T2.State` embeds `T1.State` as the field `s1` and adds five scalar/flag fields: `score`,
`level`, `combo`, `perfectClear`, `totalClearedLines` (`T2.v` `Record State`).

The refinement mapping (`T2.v`, Refinement section):
- `fₑ : T2.Event → T1.Event` is the constructor-wise identity.
- `fₛ : T2.State → T1.State` is the projection `s1`.
- `T2RefinesT1`'s second conjunct: `∀ e2 s2 s2', T2.Next e2 s2 = Some s2' → T1.Next (fₑ e2)
  (fₛ s2) = Some (fₛ s2')`.

Consequence for codegen: the `s1` half of every T2 transition **is** a T1 transition. So
`t2::model::Machine<P>` holds a real `t1::model::Machine<P>` and delegates the `s1` update
to it; only the five T2 fields need new logic, and only `fix_piece` changes them
non-trivially (skill §7.1's full/partial/no-use classification, applied per-action in §6
below).

Scope (`proofs.md`, full structure in §8): safety/refinement only. Fall speed (§15) and
on-screen banners (§14) are UI-layer concerns outside the refinement, exactly as fall
timing was outside T1 (`T1.v`'s own design note: "time is intentionally not part of the
model").

---

## 2. File layout & module shape

```
t2/
  Cargo.toml            # depends on t1 by path (workspace member)
  src/
    lib.rs               # pub mod instance; model; view — same role as t1's lib.rs
    instance.rs          # re-exports t1::instance's Params impl (§11, §13)
    model.rs              # T2 engine: wraps t1::model::Machine, adds score/level/combo/
                           # perfectClear/totalClearedLines (§5–§7)
    view.rs                # renderer: t1's grid + a left info panel + transient banners (§14)
    main.rs                 # entry point: level→fall-speed, banner timing (§15)
  proofs.md              # refinement proof, delta over t1/proofs.md (§8)
  tests/
    test_instance.rs     # test fixture — re-exports t1's tests/test_instance.rs
    model_unit_test.rs
    model_properties_test.rs
    model_fuzz_test.rs
    oracle.rs             # executable T2.v reference (reuses t1's oracle for s1)
```

The workspace root (`Cargo.toml`, `members = ["t1", "t2"]`) is what makes `t2/Cargo.toml`'s
`t1 = { path = "../t1" }` dependency resolve; `t1` remains independently buildable as its
own crate, unmodified by T2's existence.

---

## 3. Naming map (`T2.v` → Rust)

Only T2-introduced names appear here; T1 names keep their `t1/implementation.md` §3
mapping and are reached through `self.s1`.

| `T2.v` | Rust |
|--------|------|
| `State` (record) | `t2::model::Machine<P>`; fields below |
| `s1` | `pub s1: t1::model::Machine<P>` |
| `score` | `pub score: u64` |
| `level` | `pub level: u64` |
| `combo` | `pub combo: u64` (stored = visible combo + 1; see §4-T2b) |
| `perfectClear` | `pub perfect_clear: bool` |
| `totalClearedLines` | `pub total_cleared_lines: u64` |
| `gameover` (helper) | not a stored field; read as `self.s1.gameover` at call sites |
| `Init` | `Machine::new` |
| `Event` | implicit (five public `&mut self` methods, as in T1) |
| `UpdateS1` | not emitted — realized by delegating to `self.s1` and leaving the five T2 fields untouched (§4-T2d) |
| `MovePiece` | `Machine::move_piece(&mut self, dy, dx) -> bool` |
| `RotatePiece` | `Machine::rotate_piece(&mut self, cw) -> bool` |
| `FixPiece` | `Machine::fix_piece(&mut self, p_new) -> bool` |
| `FallStep` | `Machine::fall_step(&mut self, p_new) -> bool` |
| `LineClearPoints` | `line_clear_points(cleared_lines, level) -> u64` |
| `ComboPoints` | `combo_points(level, combo) -> u64` |
| `PerfectClearPoints` | `perfect_clear_points(perfect_clear, cleared_lines, level) -> u64` |
| `Points` | `points(cleared_lines, level, combo, perfect_clear) -> u64` |
| `clearedLines` (read of `s1'.(clearedLines)`) | `self.s1.cleared_lines` (a T1 field, set by T1 on the pre-clear grid) |
| `EmptyGridb` | `empty_gridb(g: &[Vec<Option<P::Piece>>]) -> bool` |
| `fₑ` | not emitted — `main.rs`'s action dispatch already maps input → method |
| `fₛ` | not emitted — `self.s1` *is* the projection |
| `Correct`, `LevelCorrect`, `NonDecreasing*`, `ScoreRisesOnClear`, `CorrectStep` | `proofs.md` only; not emitted |

---

## 4. Translation rules specific to T2

Every T1 rule (`t1/implementation.md` §4) applies unchanged wherever T2 touches T1 state,
reached exclusively through `self.s1`'s methods. New T2-only points:

- **§4-T2a — `cleared_lines` comes from the inner T1 state.** `T1.v` sets `clearedLines :=
  FullLineCount u` on the post-union, pre-clear grid `u` inside `T1.FixPiece`, and carries
  it through `MovePiece`/`RotatePiece` unchanged; `t1::model::Machine` exposes this as the
  public field `cleared_lines`. `t2::model::Machine::fix_piece` reads `self.s1.cleared_lines`
  immediately after calling `self.s1.fix_piece(p_new)` — no independent
  count, no before/after diff.

- **§4-T2b — `combo` carries the T2.v `+1`.** `T2.v` stores `combo = visible + 1`;
  `t2::model::Machine::combo` keeps that exact convention. The scoring/display combo is
  `combo − 1`, computed with `u64::saturating_sub(1)` — the natural floor-at-zero `nat`
  subtraction, needing no dedicated helper (`u64` subtraction below zero is either a panic
  in debug builds or a wrap in release; `saturating_sub` is the one call that matches
  Rocq `nat` subtraction's semantics directly).

- **§4-T2c — `level` is `nat` division.** `level := 1 + totalClearedLines / 10` is Rocq
  `nat` (floor) division; Rust's `u64` `/` is already floor division on non-negative
  operands, so `1 + total_cleared_lines / 10` is the direct transcription — no helper, no
  rounding adjustment.

- **§4-T2d — move/rotate/fall scalars ride along unchanged.** `MovePiece`, `RotatePiece`,
  and the move-branch of `FallStep` are `UpdateS1` of a T1 call: the five T2 fields are
  copied verbatim. In Rust this needs no explicit code at all — `move_piece`/
  `rotate_piece` mutate only `self.s1`, so `self.score`/`level`/`combo`/`perfect_clear`/
  `total_cleared_lines` are simply never touched by those methods (skill: `UpdateS1` =
  "delegate; do not write the untouched fields").

- **§4-T2e — saturating accumulation.** `score`, `combo`, and `total_cleared_lines` grow
  without a model bound (`T2.v` places no cap on them, unlike T1's bounded state). Every
  increment to one of these three fields uses `u64::saturating_add`, so a field simply
  stops growing at `u64::MAX` instead of wrapping. `saturating_add` tests for overflow
  before committing the addition (it cannot silently wrap the way plain `+` can in a
  release build), so no field is ever read past a genuine, representable value.
  - Only the **accumulators** are capped this way: `score`, `combo`, `total_cleared_lines`.
  - `level` is **not** capped directly; it is recomputed as `1 + total_cleared_lines / 10`.
    Since `total_cleared_lines ≤ u64::MAX`, `level ≤ 1 + u64::MAX / 10`, comfortably a valid
    `u64` — `level` is safe by inheritance, no clamp needed (proof obligation in §8.4).
  - `perfect_clear` is a flag (no cap). `cleared_lines ∈ [0,4]` and `points(...)`'s output
    is bounded by the formula itself (≤ ~2800·level); the unbounded accumulation site is
    `score + points`, so the cap lives on the `score` write, not on `points` itself.

---

## 5. Free functions emitted by `model.rs` (`T2.v` source order)

```
line_clear_points   (cleared_lines: u64, level: u64)                                -> u64
combo_points        (level: u64, combo: u64)                                        -> u64
perfect_clear_points(perfect_clear: bool, cleared_lines: u64, level: u64)           -> u64
points              (cleared_lines: u64, level: u64, combo: u64, perfect_clear: bool) -> u64
empty_gridb<P: Params>(g: &[Vec<Option<P::Piece>>])                                  -> bool
```

None of these read a `Params` item except `empty_gridb` (generic only over the cell type,
via `t1::model`'s `Cell`/`occ`, not over any other trait item) — matching skill §1's
"generic over the minimum it needs" rule. Argument order matches `T2.v` exactly: note
`combo_points` is `(level, combo)` and `perfect_clear_points` is `(perfect_clear,
cleared_lines, level)`.

```rust
// spec: LineClearPoints
pub fn line_clear_points(cleared_lines: u64, level: u64) -> u64 {
    match cleared_lines {
        0 => 0,
        1 => 100 * level,
        2 => 300 * level,
        3 => 500 * level,
        _ => 800 * level,
    }
}

// spec: ComboPoints
pub fn combo_points(level: u64, combo: u64) -> u64 {
    if combo > 0 { 50 * combo * level } else { 0 }
}

// spec: PerfectClearPoints
pub fn perfect_clear_points(perfect_clear: bool, cleared_lines: u64, level: u64) -> u64 {
    if !perfect_clear {
        return 0;
    }
    match cleared_lines {
        0 => 0,
        1 => 800 * level,
        2 => 1200 * level,
        3 => 1800 * level,
        _ => 2000 * level,
    }
}

// spec: Points
pub fn points(cleared_lines: u64, level: u64, combo: u64, perfect_clear: bool) -> u64 {
    line_clear_points(cleared_lines, level)
        + combo_points(level, combo)
        + perfect_clear_points(perfect_clear, cleared_lines, level)
}

// spec: EmptyGridb — routed through t1::model's occ (D1 of t1/implementation.md),
// correct regardless of which Cell-implementing type the grid holds.
pub fn empty_gridb<P: Params>(g: &[Vec<Option<P::Piece>>]) -> bool {
    g.iter().all(|row| row.iter().all(|c| !c.occ()))
}
```

`line_clear_points`/`combo_points`/`perfect_clear_points`/`points` are plain functions —
`Params`-free — since none of them reads a parameter; only `empty_gridb` needs `P: Params`,
and only to name the cell type.

---

## 6. `t2::model::Machine<P: Params>`

```rust
pub struct Machine<P: Params> {
    pub s1: t1::model::Machine<P>,  // spec: s1
    pub score: u64,                 // spec: score
    pub level: u64,                 // spec: level
    pub combo: u64,                 // spec: combo (stored = visible + 1, §4-T2b)
    pub perfect_clear: bool,        // spec: perfectClear
    pub total_cleared_lines: u64,   // spec: totalClearedLines
}
```

No `PhantomData<P>` marker: `s1: t1::model::Machine<P>` already mentions `P`.

### 6.1 Constructor — `Init p` (`T2.v`)

```rust
// spec: Init
pub fn new(p0: P::Piece, piece_source: impl FnMut() -> P::Piece) -> Self {
    Machine {
        s1: t1::model::Machine::new(p0, piece_source), // spec: T1.Init p
        score: 0,                                       // req-score-init
        level: 1,                                       // req-level-init
        combo: 0,
        perfect_clear: false,
        total_cleared_lines: 0,
    }
}
```

`t1::model::Machine::new`'s exact signature (piece source shape, `check_axioms` call site)
is `t1/implementation.md`'s to define; T2's constructor forwards to it unchanged (full-use,
skill §7.1) and writes only the five new fields.

### 6.2 `move_piece(dy, dx)` — `MovePiece` (`T2.v`) — full use

```rust
// spec: MovePiece — delegate; the five T2 fields are untouched (§4-T2d)
pub fn move_piece(&mut self, dy: i64, dx: i64) -> bool {
    self.s1.move_piece(dy, dx)
}
```

### 6.3 `rotate_piece(cw)` — `RotatePiece` (`T2.v`) — full use

```rust
// spec: RotatePiece — delegate; scalars unchanged
pub fn rotate_piece(&mut self, cw: bool) -> bool {
    self.s1.rotate_piece(cw)
}
```

### 6.4 `fix_piece(p_new)` — `FixPiece` (`T2.v`) — partial use, the only non-trivial T2 logic

Field writes happen strictly after every read that needs the pre-state value (skill §4b):
`pts` (step 5) reads `self.level` **before** `self.level` is overwritten (step 10), so
scoring always uses the level in effect *before* this fix, and the new level is derived
from `total2`, the value just written to `total_cleared_lines`.

```rust
// spec: FixPiece
pub fn fix_piece(&mut self, p_new: P::Piece) -> bool {
    let fired = self.s1.fix_piece(p_new); // spec: T1.FixPiece — mutates self.s1 in place
    if !fired {
        return false; // option_map None ⇒ no T2 update
    }
    let cleared_lines = self.s1.cleared_lines as u64;              // spec: s1'.(clearedLines) (§4-T2a)
    let combo2 = if cleared_lines == 0 {
        0
    } else {
        self.combo.saturating_add(1)                                // spec: combo' (§4-T2e)
    };
    let perfect_clear2 = empty_gridb::<P>(&self.s1.mg);              // spec: EmptyGridb s1'.(mg)
    let pts = points(cleared_lines, self.level, combo2.saturating_sub(1), perfect_clear2);
    // spec: Points … (combo'-1) — OLD level (§4-T2b, §4-T2c)
    let total2 = self.total_cleared_lines.saturating_add(cleared_lines); // spec: totalClearedLines'

    self.combo = combo2;
    self.perfect_clear = perfect_clear2;
    self.score = self.score.saturating_add(pts);                    // OLD level already used above
    self.total_cleared_lines = total2;
    self.level = 1 + total2 / 10;                                    // spec: 1 + totalClearedLines'/10 (NEW total)
    true
}
```

### 6.5 `fall_step(p_new)` — `FallStep` (`T2.v`)

```rust
// spec: FallStep
pub fn fall_step(&mut self, p_new: P::Piece) -> bool {
    if self.move_piece(-1, 0) {
        return true; // spec: T2.MovePiece (-1) 0 — delegate, scalars unchanged
    }
    self.fix_piece(p_new) // spec: T2.FixPiece — full §6.4 logic
}
```

Guards are mutually exclusive exactly as in T1 (`t1/implementation.md` §6, skill §6.6): the
inner move-branch and fix-branch never both fire, so `fall_step` never double-applies §6.4.

### 6.6 `gameover` — controller convenience, not a stored field

`T2.v`'s own `gameover` helper is `T1.gameover (s1 s)`, a pass-through read with no stored
counterpart. Realized the same way in Rust: call sites read `machine.s1.gameover` directly.
No wrapper method is added — Rust has no property-getter sugar that would make
`machine.gameover` read any more naturally than `machine.s1.gameover` does, so introducing
one would be a needless indirection with no `T2.v` counterpart to justify it.

### 6.7 `check_invariants` (default off, per `t1/implementation.md` D7)

```rust
// spec: T2.Correct's LevelCorrect conjunct, on top of T1's Correct — delegates for
// everything s1-shaped rather than re-checking type_ok/PieceOnFreeBlocks/etc.
pub fn check_invariants<P: Params>(s: &Machine<P>) {
    t1::model::check_invariants(&s.s1);
    debug_assert!(s.level == 1 + s.total_cleared_lines / 10); // LevelCorrect
}
```

`combo >= 0`, `total_cleared_lines >= 0`, `score >= 0` are type-level facts of `u64`
(skill §4h) — no runtime assertion needed for any of them, unlike a signed-integer or
floating-point representation would require.

---

## 7. `check_axioms`

`T2.v` adds no `Axiom` block, so `t2::model::check_axioms::<P>()` asserts nothing of its
own; it calls `t1::model::check_axioms::<P>()` and returns. `t2::model` also declares its
own `pub const CHECK_AXIOMS: bool = true;` (module-level, alongside `CHECK_INVARIANTS`,
§0.1), and `main.rs` gates on `model::CHECK_AXIOMS`/`model::check_axioms::<Instance>()` —
`t2::model`'s own items, not `t1::model`'s — once, before constructing any `Machine<P>`.

---

## 8. `proofs.md` (scope)

`t2/proofs.md` establishes that `model.rs` simulates `T2.v`, reusing:
1. `t1/model.rs ⊨ T1.v` (`t1/proofs.md`) for the `s1` half, in full.
2. `T2RefinesT1` (`T2.v`): every T2 transition's `s1` component is the corresponding T1
   transition, so `move_piece`/`rotate_piece`/the move-branch of `fall_step` need no new
   argument beyond "delegates to the already-verified T1 method; the five T2 fields are
   untouched by that call" (skill §7.1, full use).
3. New per-field obligations for `fix_piece` only: `score`, `level`, `combo`,
   `perfect_clear`, `total_cleared_lines` equal their `T2.FixPiece` values. Each is a direct
   transcription (§6.4) of a `let`-binding; the one subtlety, `cleared_lines`, is read from
   the inner state (`self.s1.cleared_lines` = `s1'.(clearedLines)`), which `t1/proofs.md`
   already establishes is the correct `FullLineCount u` value — T2 consumes it with no
   re-derivation.
4. `LevelCorrect` preservation (the extra `T2.Correct` conjunct, not covered by
   `T2RefinesT1`): `level = 1 = 1 + 0/10` at `new` (`total_cleared_lines = 0`), and
   `fix_piece` recomputes `level := 1 + total2/10` from the same `total2` it just wrote to
   `total_cleared_lines`; `move_piece`/`rotate_piece` leave both fields unchanged. Hence
   `level == 1 + total_cleared_lines/10` holds after every step, and in particular
   `level ≥ 1` always — discharging `ScoreRisesOnClear`'s premise that `Correct s` holds.
5. **Saturation soundness (§8.4).** The saturating adds (§4-T2e) are a Rust-representational
   safeguard with no `T2.v` counterpart; argue they preserve monotonicity and `level`'s
   range.
6. Out of scope (UI layer, safety-only boundary as in T1): fall speed (§15), banner timing
   (§14). No liveness claim.

### 8.4 Saturation soundness

`score` and `total_cleared_lines` are unbounded in `T2.v` — a long enough game exceeds any
fixed bound, so no machine-checked "never saturates" claim is made or needed. Instead
`model.rs` applies `u64::saturating_add` to the three accumulators (`score`, `combo`,
`total_cleared_lines`). `proofs.md` states two elementary facts about this:

- **Representation safety.** `saturating_add` never panics and never wraps — every
  accumulator field is a valid `u64` at every step, by construction of the standard-library
  primitive itself (no bespoke argument needed, unlike a hand-rolled cap would require).
- **Monotonicity preserved.** `a.saturating_add(b) ≥ a` for all `b`, so `NonDecreasingScore`
  / `NonDecreasingLevel` and `total_cleared_lines`'s monotonicity hold under saturation.
  `ScoreRisesOnClear` is unaffected until `score` reaches `u64::MAX` (after which it cannot
  strictly rise) — flagged as the one place saturation weakens the abstract property,
  reachable only after roughly 1.8·10¹⁹ points, i.e. never in real play.
- **`level` bound by inheritance.** `level = 1 + total_cleared_lines/10` and
  `total_cleared_lines ≤ u64::MAX` give `level ≤ 1 + u64::MAX/10`, itself far inside
  `u64`'s range — `level` needs no clamp of its own. This is the obligation justifying
  "cap accumulators only" in §4-T2e.

The saturating cap is a documented divergence from `T2.v` (which has no cap): `model.rs`
refines `T2.v` exactly up to the saturation point and conservatively (monotonically)
beyond it.

---

## 9. Tests (`tests/`)

Mirror T1's suite shape (`t1/implementation.md` §9) on T1's own fixture — `TestInstance`
(`PW=3`, two pieces `Bar`/`Corner`, a 6×5 board, `t1/tests/test_instance.rs`).

- `test_instance.rs` — not a copy: `include!(concat!(env!("CARGO_MANIFEST_DIR"),
  "/../t1/tests/test_instance.rs"))`, so the fixture has exactly one physical copy in the
  workspace and this file is a compile-time pointer to it — `T2.v` introduces no new
  parameters (§13), so there is nothing to add on top. Works both as the `mod fixture`
  every other T2 test file pulls in via `#[path = "test_instance.rs"]` and, like the
  original, as its own (empty) integration-test binary.
- `model_unit_test.rs` — golden vectors for `line_clear_points`/`combo_points`/
  `perfect_clear_points`/`points`/`empty_gridb`; `fix_piece` scenarios built on a
  `rest_bar_at_row0` helper (`Machine`'s public `s1` field, same D-Rust2 rationale as T1's
  `bar_at_rest`): a non-clearing fix (`combo` resets to 0, `score` unchanged), a single
  clear that leaves the board non-empty, a single clear that empties it (`perfect_clear`),
  a combo streak across two consecutive clearing fixes, a guard-failure (no T2 field
  changes), ten single-line clears in a row to cross a `level` boundary; a
  move/rotate-leaves-T2-fields-untouched check; `check_invariants` passing on a fresh
  machine and catching a deliberately broken `LevelCorrect`.
- `model_properties_test.rs` — `proptest`, generic-free (fixed to `TestInstance`): every
  action preserves `LevelCorrect` and `level ≥ 1`, delegates to `t1::model::type_ok`/
  `t2::model::check_invariants` for the rest of `Correct`, and checks `score`/`level`/
  `total_cleared_lines` are non-decreasing and `gameover` is monotone. Detecting "a clear
  happened this step" uses the **`total_cleared_lines` delta**, never `s1.cleared_lines > 0`
  in isolation: `cleared_lines` rides through `move_piece`/`rotate_piece` unchanged, so a
  `Fall` that resolves as a move would leave a previous fix's `cleared_lines` value in place
  and give a false positive — `ScoreRisesOnClear` is checked exactly on that delta.
- `model_fuzz_test.rs` — same dependency-free PRNG-driven shape as T1's: `N` seeds × `M`
  steps, `type_ok`/`LevelCorrect`/monotonicity/`ScoreRisesOnClear` (same delta rule) after
  every single step. Deliberately does not re-check T1's four grid-shaped `Correct`
  conjuncts independently — `t1/tests/model_fuzz_test.rs` already covers that on the same
  engine, and `t2::model` never mutates grid content itself (§0.1).
- `oracle.rs` — a from-scratch reimplementation of the five T2-only fields only (not the
  `s1` half: `t1/tests/oracle.rs` already differentially checks T1's grid algebra against
  its own independent reimplementation, so re-doing that here would test `t1::model::
  Machine` a second time, not anything new). Reads `s1.cleared_lines`/`s1.mg` from the
  `Machine<P>` under test as ground truth — exactly as `t2::model::Machine::fix_piece`
  itself does (§4-T2a) — and independently re-derives `score`/`level`/`combo`/
  `perfect_clear`/`total_cleared_lines` to check against it every step. `FallStep` is
  decomposed into its `move_piece`/`fix_piece` calls explicitly in the driver (§6.5), so the
  oracle observes which branch fired directly from `move_piece`'s return value rather than
  inferring it after the fact.

The SRS grids in `t1::instance` are validated by `t1::model::check_axioms` at startup
(§7), not by these suites — the same boundary as T1 (`t1/implementation.md` §13.6).

---

## 10. Acceptance oracle (definition of correct regeneration)

A regeneration is correct iff:
1. Every `T2.v` definition with a §3 mapping is realized with the mapped name/behavior;
   every "not emitted" entry is absent.
2. `model.rs` constructs and calls into `t1::model::Machine`/free functions and never
   reimplements one.
3. `tests/` passes on the small fixture: unit + fuzz fully; properties under `proptest`.
4. The differential oracle (`oracle.rs`) agrees with `model.rs` on all five T2-only state
   components (`score`/`level`/`combo`/`perfect_clear`/`total_cleared_lines`) over every
   generated trace — the `s1` half is out of this oracle's scope by design (§9).
5. `fix_piece` reads `cleared_lines` from the inner T1 state immediately after the inner
   fix (§4-T2a), and scores with the **old** `level` while setting the **new** `level` from
   the updated total (§6.4 ordering).

---

## 11. Instantiation (`t2/src/instance.rs`)

```rust
pub use t1::instance::{piece_color, Piece, Tetris};
```

`T2.v` introduces no abstract parameters, so `instance.rs` re-exports `t1::instance`'s
items rather than restating them. `t1::model::check_axioms::<Tetris>()` (§7) validates the
underlying grids/piece set at construction time, exactly as it does for T1.

Fall-speed constants are a **`main.rs`** concern (§15), not `instance.rs`: they are UI
pacing, not a `Params` item.

---

## 12. Generator determinism rules

Inherit `t1/implementation.md` §12 verbatim (temperature 0, frozen orders, no invented
behavior, ambiguity → TODO, closure-scope rule). T2 addition:

- **Reuse over restatement.** Never copy a T1 definition into `model.rs`/`view.rs`/
  `main.rs` when it can be called through `t1::…` instead. The only intentional new code is
  the T2-specific logic in `model.rs` (§5–§7), `view.rs`'s panel/banner additions (§14), and
  `main.rs`'s fall-speed/banner-timing additions (§15) — everything else is a call into the
  `t1` crate.

---

## 13. `instance.rs` parameters

None beyond `t1`'s. See §11. (Section kept for parallelism with `t1/implementation.md`
§13; intentionally empty of new content.)

---

## 14. `view.rs` — renderer (grid + left info panel + transient banners)

### 14.1 Public API

```rust
pub use t1::view::RenderConstants; // byte-identical fields (hm, wm, pw, fy, fx, fh, fw);
                                     // reused per §12, not redeclared

pub struct Banner {
    pub combo: u64,
    pub perfect_clear: bool,
    pub t: f64, // macroquad::time::get_time() at capture (§15.2)
}

pub fn render<P: Params>(
    constants: &RenderConstants,
    machine: &Machine<P>,
    piece_color: impl Fn(P::Piece) -> [f32; 4],
    banner: Option<&Banner>,
    font: Option<&Font>,
) { … }
```

`view.rs` imports nothing from `instance.rs` (same decoupling as `t1::view`). `t1::view`'s
`Layout`/`compute_layout` and grid-drawing sub-procedures (`draw_block`, `draw_background`,
`draw_grid_lines`, `draw_grid`, `draw_piece`) are `pub` expressly so a wrapper layer can
reuse them (`t1/implementation.md` §14.1); `t2::view` is that wrapper for the grid,
embedding `t1::view::Layout` as `base` and delegating `draw_block`/`draw_grid`/
`draw_background`/`draw_grid_lines` straight through via `pub use`, and `draw_piece`
through a one-line adapter that unwraps `self.s1` (skill §7) — none of the five have any
panel-aware logic, so there is nothing T2-specific to add to them. `font` is loaded once
by `main.rs` (§15.9) and passed in by reference every frame; `render` never loads or owns
it.

The panel (`Layout`'s own `panel_left`/`panel_width`, `PanelMetrics`, `draw_panel`,
`draw_banners`, `draw_text_label`) and the font-aware `draw_game_over` have no `t1::view`
counterpart — T1 has no panel and no loaded `Font` at all — so they're new code here, not
a duplication the reuse principle (§12) forbids; `draw_game_over` reuses T1's
`GAME_OVER_TEXT_COLOR`/`GAME_OVER_BG_COLOR` values (`pub use`) even though its drawing
logic differs (panel-excluding region, explicit `Font`), since the two are meant to look
the same, just cover a different area. These new items are themselves `pub`, along with
`BG_COLOR`/`LABEL_COLOR` (the latter reused from T1, the former re-exported from it): a
further wrapper layer (`t3`, or any future one stacking on `t2`) reuses them directly on
`self.s2`/`self.base` instead of redefining a parallel copy (§12's reuse principle,
applied one layer up — see `t3/implementation.md` §14). `draw_panel` takes its starting y
as an explicit `top` parameter (rather than deriving it internally from
`panel_metrics(layout.panel_width).margin_y`) for the same reason: this crate's own
`render` passes that margin, but a wrapper with content above the panel passes its own
lower starting point.

### 14.2 Layout / scaling

`cell_size`/`origin_x`/`origin_y` are exactly `t1::view::compute_layout`'s own `Layout`
(§14.2 of `t1/implementation.md`), embedded unmodified as `base` — the panel does not
participate in the grid's own centering. The panel's width is relative to the live
window, not to the cell size (a cell can be tiny when the grid is large), and is
recomputed from `screen_width()` fresh every frame — no cached dimension, no resize
handler, the same per-frame-recomputation discipline `t1/implementation.md`
D-Grid-Centering already uses for `cell_size` itself. The panel is placed **inside the
left margin the centered grid already leaves**, snug against the grid's left edge rather
than pinned to the window edge, clamped so it never spills past `x = 0` on a
narrow/near-square window:

```rust
const PANEL_FRACTION: f32 = 0.22;
const PANEL_MIN_PX: f32 = 120.0;
const PANEL_MAX_PX: f32 = 360.0;
const PANEL_GRID_GAP_FRACTION: f32 = 0.08; // gap between panel and grid, relative to panel width

fn desired_panel_px() -> f32 {
    (screen_width() * PANEL_FRACTION).clamp(PANEL_MIN_PX, PANEL_MAX_PX)
}

pub struct Layout {
    pub base: t1::view::Layout,
    pub panel_left: f32,
    pub panel_width: f32,
}

pub fn compute_layout(constants: &RenderConstants) -> Layout {
    let base = t1::view::compute_layout(constants);
    let desired = desired_panel_px();
    let gap = desired * PANEL_GRID_GAP_FRACTION;
    let panel_width = desired.min((base.origin_x - gap).max(0.0));
    let panel_left = (base.origin_x - gap - panel_width).max(0.0);
    Layout { base, panel_left, panel_width }
}
```

### 14.3 Coordinate transform

Not redefined: `t1::view::cell_origin` stays private to `t1::view` (§14.1 of
`t1/implementation.md`) — every grid-cell placement in this crate happens inside the
`pub` sub-procedures it reuses (§14.4), never through the transform directly.

### 14.4 Sub-procedures

```rust
pub use t1::view::{BG_COLOR, GAME_OVER_BG_COLOR, GAME_OVER_TEXT_COLOR};
pub use t1::view::{draw_background, draw_block, draw_grid, draw_grid_lines};

pub fn draw_piece<P: Params>(
    machine: &Machine<P>,
    constants: &RenderConstants,
    layout: &t1::view::Layout,
    piece_color: &impl Fn(P::Piece) -> [f32; 4],
) {
    t1::view::draw_piece(&machine.s1, constants, layout, piece_color)
}
```

`draw_block`/`draw_background`/`draw_grid_lines`/`draw_grid` are plain re-exports: none of
the four have panel-aware logic, so `t1::view`'s versions are reused byte-for-byte.
`draw_piece` needs a one-line adapter instead of a bare `pub use`, since `t2::model::Machine<P>`
wraps `t1::model::Machine<P>` as `s1` (skill §7) — otherwise it's `t1::view::draw_piece`'s
exact body. `draw_game_over`'s dimmed rectangle spans the grid region only (`[origin_x,
screen_width())`), leaving the panel readable at game over — genuinely new relative to
`t1::view::draw_game_over` (no panel to exclude there, and no loaded `Font`), reusing only
T1's colours. The text itself is centered on the grid's own box
(`[origin_x, origin_x + wm * cell_size)`), not the wider dimmed rectangle: the dimmed
rectangle deliberately also covers the empty margin past the grid's right edge (so nothing
right of the panel is left undimmed), but centering the text against that wider width
would drag it off the grid's actual center by half that margin — hence the separate
`grid_width` and the `constants` parameter needed to compute it:

```rust
pub fn draw_game_over(constants: &RenderConstants, layout: &Layout, font: Option<&Font>) {
    let text = "GAME OVER";
    let font_size = (layout.base.cell_size * 1.2).max(16.0).round() as u16;
    let dims = measure_text(text, font, font_size, 1.0);
    let (w, h) = (screen_width(), screen_height());
    let grid_x0 = layout.base.origin_x;
    let grid_width = constants.wm as f32 * layout.base.cell_size;
    draw_rectangle(grid_x0, 0.0, w - grid_x0, h, GAME_OVER_BG_COLOR);
    draw_text_label(text, grid_x0 + (grid_width - dims.width) / 2.0, (h - dims.height) / 2.0 + dims.offset_y,
                     font_size, GAME_OVER_TEXT_COLOR, font);
}
```

New T2 sub-procedures — `draw_text_label`, `panel_metrics`:

```rust
pub fn draw_text_label(text: &str, x: f32, y: f32, font_size: u16, color: Color, font: Option<&Font>) {
    draw_text_ex(text, x, y, TextParams { font, font_size, font_scale: 1.0, color, ..Default::default() });
}

pub struct PanelMetrics {
    pub margin_y: f32,
    pub margin_x: f32,
    pub label_font: u16,
    pub value_font: u16,
    pub banner_font: u16,
}

pub fn panel_metrics(panel_width: f32) -> PanelMetrics {
    PanelMetrics {
        margin_y: panel_width * 0.12,
        margin_x: panel_width * 0.24,
        label_font: (panel_width * 0.10).max(9.0) as u16,
        value_font: (panel_width * 0.10).max(10.0) as u16,
        banner_font: (panel_width * 0.10).max(9.0) as u16,
    }
}
```

`panel_width` is the *only* scale reference here, for both axes, deliberately: this design
has no separate "panel height" (§14.2 — `Layout` never computes one; the panel is just a
column of text lines, as tall as its content needs, not a sized box). `margin_y`'s job is
to look proportioned next to `label_font`/`value_font`/`banner_font`, which are themselves
`panel_width`-derived — scaling `margin_y` off `panel_width` too keeps it in step with the
text sizes it surrounds. Deriving it from `screen_height()` or `cell_size` instead would
decouple it from the thing it actually needs to stay proportioned to, for no benefit — a
vertical-looking quantity being `panel_width`-scaled is intentional, not a leftover from
`margin_x`/`margin_y` having once been a single field.

Every text draw — panel labels/values, banners, `GAME OVER` — goes through
`draw_text_label`, i.e. `draw_text_ex` with an explicit loaded `font` (§15.9), never
`draw_text`'s built-in bitmap font: macroquad's default font is a small, fixed-resolution
bitmap that visibly pixelates once stretched to panel-sized text; a real TTF rasterizes
fresh vector glyphs at whichever `font_size` is requested, so text stays crisp at any HUD
scale. `draw_panel` and `draw_banners` both call `panel_metrics` rather than each computing
its own margin/font sizes — they lay out the same column, so one source keeps their
fractions from drifting apart.

```
draw_panel(layout, machine, font) -> f32
  — draws, top-down, left-aligned at layout.panel_left + panel_metrics's margin_x:
      "SCORE"  label  + score        (value on the next line, larger)
      "LEVEL"  label  + level
    Font sizes come from panel_metrics (relative to panel_width), not cell_size. Decimal,
    no digit grouping. Returns the y-coordinate immediately below the LEVEL block, so
    draw_banners can stack under it without hardcoding its height.

draw_banners(layout, below_level_y, banner: Option<&Banner>, font)
  — when Some, draws below below_level_y, stacked so the two lines never overlap:
      if banner.combo >= 2:     "<n>-hit combo!" with n = banner.combo (verbatim — see below)
      if banner.perfect_clear:  "Perfect clear!"
    Both lines are allotted a fixed slot height (banner_font × 1.4) so the perfect-clear
    line's position is independent of whether the combo line is drawn (reserve the combo
    slot even when empty, so "Perfect clear!" never jumps).
```

**Combo display convention.** The stored `combo` field (`T2.v`'s own, offset by +1 for
scoring purposes — §4-T2b) is displayed **as-is**, not `combo - 1`: the first
line-clearing fix leaves `combo == 1` (no banner shown — a single clear is not yet a
combo), the next consecutive clearing fix leaves `combo == 2` and shows "2-hit combo!",
the one after that leaves `combo == 3` and shows "3-hit combo!", and so on — the displayed
number is simply the count of consecutive clearing fixes. This is a UI-layer display
choice with no `T2.v` counterpart; the model's own `combo` field exists to drive
`comboPoints`'s scoring formula (which does use `combo - 1` internally, §6.4 of this
document), and the two uses are independent of each other. Both banners read the
snapshotted `Banner` `main.rs` passes in (§15.2), not `machine`'s live fields — a fix that
happens after the frame's snapshot was captured must not retroactively change what this
frame draws.

### 14.5 Piece color parameter

As `t1/implementation.md` §14.5: a `piece_color` closure parameter, no default baked into
`view.rs`.

### 14.6 Call order inside `render`

```
1. clear_background       (whole canvas, including the panel area — t1's own convention)
2. draw_panel              (score / level)
3. draw_banners             (combo / perfect-clear, if banner is Some)
4. draw_grid                 (locked blocks)
5. draw_background             (forbidden-zone tint)
6. draw_grid_lines               (grid lines)
7. draw_piece                     (active piece, clipped)
8. if machine.s1.gameover: draw_game_over   (overlay spans the grid area only)
```

---

## 15. `main.rs` — entry point

Extends `t1/implementation.md` §15's shape. Same input model (keyboard + gamepad, shared
DAS engine, one main loop) — `Action`/`LogicalKeys`/`RepeatTimer`/`window_conf`/
`random_piece`/`DAS_DELAY`/`ARR`/`any_action_just_pressed` are imported directly from
`t1::misc` (§15.2 of `t1/implementation.md`, §0.1 above), not re-declared. Only `fire` is
crate-local: `t2/main.rs` defines its own free `fn fire<P: Params>(action: Action,
machine: &mut Machine<P>)` calling the T2 wrapper's methods (`move_piece`/`rotate_piece`/
`fall_step` on `Machine<P>`, not on `Machine<P>.s1` directly — so a T2-restart still goes
through `t2::model::Machine::new`, not `t1::model::Machine::new`), same reason
`t1::misc::Action` excludes `fire` as a method in the first place.

### 15.1 Fall speed — classic gravity curve

```rust
const BASE_PERIOD_SECS: f64 = 1.0;   // level 1 (1.0 × 0.8^0)
const MIN_PERIOD_SECS: f64 = 0.016;  // floor (~one 60 Hz frame)
const EPS: f64 = 1e-6;               // keeps the base positive for very high levels

// spec-external: time-per-cell(level) = (0.8 − (level−1)·0.007)^(level−1), floored.
fn fall_period(level: u64) -> f64 {
    let base = (0.8 - (level as f64 - 1.0) * 0.007).max(EPS);
    let secs = base.powf(level as f64 - 1.0);
    (BASE_PERIOD_SECS * secs).max(MIN_PERIOD_SECS)
}
```

Level 1 → 1.000s, 2 → 0.793s, 5 → 0.394s, 10 → 0.118s, flooring at `MIN_PERIOD_SECS` for
every `level ≥ 1` (the `EPS` guard keeps `base` positive so `powf` never receives a
negative base at implausibly high levels). A UI-pacing function with no `Params`/`Machine`
counterpart, same category as `t1/implementation.md`'s `FALL_PERIOD_SECS` (D16 there):
`T2.v` places no requirement on fall timing either.

### 15.2 `after_action(now)` — level-change rescheduling, banner capture

The level-schedule and banner state are bundled into one `RunState` (main-loop-local, no
`Params`/`Machine` counterpart — same category as fall speed itself, §1's scope note),
rather than threaded as five separate `&mut` parameters:

```rust
const BANNER_SECS: f64 = 1.2;

struct RunState {
    prev_level: u64,
    current_gravity_period: f64,
    last_fall: f64,
    prev_total_cleared_lines: u64,
    banner: Option<view::Banner>,
}

impl RunState {
    fn fresh(now: f64) -> Self {
        RunState { prev_level: 1, current_gravity_period: fall_period(1), last_fall: now,
                   prev_total_cleared_lines: 0, banner: None }
    }
}

fn after_action<P: Params>(machine: &Machine<P>, now: f64, run: &mut RunState) {
    if machine.level != run.prev_level {
        run.current_gravity_period = fall_period(machine.level);
        run.prev_level = machine.level;
        run.last_fall = now; // faster gravity takes effect now, discarding whatever had
    }                          // already accumulated toward the previous period

    if machine.total_cleared_lines > run.prev_total_cleared_lines {
        run.banner = Some(view::Banner { combo: machine.combo, perfect_clear: machine.perfect_clear, t: now });
    }
    run.prev_total_cleared_lines = machine.total_cleared_lines;
}
```

Called after every state-changing input (tick, key, gamepad), on the same clock the main
loop already uses for input — not a second, independent timer. Clear detection compares
`total_cleared_lines` before/after rather than testing `s1.cleared_lines > 0` in isolation,
for the same false-positive reason noted in §9's test rules: `cleared_lines` survives a
`Move`/`Rotate` unchanged, so a `Fall` that resolves as a plain move must not be read as a
clear. `run.banner` expires (`None`) once `now - run.banner.t > BANNER_SECS`, checked once
per frame before `render` (mirroring `t1/implementation.md`'s per-frame structure, one more
check added).

### 15.3 Restart

On gameover-restart, in addition to replacing `machine` with a fresh
`Machine::<Instance>::new(...)`, replace `run` with `RunState::fresh(now)` — in place of
`t1/implementation.md`'s single fixed `FALL_PERIOD_SECS` restart.

### 15.4 Everything else

`Action`/`LogicalKeys`/`RepeatTimer`/`window_conf`/the DAS/ARR constants are
`t1::misc`'s (§15.2 of `t1/implementation.md`), imported unchanged rather than
re-declared (§0.1). `process_input`/`fire` are `t2/main.rs`'s own — `process_input`'s
shape carries over unchanged from `t1/implementation.md` §15.5, but it is not itself
shared via `t1::misc` (that file's own note on why: no trait spans every
`ti::model::Machine<P>`'s `fall_step` once `T4.v`'s bag-based one exists). The only new
call site inside `process_input` is routing every action's effect through `after_action`
(§15.2) instead of leaving fall pacing on a single fixed-period check; `fire` is generic
over `t2::model::Machine<P>` (§15) rather than `t1::model::Machine<P>`.

### 15.9 Font

```rust
const FONT_BYTES: &[u8] = include_bytes!("../../assets/JetBrainsMono-Regular.ttf");
```

Loaded once, synchronously, before the frame loop starts:

```rust
let font = load_ttf_font_from_bytes(FONT_BYTES).expect("embedded font must parse");
```

and passed to every `view::render` call as `Some(&font)`. Embedded at compile time
(`include_bytes!`) rather than loaded from a runtime path (`load_ttf_font`, async): the
binary is then self-contained, with no working-directory-relative asset lookup to get
wrong at deployment. `assets/` lives once at the workspace root (a sibling of `t1/`, `t2/`,
`t3/`, `t4/`), not inside any one crate; `include_bytes!`'s path is relative to this file
(`src/main.rs`), so `../../` reaches it from every crate alike. `assets/JetBrainsMono-Regular.ttf`
(JetBrains Mono, SIL Open Font License 1.1) ships alongside `assets/OFL.txt`. Any other
TTF/OTF can be substituted by replacing the file `include_bytes!` points at — nothing else
in `view.rs`/`main.rs` is font-specific beyond the `Option<&Font>` parameter threaded
through §14.
