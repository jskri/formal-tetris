# implementation.md — ImplementationInstructions for T6 (Rust)

Per-model instructions for the transformation

```
FormalModel (T6.v)  ×  ImplementationInstructions (this file)
      ── rocq-to-rust skill ──▶  Code (model.rs, view.rs, main.rs, instance.rs, misc.rs)
                                  ×  Proofs (proofs.md)  ×  Tests (tests/)
```

This file is the **T6-Rust-specific source of truth**, applying the `rocq-to-rust` skill's
general rules — in particular §7, "translating a module that wraps another" — to `T6.v`.
`t5/implementation.md` (and transitively `t4`/`t3`/`t2`/`t1/implementation.md`) are the frozen
sources of truth for everything T6 reuses unchanged; this file states only what is specific to
T6. Generated artifacts are never hand-edited: to change one, change this file or `T6.v` and
regenerate. All references to `T6.v`/`T5.v`/`T4.v`/`T3.v`/`T2.v`/`T1.v` are **by definition
name**.

## 0. Inputs, outputs, and what is frozen

Codegen-time inputs:
- `T6.v` — the abstract model (refines `T5.v` for `Event5` events only — see §1).
- `T5.v`/`t5/implementation.md` (and transitively `T4.v`/`T3.v`/`T2.v`/`T1.v`) — reused in
  full.
- this file.
- the `rocq-to-rust` skill (cited as `skill §N`).

Runtime input (NOT codegen-time, NOT derived from `T6.v`):
- `t6/src/instance.rs` — pure re-export of `t5::instance` (§11). `T6.v` declares no
  `Parameter` of its own, and `t6::model` defines no `Params` trait of its own either (§6.0),
  so there is nothing for `instance.rs` to `impl`.

Outputs: `t6/src/model.rs`, `t6/src/view.rs`, `t6/src/main.rs`, `t6/src/misc.rs`,
`t6/src/instance.rs`, `t6/Cargo.toml`, `t6/proofs.md`, `t6/tests/` (§9). A generation is
**correct** iff `model.rs` refines `T5.v` on `Event5` events (established by `proofs.md`); the
acceptance oracle (§10) is the operational check that provides evidence for this, it is not
itself the definition.

### 0.1 Files reused from `t1`–`t5` unchanged (not regenerated, imported as path dependencies)

| item | role in T6 |
|------|-----------|
| `t5::model::Params` | the parameter trait, reused directly as `t6::model::Params` (§6.0) — `T6.v` adds no new abstract parameter |
| `t5::model::Machine<P>` | reused directly as `t6::model::Machine<P>` via a type alias (§1, §6.1) — not wrapped in a new field |
| `t5::model::{check_axioms, check_invariants, CHECK_AXIOMS, CHECK_INVARIANTS}` | reached by their `t5::model::` path, not redefined (§7) — `T6.Correct = T5.Correct`, no new axiom |
| `t1::model::{valid, new_piece_yx_state}` | `new_piece_yx_state` relocates `px` for each kick attempt; `valid` underlies the new `can_rotate_piece` (§0.2) — both already `pub` in `rs_t1_src_model.rs`, no visibility patch needed |
| `t5::view` (all of it) | re-exported by `t6::view` (§14) — no new visual state; `render::<P>` already type-checks against `t6::model::Machine<P>` since it *is* `t5::model::Machine<P>` |
| `t5::instance` (all of it) | re-exported by `t6::instance` (§11) |
| `t5::misc::{Action, any_action_just_pressed}` | re-exported by `t6::misc` (§15) — no new player-facing action, no new keybinding |
| `t1::misc::{DAS_DELAY, ARR, window_conf, LogicalKeys, RepeatTimer, random_piece}` | `main.rs`-only primitives; `t6/main.rs` imports them directly |

`t6/src/model.rs` therefore contains exactly one new piece of state-machine logic:
`rotate_kick_piece`. Nothing in `t6` reimplements grid algebra, rotation validity, line
clearing, scoring, the hold slot, the bag/preview mechanism, or the shadow/ghost computation.

### 0.2 Prerequisite patch to `t1/src/model.rs`: `can_rotate_piece`

The kick logic needs to know whether a plain rotation *would* fire, without performing it —
`RotateKickPiece` fires only when `T5.RotatePiece` would not (`T6.v`'s own exclusivity guard).
`t1::model::rotate_piece` computes its guard inline, once, and has no reason to factor it out
for its own sake; only this wrapper needs the guard as a standalone, side-effect-free
predicate. This is implementation freedom — `T6.v` names no such definition — with a direct
structural precedent already in `t1::model`: `t1::model::can_move_piece` factors `move_piece`'s
own guard out the same way, *excluding* the `gameover` check (left to the caller).
`can_rotate_piece` follows the identical shape:

```rust
// spec: the guard `RotatePiece` computes inline, factored into a named, side-effect-free
// predicate — same division of labor as `can_move_piece` (gameover excluded, checked by the
// caller). No `T1.v` counterpart: `T1.RotatePiece` needs no such definition, only a caller
// wrapping kick logic around it does.
pub fn can_rotate_piece<P: Params>(cw: bool, s: &Machine<P>) -> bool {
    let delta = if cw { -1 } else { 1 };
    let pr2 = (s.pr as i64 + delta).rem_euclid(4) as u8;
    valid::<P>(&s.mg, s.p, s.py, s.px, pr2)
}
```

`can_rotate_piece(cw, s)` is true iff `s.rotate_piece(cw)` would fire on a machine currently in
state `s` that is not already `gameover` — the same equivalence `can_move_piece` already
carries relative to `move_piece`. `t1/proofs.md` gains `L-can-rotate-piece`, a
definitional-equivalence lemma (no independent Rocq statement to be equivalent to beyond the
guard expression it's extracted from), the same shape `L-can-move-piece` already has.

`new_piece_yx_state` needs **no** patch: it already exists in `t1::model` (added for T5's
`drop_piece`), overrides both `py`/`px` unconditionally, and is exactly what relocates `px`
for each kick attempt while holding `py` fixed.

This patch is a prerequisite for T6 codegen but is not itself part of T6's own output.

### 0.3 No flattening retrofit needed

`t5/implementation.md` §0.2's `t4::view` visibility widening, and every prior layer's own
patches, are already in place and untouched by T6. Every layer reaches nested state via direct,
explicit field-chain access (`machine.s4.s3.s2.s1.…`), never through an interposed getter — so
there is no flattening accessor to retrofit at this layer either.

---

## 1. The refinement, and the structural departure

`T6.State = T5.State` (`T6.v`'s own `Definition State := T5.State`) — a type alias, not a new
record. This is the first model in the chain with no new state field to embed. Every prior
layer (`T2`–`T5`) wrapped its predecessor's `Machine<P>` in a new struct because there was a
new field (`hold`, `bag`, `gy`, …) needing a home; here there is nothing to wrap, so a wrapping
struct would misrepresent `T6.v`'s own definition. The faithful translation is a **type
alias**:

```rust
pub type Machine<P> = t5::model::Machine<P>;
```

— literally the same type, not a new struct embedding it. Rust has no inheritance, and
coherence rules forbid adding an inherent `impl<P> t5::model::Machine<P> { … }` block from the
`t6` crate — inherent impls are only legal in the crate that defines the type. The one new
method is instead added via an **extension trait** (§6.1) — the idiomatic Rust mechanism for
"add a method to a type you don't own, no new field."

Refinement mapping (`T6.v`'s own `fₑ := id`, `fₛ := id`): both trivial, and trivial in an even
stronger sense than `T6.v`'s own statement suggests — since `Machine<P>` *is*
`t5::model::Machine<P>`, there is no projection to define at all; the Rust-to-Rocq mapping `α₆`
is `α₅` unchanged, applied to the same value (§8.2). The refinement holds only for `Event5`
events; `RotateKick` is excluded, the same shape as T3/T5 excluding `Hold`/`Drop`. Per skill
§7.1's three-way classification:

- `move_piece`, `rotate_piece`, `fix_piece`, `fall_step`, `hold_piece`, `drop_piece` are **full
  uses**, realized by identity (the alias), not by delegating calls or inheritance. `t6::model`
  defines none of these; they are `t5::model::Machine<P>`'s own inherent methods, reachable
  directly on any `t6::model::Machine<P>` value because the two types are one and the same.
- `rotate_kick_piece` is a **no-use**. No T5/T4/… action is invoked as a subterm before the
  exclusivity check; the kick attempts do call `self.rotate_piece(cw)` (a genuine reuse), but
  only after establishing, via a pure check, that the plain call would otherwise not have
  fired — see §4-T6b.

Rejected alternative, and why: a composite method (e.g. `rotate_with_kick(cw)` trying both in
sequence, exposed as the "main" rotate entry point on `Machine<P>` itself) was considered and
rejected. `T6.v` defines no event combining `RotatePiece` and `RotateKickPiece` — that
combination is a caller's sequencing decision, not a model definition. The sequencing belongs
in `main.rs` (§15.2), which already owns orchestration the model doesn't speak to (DAS timing,
gamepad polling, restart-on-gameover).

---

## 2. File layout & module shape

```
t6/
  Cargo.toml            # depends on t1, t2, t3, t4, t5 by path (workspace member)
  src/
    lib.rs               # pub mod instance; misc; model; view — same role as t5's
    misc.rs               # pub use t5::misc::*; — no new player-facing action (§15)
    instance.rs            # pub use t5::instance::*; — no new Params trait to impl (§11)
    model.rs                 # T6 engine: Machine<P> alias + RotateKickPieceExt (§5–§7)
    view.rs                   # pub use t5::view::*; — no new visual state (§14)
    main.rs                    # entry point: CW/CCW try a kick on plain-rotation failure (§15)
  proofs.md              # refinement proof, delta over t5/proofs.md (§8)
  tests/
    test_instance.rs     # own `include!` copy of t1's fixture, same shape as t5's (§9)
    model_unit_test.rs
    model_properties_test.rs
    model_fuzz_test.rs
    oracle.rs             # executable T6.v reference for rotate_kick_piece only (§9)
```

The workspace root's `Cargo.toml` gains `"t6"` in `members`; `t1`–`t5` remain independently
buildable, unmodified in behavior by T6's existence (only the additive `can_rotate_piece`
patch, §0.2).

---

## 3. Naming map (`T6.v` → Rust)

Only T6-introduced names appear here; T1–T5 names keep their own maps and are reached through
`t5::model::Machine<P>`'s existing field chain.

| `T6.v` | Rust |
|--------|------|
| `State` (`= T5.State`) | `pub type Machine<P> = t5::model::Machine<P>;` — a type alias, not a new struct |
| `RotateKickPiece` | `RotateKickPieceExt::rotate_kick_piece(&mut self, cw: bool) -> bool` (extension trait, §6.1) |
| `Event`, `Next` | implicit (`main.rs` dispatch + method args, as T1–T5); the `Event5` case is realized by identity, not a forward call |
| `fₑ`, `fₛ` | `proofs.md` only; not emitted (both `id`, and trivially so — §1) |
| `Correct` (`= T5.Correct`) | not emitted — no new invariant; `check_invariants` is `t5::model::check_invariants`, reached by its own path, never redefined |
| `s5`, `MovePiece`, `RotatePiece`, `FixPiece`, `HoldPiece`, `mg`, `p`, `pyx`, `pr`, `gameover`, `clearedLines`, `score`, `level`, `combo`, `perfectClear`, `totalClearedLines`, `hold`, `swapped`, `d`, `gy`, `px`, `NewPieceYXState`, `CorrectWithoutGameover` (T6.v's "helpers for refining models" section) | not emitted — each is `T5.v`'s own, reached unchanged through `Machine<P>` being `t5::model::Machine<P>` itself; `proofs.md` cites them by their `t5::model`/`t1::model` paths directly |

---

## 4. Per-definition translation rules (T6-specific)

- **§4-T6a. `can_rotate_piece`** — lives in `t1::model`, not `t6::model` (§0.2). Not a `T6.v`
  definition itself; the prerequisite predicate `rotate_kick_piece`'s guard is built from.

- **§4-T6b. `rotate_kick_piece(cw)`:**
  ```rust
  // spec: RotateKickPiece
  fn rotate_kick_piece(&mut self, cw: bool) -> bool {
      let s1 = &self.s4.s3.s2.s1;
      if s1.gameover || t1::model::can_rotate_piece::<P>(cw, s1) {
          return false; // req-piece-kick: exclusive with a plain rotation that would fire
      }
      let (orig_py, orig_px) = (s1.py, s1.px);
      // spec: RotateKickPiece's left attempt — T5.RotatePiece clockwise (T5.NewPieceYXState
      // (py s, px s - 1) s)
      t1::model::new_piece_yx_state::<P>(orig_py, orig_px - 1, &mut self.s4.s3.s2.s1);
      let mut fired = self.rotate_piece(cw); // reuse — T5's own method, full use
      if !fired {
          // spec: the right attempt, relative to the ORIGINAL px, not the failed left one
          t1::model::new_piece_yx_state::<P>(orig_py, orig_px + 1, &mut self.s4.s3.s2.s1);
          fired = self.rotate_piece(cw);
      }
      if !fired {
          t1::model::new_piece_yx_state::<P>(orig_py, orig_px, &mut self.s4.s3.s2.s1); // restore
      }
      if t5::model::CHECK_INVARIANTS {
          t5::model::check_invariants(self);
      }
      fired
  }
  ```
  Both kick attempts are computed from `orig_px`, never chained — the right attempt is `orig_px
  + 1`, not "one more than wherever the failed left attempt left `px`." Mutating `px` in place
  before calling `rotate_piece` is sound specifically because `px` is a trivially-restorable
  scalar with no side effect beyond itself — unlike a T4-style `fix_piece`, where "undoing a
  draw" isn't a clean no-op. `self.rotate_piece(cw)` is `t5::model::Machine<P>`'s own inherent
  method — reachable directly, no trait import needed for that call (only
  `RotateKickPieceExt` itself needs importing at the call site, §6.1). `check_invariants` is
  `t5::model::check_invariants` — not redefined, since `T6.Correct = T5.Correct`.

---

## 5. Free functions emitted by `model.rs` (`T6.v` source order)

None. `T6.v` defines no free function of its own; `can_rotate_piece` is emitted in
`t1::model` (§0.2), not redefined here.

---

## 6. `t6::model::Params` and `t6::model::Machine<P>`

### 6.0 `Params` — no new trait

```rust
// spec: T6.v declares no Parameter of its own.
pub use t5::model::Params;
```

Unlike `t4::model::Params`/`t5::model::Params` (each of which declares its own — possibly
empty — trait extending its predecessor's, per skill §7.4), `t6::model` reuses
`t5::model::Params` directly with no wrapper trait at all. The stronger precedent here is
`t2::model`/`t3::model` (`rs_t2_src_model.rs`, `rs_t3_src_model.rs`): both introduce a new
wrapping `Machine<P: Params>` struct with zero new abstract parameters, and both bind `Params`
by importing `t1::model::Params` directly rather than declaring `pub trait Params:
t1::model::Params {}`. T6 has even less reason for a local trait than T2/T3 did — it doesn't
even introduce a new struct (§1) — so the leaner precedent applies with more force. A vacuous
`pub trait Params: t5::model::Params {}` here would be dead indirection: nothing would ever
implement it that doesn't already implement `t5::model::Params`, and nothing in `t6` reads a
`Params` item that isn't already reachable through `t5::model::Params`'s own supertrait chain.

### 6.1 `Machine<P>` — type alias, plus the extension trait

```rust
// spec: State (= T5.State)
pub type Machine<P> = t5::model::Machine<P>;

pub trait RotateKickPieceExt {
    fn rotate_kick_piece(&mut self, cw: bool) -> bool;
}

impl<P: Params> RotateKickPieceExt for Machine<P> {
    fn rotate_kick_piece(&mut self, cw: bool) -> bool { /* §4-T6b */ }
}
```

No `Machine::new` is defined at this layer: `T6.v` declares no new `Init` and there is no new
field to initialize (§0). `t5::model::Machine::<P>::new(...)` is `Machine::<P>::new(...)` here
too, by the alias — callers construct exactly as T5's own `main.rs` already does (§15). Every
T1–T5 method, getter, and public field is available on `Machine<P>` unchanged, with no `.s5.`
or similar indirection, because there is no such field.

### 6.2 Read-through access

No new getters. `main.rs`/`view.rs` read `machine.s4.…`/`machine.gy` exactly as `t5`'s own do
(§6.6, `t5/implementation.md`) — `Machine<P>` being an alias means every one of `t5::model`'s
public fields is already `machine.<field>`, not `machine.<something>.<field>`.

---

## 7. `t6::model`'s constants

None. `CHECK_AXIOMS`/`CHECK_INVARIANTS` are `t5::model::CHECK_AXIOMS`/
`t5::model::CHECK_INVARIANTS`, reached by their own path wherever needed (§4-T6b) — `t6::model`
does not redeclare or re-export them, the same restraint `t6::model::Params` (§6.0) exercises
for the parameter trait.

---

## 8. `proofs.md` (scope)

Delta over `t5/proofs.md`.

1. **Scope.** Safety only. `RotateKick`'s exclusion from the refinement is structural, per
   `T6.v` itself (§1).
2. **α₆.** `α₆ = α₅`, applied to the same value — no new field, no new struct, hence no new
   projection to state (§1). Every `Machine<P>` method other than `rotate_kick_piece` needs no
   per-method transfer argument: they are `t5::model::Machine<P>`'s own methods, identical by
   the type alias, not delegating calls that would need one.
3. **`rotate_kick_piece` — no-use, full fresh argument.** Guard/exclusivity via
   `can_rotate_piece` (cite `t1/proofs.md`'s `L-can-rotate-piece`, §0.2, as an imported fact:
   `can_rotate_piece(cw, s)` iff `rotate_piece(cw)` would fire on a non-`gameover` `s`). Kick
   attempts are both computed from `orig_px`, not chained. Mutate-then-restore is sound because
   `px` has no accumulated side effect to undo — contrast `t4/proofs.md`'s `fix_piece`, where
   it wasn't. `gy`-refresh (inherited from T5's own state, since `T6.State = T5.State` carries
   `gy` too) comes from the reused `self.rotate_piece(cw)` call, not re-derived.
4. **Cap soundness — not applicable.** `rotate_kick_piece` introduces no new arithmetic beyond
   `px ± 1` around a bounded restore, and touches no capped accumulator.
5. **`Init` and every other action.** `T5.v`'s own, unchanged; there is no `t6::model::Machine`
   constructor to argue about, by the type alias (§6.1).

---

## 9. Tests (`tests/`)

Mirror T5's suite on the same fixture, plus:

- **`test_instance.rs`** — the same content as `rs_t5_tests_test_instance.rs`: its own
  `include!(concat!(env!("CARGO_MANIFEST_DIR"), "/../t1/tests/test_instance.rs"));`, the
  re-declared `TestInstanceWide` `t1::model::Params` impl, and the `t4::model::Params`
  (`NEXT_LEN`) impls — `t5/tests/test_instance.rs`'s own header explains why each `tests/`
  directory recompiles its own fixture rather than sharing compiled code across crates. No new
  impl block is added for `t6`: since `t6::model` defines no `Params` trait of its own (§6.0),
  a fixture satisfying `t5::model::Params` already satisfies everything `t6` needs.
- **`oracle.rs`** — standalone, from scratch, covering only what's genuinely new:
  `rotate_kick_piece`. Does **not** `include!` or otherwise reuse `t5`'s oracle — the same
  independence discipline every prior layer's oracle already follows (e.g. `t3/tests/
  oracle.rs`'s header: a bug shared between the translation and a helper it reuses should still
  surface as a mismatch here). Reimplements the rotation-validity check directly against the
  raw grids (no call to `t1::model::valid`/`can_rotate_piece`) and the two-kick-attempt
  sequence independently. `s4`'s own correctness is not re-verified here — that risk belongs to
  `t1`–`t5`'s own test suites (skill §7's reuse principle, applied to testing scope, the same
  way every prior layer's own oracle header already applies it one layer down).
- **`model_unit_test.rs`** — golden vectors on `TestInstance`:
  - `rotate_kick_piece` does not fire when plain rotation would (exclusivity), leaving the
    state byte-identical to before the call.
  - `rotate_kick_piece` fires via a left kick when available.
  - `rotate_kick_piece` fires via a right kick, relative to the *original* column, when only
    that one is available — construct a board where a naive "kick from wherever the left
    attempt left off" would wrongly succeed or fail, to distinguish this from the chained
    alternative.
  - a successful kick moves `px` by exactly `±1` from where it started, never more; `py`/`pr`
    at a successful kick match what a plain `rotate_piece` at the kicked column would have
    produced.
  - both kicks failing leaves `px` restored to its original value and the rest of the state
    untouched.
  - `Machine<P>` is `t5::model::Machine<P>`: every inherited T5 method (`move_piece`,
    `fix_piece`, `hold_piece`, `drop_piece`, `fall_step`) is directly callable on the same
    value `rotate_kick_piece` was called on, with no wrapping field to route through.
- **`model_properties_test.rs`** — `proptest`, on `TestInstanceWide`: `rotate_piece` and
  `rotate_kick_piece` are mutually exclusive for every generated input (never both fire from
  the same pre-state/`cw`); differential oracle over every snapshot field, across all seven
  event kinds (T5's six plus `RotateKick`).
- **`model_fuzz_test.rs`** — long random traces including `rotate_kick_piece`, `gy` invariant
  (inherited from `t5::model::check_invariants`) checked every step, differential oracle,
  adversarial `check_axioms` (delegated to `t5::model::check_axioms`, no new axioms to fuzz).

---

## 10. Acceptance oracle

A regeneration is correct iff:
1. Every `T6.v` definition with a §3 mapping is realised; every "not emitted" entry is absent.
2. `t6::model::Machine<P>` is a type alias for `t5::model::Machine<P>`, not a wrapping struct
   with a new field.
3. `rotate_kick_piece` never fires when `can_rotate_piece` holds (exclusivity), and never
   mutates anything when it doesn't fire.
4. A successful kick's `px` differs from the original by exactly `±1`, never more, and the
   right attempt is computed relative to the original position, not the failed left one.
5. `rotate_kick_piece` reuses `self.rotate_piece(cw)` for the actual mutation — it does not
   reimplement rotation validity, mutation, or `gy`-refresh itself.
6. The `t1::model::can_rotate_piece` patch (§0.2) is present and additive-only; no existing
   `t1::model` item changes signature or behavior.
7. `t6::model` defines no `Params` trait and no `Machine::new` — both reached exclusively
   through the `t5::model` alias.

---

## 11. Instantiation (`instance.rs`)

```rust
pub use t5::instance::*;
```

Pure re-export. `T6.v` declares no `Parameter` of its own, and `t6::model` defines no `Params`
trait of its own (§6.0) — there is no `impl` for `instance.rs` to add, unlike every prior
layer's `instance.rs` (`t2`–`t5`), which each add at least an empty `impl <crate>::model::Params
for Tetris {}`.

---

## 12. Generator determinism rules

Inherit `t1`–`t5/implementation.md` §12's "reuse over restatement" verbatim. The §0.2 patch to
`t1::model` is a prerequisite of T6 codegen, not part of T6's own output.

---

## 13. `instance.rs` parameters

None beyond `t5`'s. See §11.

---

## 14. `view.rs`

```rust
pub use t5::view::*;
```

Pure re-export — `T6.v` adds no new state to render, and `rotate_kick_piece`'s effect on the
piece (`px`, `pr`) is already drawn by `t5::view::render`'s existing `draw_piece`/`draw_ghost`
calls, which read `machine.s4.s3.s2.s1.{px,pr}`/`machine.gy` generically, not through any
rotation-specific code path. `t5::view::render::<P>` type-checks directly against
`t6::model::Machine<P>` — no wrapper, no re-export shim beyond the `pub use` itself.

---

## 15. `main.rs` — entry point

Extends `t5/implementation.md` §15's shape.

### 15.1 `misc.rs` — `Action` reused verbatim

```rust
pub use t5::misc::*;
```

`req-piece-kick` extends what rotation *does*; it is not a separate action the player triggers
differently — no new `Action` variant, no new keybinding. Bound to the same `Cw`/`Ccw` keys and
gamepad buttons as T1–T5.

### 15.2 `fire` — `Cw`/`Ccw` try a kick on plain-rotation failure

```rust
fn rotate<P: Params>(machine: &mut Machine<P>, cw: bool) -> bool {
    machine.rotate_piece(cw) || machine.rotate_kick_piece(cw)
}

fn fire<P: Params>(action: Action, machine: &mut Machine<P>) {
    match action {
        Action::Left => { machine.move_piece(0, -1); }
        Action::Right => { machine.move_piece(0, 1); }
        Action::Down => { machine.fall_step(&shuffle_bag::<P>()); }
        Action::Cw => { rotate(machine, true); }
        Action::Ccw => { rotate(machine, false); }
        Action::Hold => { machine.hold_piece(&shuffle_bag::<P>()); }
        Action::Drop => { machine.drop_piece(&shuffle_bag::<P>()); }
    }
}
```

`rotate_kick_piece` is only reachable here because `use t6::model::RotateKickPieceExt;` is in
scope — an extension trait's methods are invisible without importing the trait itself, unlike
`t5::model::Machine`'s inherent methods (`rotate_piece`, `move_piece`, …), which need no such
import. This two-call sequencing is a `main.rs`-level orchestration decision, not a `T6.v`
definition (§1's rejected alternative): the model defines two mutually exclusive events;
nothing in `T6.v` says a caller must try both, in this order, on every rotate input. That
decision belongs here for the same reason DAS timing does — a concern the abstract model
doesn't speak to at all.

### 15.3 Everything else

Unchanged from T5's (`t5/implementation.md` §15) — `shuffle_bag`, `make_bags_fn`, `RunState`,
`after_action`, `fall_period`, `process_input`'s DAS/ARR engine, restart-on-gameover, and font
loading, all generic over `t6::model::Machine<P>` instead of `t5::model::Machine<P>` (the same
type, by the alias), reading `machine.s4.s3.s2.…` at the identical nesting depth T5's own
`main.rs` already uses — T6 adds no wrapping layer, so no field path gets one hop deeper.
