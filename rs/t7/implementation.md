# implementation.md — ImplementationInstructions for T7 (Rust)

Per-model instructions for the transformation

```
FormalModel (T7.v)  ×  ImplementationInstructions (this file)
      ── rocq-to-rust skill ──▶  Code (model.rs, view.rs, main.rs, net.rs, instance.rs, misc.rs)
                                  ×  Proofs (proofs.md)  ×  Tests (tests/)
```

This file is the **T7-Rust-specific source of truth**, applying the `rocq-to-rust` skill's
general rules — in particular §7, "translating a module that wraps another" — to `T7.v`.
`t6/implementation.md` (and transitively `t5`/`t4`/`t3`/`t2`/`t1/implementation.md`) are the
frozen sources of truth for everything T7 reuses unchanged; this file states only what is
specific to T7. Generated artifacts are never hand-edited: to change one, change this file or
`T7.v` and regenerate. All references to `T7.v`/`T6.v`/…/`T1.v` are **by definition name**.

## 0. Inputs, outputs, and what is frozen

Codegen-time inputs:
- `T7.v` — the abstract model (refines `T6.v`, per-player, excluding a materializing `Fix`/
  `Drop` and every network-only event — see §1).
- `T6.v`/`t6/implementation.md` (and transitively `T5.v`/…/`T1.v`) — reused in full.
- this file.
- the `rocq-to-rust` skill (cited as `skill §N`).

Runtime input (NOT codegen-time, NOT derived from `T7.v`): `t7/src/instance.rs` — a **new**
marker type (not a further `impl` on `t1::instance::Tetris`, §11) implementing
`t1::model::Params` with `CellExtra = Garbage`, an inhabited type `t1::instance::Tetris` itself
never needs (its own `CellExtra` stays `Infallible`).

Outputs: `t7/src/model.rs`, `t7/src/view.rs`, `t7/src/main.rs`, `t7/src/app.rs`, `t7/src/text.rs`,
`t7/src/net.rs`, `t7/src/session.rs`, `t7/src/instance.rs`, `t7/src/misc.rs`, `t7/Cargo.toml`,
`t7/proofs.md`, `t7/tests/` (§9).
A generation is **correct** iff `model.rs` refines `T7.v`, per-player (established by
`proofs.md` — see §8); the acceptance oracle (§10) is the operational check that provides
evidence for this, it is not itself the definition.

### 0.1 Files reused from `t1`–`t6` unchanged (not regenerated, imported as path dependencies)

| item | role in T7 |
|------|-----------|
| `t6::model::Params` | reused directly as `t7::model::Params`'s supertrait (§6.0) — `T7.v`'s `Player`/`Host`/`PlayerEqb`/`PlayerNext`/`PlayerCount` are **not** `Params` items at all (§0.2) |
| `t6::model::Machine<P>` | the wrapped per-player engine, reached as `self.s6` (a new field — T7 introduces real new state, unlike `t6`'s own alias) |
| `t6::model::{check_axioms, check_invariants}` | called directly for the `s6` portion, not re-implemented |
| `t1::model::{intersect, new_piece_yx_state, PieceOrExtra, Cell}` | `intersect` re-checks the forbidden zone after materialization; `new_piece_yx_state` relocates the piece for `drop_piece`; `PieceOrExtra`/`Cell` are `mg`'s own cell type and occupancy trait |
| `t5::model::Machine::update_shadow_y` | recomputes the shadow after materialization splices rows into `mg` directly, outside any `t6::model` action (§4-T7c); `pub` (`t5/implementation.md` §6.9) |
| `t6::view::render` | called once, on `machine.s6`, for this player's own board — never for an opponent's (§14.3's mini-grid strip is genuinely new drawing code, not a scaled-down `render` call) |
| `t1::view::Colored` | `Garbage` implements it (§11); `Piece` already does (`rs_t1_src_instance.rs`, unaffected — T7 reuses the exact same `Piece` type and its existing `Colored` impl, §11) |
| `t1::misc::{DAS_DELAY, ARR, window_conf, LogicalKeys, RepeatTimer, random_piece}` | UI-layer primitives — `DAS_DELAY`/`ARR`/`RepeatTimer` reached from `app.rs`'s `process_input`, `window_conf`/`LogicalKeys` from `main.rs`'s own frame loop |
| `t6::misc::Action` | reused verbatim (§15.1) — T7 adds no new *player-facing* action; network events are not player input |

`t7/src/model.rs` therefore contains: the garbage-materialization logic (genuinely new), the
multiplayer bookkeeping (`target`/`gameover_view`/`connected_view`/`winner_multi`/
`next_target`), and three `receive_*` methods. It reimplements no T1–T6 game logic — movement,
rotation, line-clearing, scoring, hold, preview, shadow, and wall-kick are all reached through
`self.s6`.

### 0.2 The structural departure: `Player`/`PlayerCount`/`Host` are not `Params` items

Every prior layer's new `Parameter` became a new `Params` trait item — `t4`'s `NextLen`, and
`t1::model::Params`'s own `CellExtra` (§0.1: `PieceOrExtra`'s companion item, already part of
`t1::model::Params` — every `Params` implementor across `t1`–`t7` supplies one). `T7.v`'s own
new parameters — `Player`, `Host`, `PlayerEqb`, `PlayerNext`, `PlayerCount` — do **not** get the
same treatment, for a categorical reason, not a convenience: every existing `Params` item is
fixed once per
*compiled instantiation* (a `Piece` enum, a board size, `NEXT_LEN` — all Rust `const`/
associated-type facts, resolved at compile time). A match's roster is fixed once per *lobby
session* — the same compiled binary runs a 2-player match one evening and a 4-player match the
next, with `Host` being whichever peer happened to create the lobby. `PlayerCount` cannot be a
Rust `const` without freezing it at compile time, which would be simply false. `Player` values
are realized as plain `usize` roster indices (comparison is `==`, no `PlayerEqb` needed — a
type-level fact for a `Copy + Eq` primitive, not a runtime axiom, the same discharge-by-type
argument `skill §4h` already applies to enum exhaustiveness); `PlayerNext` is
`(i + 1) % player_count`; `Host` is `Player[0]` by the roster-assignment convention (§15.1) —
none of these need naming as a `Params` item, they're plain runtime values threaded through
`Machine::new` and the lobby protocol instead (§6.1, §15).

---

## 1. The refinement, and what it buys

`T7.State` holds one `T6.State` per player (`s6 : Player → T6.State`) plus network-wide fields
(`connected`, `messages`) that are not local to any one player. The Rust image keeps only the
**local** half in `Machine<P>` — `self.s6` is *this* player's own `T6.Machine`, `garbage`/
`target`/`gameover_view`/`connected_view` are this player's own local view — and pushes
`connected`/`messages` entirely out of the model, into `net.rs` (§15), which is not part of any
player's formal local state either. There is therefore no single Rust value corresponding to
`T7.State` as a whole; the correspondence is per-player, and the full system correspondence
(needed for `proofs.md`) spans every player's `Machine` plus the network layer together — see §8.

Refinement mapping (`T7.v`'s own `fₑ`, partial: `Receive` has no `T6.v` counterpart; `fₛ pl :=
s6 s pl`): per skill §7.1's three-way classification, evaluated per player:

- **`move_piece`/`rotate_piece`/`hold_piece`/`rotate_kick_piece` — full uses.** Gated by
  `!winner_multi(...)`, then a one-line delegating call to `self.s6`'s own method — nothing
  else in the T7.v definition beyond the guard.
- **`fix_piece` — full use when no garbage remains to materialize; no-use (new logic) when
  it does.** The `T6.FixPiece` call itself is always a full use (§4-T7c calls `self.s6.fix_piece`
  first, unconditionally, before any T7-only logic runs); everything after it — the
  materialization shift, the overflow/gameover recheck, `target`/`gameover_view` updates — has
  no `T6.v` counterpart and is argued fresh.
- **`drop_piece` — no-use for the relocation (mirrors T5's own classification of that step),
  then inherits `fix_piece`'s own classification for everything after.**
- **`receive_garbage`/`receive_gameover`/`receive_disconnect`/`notice_disconnection` — no `T6.v`
  counterpart at all; each is a stutter with respect to `s6`** (none of the three ever touches
  `self.s6`), argued as a cross-machine/network-layer fact in `proofs.md`, not a single-`Machine`
  one (§8).
- **The network layer itself (`DisconnectPlayer`, host relay, hole-punching, retransmission) —
  realized by nobody's `Machine`, `net.rs`/host behavior instead.** No Rust `Machine` method
  corresponds to `DisconnectPlayer`; its effect (on `connected`/`messages`, neither in
  `Machine`) is realized entirely outside the model (§4-T7f).

---

## 2. File layout & module shape

```
t7/
  Cargo.toml             # depends on t1–t6 by path (workspace member); serde, serde_json,
                          #   flate2 (§15.3) — the only new dependencies
  src/
    lib.rs                # pub mod app; instance; misc; model; net; session; text; view (§0.4)
    misc.rs                 # pub use t6::misc::*; — no new player-facing action (§15.1)
    instance.rs               # NEW marker type + Garbage + Colored impl (§11)
    model.rs                    # T7 engine: Machine<P> wraps t6::model::Machine<P> (§5–§7)
    view.rs                       # per-player render + garbage gauge + opponent minis (§14)
    net.rs                          # pub — transport mechanism: STUN, wire codec, packet
                                     #   framing, reliable/best-effort delivery (§15.2–§15.3)
    session.rs                      # pub — lobby/relay state machine: Session, Peer,
                                     #   Endpoint, and the Machine<Instance>-facing glue
                                     #   (fire, rotate, find_winner, …) built on net.rs (§15)
    text.rs                           # pub — text-entry fields + the out-of-band clipboard
                                       #   exchange the lobby screens use (§15.1a)
    app.rs                              # pub — screen/menu/lobby state machine: the fall-speed
                                         #   schedule, single-player dispatch (also the S6/S8
                                         #   filler), the DAS/ARR input engine, and each lobby
                                         #   screen's own step/draw functions, built on
                                         #   session.rs/text.rs (§15.0–§15.1b)
    main.rs                              # the App enum, its Single arm, and the frame loop
                                          #   driving app.rs's step functions — a thin reference
                                          #   caller (§0.4); macroquad-specific, not part of the
                                          #   library
  proofs.md               # refinement proof, delta over t6/proofs.md (§8) — does not exist yet;
                           #   §8 states what it must cover
  tests/
    test_instance.rs      # NEW fixture: own Piece/grid data + Garbage (§9) — cannot `include!`
                           #   t1's fixture verbatim the way every prior layer's own does,
                           #   since it needs `CellExtra = Garbage`, not `Infallible` (§9)
    model_unit_test.rs
    model_properties_test.rs
    model_fuzz_test.rs      # multi-`Machine` harness, each one's outputs wired directly into
                             #   others' `receive_*` calls — no sockets (§9)
    oracle.rs                 # executable T7.v reference for garbage/target/view logic only
                               #   (reuses t6's own oracle for s6, §9)
    net_unit_test.rs            # net.rs's transport mechanism: STUN, wire codec, packet
                                 #   framing, the pure delivery state machines, a real
                                 #   loopback-socket exercise of NetWorkerHandle/Connection
    session_integration_test.rs   # session.rs's lobby/relay state machine: a full host +
                                   #   joiners over real loopback UDP, no display server
```

The workspace root's `Cargo.toml` gains `"t7"` in `members`; `t1`–`t6` remain independently
buildable, unmodified in behavior by T7's existence.

### 0.4 `net.rs`/`session.rs`/`app.rs`/`text.rs` as public library modules

Every prior layer keeps `model.rs` pure and deterministic and confines I/O-adjacent concerns
(keyboard/gamepad polling, timing, restart) to `main.rs`, which is a binary target — `model.rs`
never imports `net.rs`/`session.rs` and stays fully testable (§9) without a socket ever opening.
`Machine<P>`'s public API is exclusively synchronous method calls (`receive_garbage(amount)`,
`receive_gameover(from)`, …); deciding *when* to call them and *what* to send after
`fix_piece`/`fall_step`/`drop_piece` return is `net.rs`/`session.rs`'s job, not `model.rs`'s.

Unlike `main.rs` — a binary target no other crate can link against — `net.rs`, `session.rs`,
`app.rs`, and `text.rs` are all `pub mod`-declared in `lib.rs`. `net.rs` (the transport
mechanism: STUN, wire codec, packet framing, reliable/best-effort delivery) and `session.rs`
(the lobby/relay state machine built on it: `Session`, `Peer`, `Endpoint`, and the
`Machine<Instance>`-facing glue such as `fire`/`rotate`/`find_winner`) let another binary in
this workspace drive a full networked match — lobby, host relay, garbage/gameover/disconnect
delivery — without reimplementing that protocol: it depends on `t7::session::Session` and
`t7::net` the same way it depends on `t7::model::Machine`. `app.rs` (the screen/menu/lobby state
machine: the fall-speed schedule, single-player dispatch, the DAS/ARR input engine, and each
lobby screen's own step/draw functions) and `text.rs` (text-entry fields and the out-of-band
clipboard exchange) go one layer further: a caller reuses the entire UI on top of `session.rs`,
not just the networking underneath it, supplying only its own `App` enum to tie the step
functions together into a frame loop, plus whatever caller-specific screen it wants to add (this
crate's own `main.rs` adds exactly one, `Single`, served directly by `t6::model::Machine`).

`Session` itself still never calls a macroquad API (its own module doc comment) — that is what
lets `tests/session_integration_test.rs` drive a full host and two joiners over real loopback UDP
with no display server present, and lets `app.rs`'s own tests exercise a lobby's own step
functions (e.g. `HostLobby::try_add`) the same way. This crate's own `main.rs` is exactly the
thin reference caller `app.rs`/`text.rs` are built to be layered under: the `App` enum, its
`Single` variant, and the frame loop that drives `t7::app`'s step functions — nothing else.

---

## 3. Naming map (`T7.v` → Rust)

Only T7-introduced names appear here; T1–T6 names keep their own maps, reached through
`self.s6`'s existing field chain.

| `T7.v` | Rust |
|--------|------|
| `Player` (Parameter) | `usize` roster index (§0.2) |
| `Host` | index `0` in the frozen roster, by convention (§15.1) |
| `PlayerEqb` | `usize`'s own `==` (§0.2) |
| `PlayerNext` | `(i + 1) % player_count`, a plain expression, not a named function |
| `PlayerCount` | `self.gameover_view.len()` (or `self.connected_view.len()`, kept equal by construction) — not stored as its own field |
| `Message` (inductive) | `net::WireMessage` enum (§15.3) — not in `model.rs`; `model.rs` never constructs or reads a wire message |
| `State` (record) | `t7::model::Machine<P>`; fields below |
| `s6` | `pub s6: t6::model::Machine<P>` |
| `garbage` | `pub garbage: i64` |
| `target` | `pub target: usize` |
| `gameoverView`, `connectedView` | `pub gameover_view: Vec<bool>`, `pub connected_view: Vec<bool>` — **own view only**, no observer index (a `Machine` only ever holds its own view, §6.1) |
| `connected`, `messages` | **not fields** — realized entirely in `net.rs`/the host's own bookkeeping (§0.4, §15.4) |
| `mg` (helper) | `self.s6.mg()`/`self.s6.mg_mut()` — reached through `T6MachineExt` (below), not the raw field chain |
| `gameover` (helper) | `self.s6.gameover()`/`self.s6.gameover_mut()` — same |
| `clearedLines` (helper) | `self.s6.cleared_lines()` — same |
| `UpdatePlayer`, `UnchangedT7Part` | not emitted — each method mutates `self` directly, field by field |
| `PlayingView` | `playing_view(gameover_view: &[bool], connected_view: &[bool], pl2: usize) -> bool` — free function, no observer parameter (§0.2's reasoning: a `Machine` only ever evaluates its own view) |
| `WinnerMulti` | `winner_multi(gameover_view: &[bool], connected_view: &[bool], my_index: usize) -> bool` |
| `NextTargetAux`/`NextTarget` | `next_target(playing: impl Fn(usize) -> bool, self_: usize, pl: usize, player_count: usize) -> usize` — fuel-bounded loop, `player_count` fuel, the same "`Fixpoint` on a strictly-decreasing measure → loop with an explicit fuel count" idiom `shadow_y` already uses (`t5/implementation.md` §4-T5a) |
| `Init` | `Machine::new(my_index, player_count, bags_fn, piece_source)` |
| `GeneratedGarbage` | `generated_garbage(cleared_lines: i64, perfect_clear: bool) -> i64` |
| `GenRemGarbage` | `gen_rem_garbage(garbage: i64, cleared_lines: i64, perfect_clear: bool) -> (i64, i64)` — `(genGarbage, remGarbage)` |
| `GarbageGrid` | not emitted as a distinct grid value — folded directly into `fix_piece`'s materialization (§4-T7c), same fusion `t1::model::fix_piece` already applies to `GridUnion`/`ClearFullLines` (skill §3.2) |
| `NewMainGridGameoverState` | not emitted — folded into `fix_piece`, sets `self.s6.s4.s3.s2.s1.mg`/`.gameover` directly |
| `ValidHoles` | checked per call, at each `holes(y)` invocation — an `assert!`, uncaught, mirroring `t4::model::assert_piece_set`'s role for `bag_new` |
| `SendMessages` | not emitted — `fix_piece` leaves `self.rem_gen_garbage` and `self.gameover_view[self.my_index]` for the caller to read after the call and act on (§4-T7d); wire-message construction is `net.rs`'s job (§15.3) |
| `FixPiece` | `Machine::fix_piece(&mut self, bag_new: &[P::Piece], holes: impl Fn(i64) -> i64) -> bool` |
| `ReceiveMessage` | split into three methods, no shared dispatch (§4-T7e): `receive_garbage(amount)`, `receive_gameover(from)`, `receive_disconnect(from)` |
| `DisconnectPlayer` | no `Machine` method (§4-T7f) — realized by the host's own `net.rs` logic |
| `NoticeDisconnection` | `Machine::notice_disconnection(&mut self) -> bool` |
| `FallStep` | `Machine::fall_step(&mut self, bag_new: &[P::Piece], holes: impl Fn(i64) -> i64) -> bool` |
| `HoldPiece` | `Machine::hold_piece(&mut self, bag_new: &[P::Piece]) -> bool` |
| `RotateKickPiece` | `Machine::rotate_kick_piece(&mut self, cw: bool) -> bool` |
| `DropPiece` | `Machine::drop_piece(&mut self, bag_new: &[P::Piece], holes: impl Fn(i64) -> i64) -> bool` |
| `Event`, `Next` | implicit (network dispatch in `session.rs` + input dispatch in `session::fire`/`app.rs`, each calling the matching method directly) |
| `NoWinner`, `Playing`, `SelfViewAccurate`, `ViewSound`, `MessageSound`, `NoSelfMessage`, `LastMessagesGameoverDisconnect`, `TargetNotSelf`, `TargetPlaying`, `Gameover`, `Correct`, `OtherS6Unchanged`, `GameoverMonotone`, `GameoverViewMonotone`, `DisconnectedMonotone`, `DisconnectedViewMonotone`, `CorrectStep` | `proofs.md` only |
| `fₑ`, `fₛ`, `T7RefinesT6`, `NoRemGarbage`, `NoMaterializedGarbage` | `proofs.md` only |

**`T6MachineExt`.** `t6::model::Machine<P>` is `t5::model::Machine<P>` itself, a type alias, not
a struct this crate wraps (`t6/implementation.md`'s own `T6.State = T5.State` note) — so `t7`
cannot reach `mg`/`gameover`/`cleared_lines`/etc. through a field chain rooted at `self.s6` the
way earlier layers reach their own wrapped state, and cannot add an inherent `impl` on a foreign
type either. `t6::model::T6MachineExt` (defined in `t6/src/model.rs`, alongside the same-shaped
`rotate_kick_piece` extension `t6/implementation.md` §4-T6b already documents) is the accessor
trait this reaches through instead: `mg`/`mg_mut`/`px`/`gameover`/`gameover_mut`/`cleared_lines`/
`perfect_clear`/`s1_mut`, used throughout `fix_piece`/`drop_piece`/`check_invariants` (§6.3,
§6.5, §6.10). Purely additive — no existing `t6` behavior changes — but it is worth being
explicit that `t6/implementation.md` itself documents only `rotate_kick_piece` among
`T6MachineExt`'s methods, not this fuller accessor set; that gap is in `t6/implementation.md`,
not this file, and is out of this file's own scope to close.

---

## 4. Per-definition translation rules (T7-specific)

- **§4-T7a. Materialization runs unconditionally after a successful `T6.FixPiece`, never
  gated on `player_count = 1`.** `T7.v`'s own `FixPiece` branches on `PlayerCount =? 1` to skip
  materialization entirely in the single-player case; that branch is dead code for this crate,
  since single-player mode is served directly by `t6::model::Machine` (§15) and never
  constructs a `t7::model::Machine` at all — `player_count > 1` is an asserted precondition of
  `Machine::new` (§0.2, §6.1), not a runtime branch inside `fix_piece`.

- **§4-T7b. `generated_garbage`/`gen_rem_garbage` — direct translation, natural subtraction as
  `.max(0)`.**
  ```rust
  // spec: GeneratedGarbage — req-multi-garbage-gen
  fn generated_garbage(cleared_lines: i64, perfect_clear: bool) -> i64 {
      let normal = if cleared_lines < 4 { cleared_lines - 1 } else { cleared_lines };
      let normal = normal.max(0); // natural subtraction: `c - 1` at `c = 0` must floor at 0
      let special = if perfect_clear { 10 } else { 0 };
      normal + special
  }

  // spec: GenRemGarbage — (genGarbage, remGarbage)
  fn gen_rem_garbage(garbage: i64, cleared_lines: i64, perfect_clear: bool) -> (i64, i64) {
      let gen_garbage = generated_garbage(cleared_lines, perfect_clear);
      let rem_garbage = (garbage - gen_garbage).max(0); // req-multi-garbage-cancel
      (gen_garbage, rem_garbage)
  }
  ```
  `remGarbage` (2nd component) is what **materializes onto this player's own board** — pending
  garbage left over after this clear's own generated garbage cancels as much of it as possible.
  `RemGenGarbage` (below) is the complementary quantity — generated garbage left over after
  cancelling pending garbage — sent **onward** to the target. At most one of the two is
  ever nonzero, by construction (both floor at 0 on opposite sides of the same subtraction).

- **§4-T7c. `fix_piece`'s materialization** (`mg` row `0` = bottom, matching every prior
  layer's own convention). Runs unconditionally once `self.s6.fix_piece(bag_new)` has fired —
  full T6 semantics: score, level, hold, `cleared_lines`, `perfect_clear`, and its own
  `mg`/`gameover` from the piece placement alone, already committed by the time this runs.
  ```rust
  let cleared_lines = self.s6.s4.s3.s2.s1.cleared_lines;
  let perfect_clear = self.s6.s4.s3.s2.perfect_clear;
  let (gen_garbage, rem_garbage) = gen_rem_garbage(self.garbage, cleared_lines, perfect_clear);
  self.rem_gen_garbage = (gen_garbage - self.garbage).max(0); // spec: FP.RemGenGarbage

  let hm = self.s6.s4.s3.s2.s1.mg.len() as i64;
  let wm = self.s6.s4.s3.s2.s1.mg[0].len() as i64;
  let eff_rem = rem_garbage.min(hm); // remGarbage is unbounded; clamp for array indices (D9/§4g)

  let mut gameover2 = self.s6.s4.s3.s2.s1.gameover;
  if !gameover2 && rem_garbage > 0 {
      gameover2 = if rem_garbage >= hm {
          true // pushes the entire board off — no scan needed
      } else {
          // must read the top rows BEFORE the shift below overwrites them
          (hm - rem_garbage..hm).any(|y| {
              (0..wm).any(|x| self.s6.s4.s3.s2.s1.mg[y as usize][x as usize].is_some())
          })
      };
  }

  // shift always runs, regardless of gameover2 — the stored grid always reflects
  // materialization, whatever caused gameover2. Decreasing index order (D9's guard-before-
  // index applies here too, in a different shape): a destination index (`i + eff_rem`) can
  // coincide with a later source index, so increasing order would read an already-overwritten
  // row.
  if eff_rem > 0 {
      for i in (0..hm - eff_rem).rev() {
          self.s6.s4.s3.s2.s1.mg[(i + eff_rem) as usize] = self.s6.s4.s3.s2.s1.mg[i as usize].clone();
      }
      for y in 0..eff_rem {
          self.s6.s4.s3.s2.s1.mg[y as usize] = garbage_row::<P>(holes(y), wm);
      }
      self.s6.update_shadow_y(); // §0.1 — the freshly-spawned piece's shadow is now stale
  }

  if !gameover2 {
      gameover2 = t1::model::intersect(
          P::forbidden_grid(), P::FY, P::FX, &self.s6.s4.s3.s2.s1.mg, 0, 0,
      );
  }
  self.s6.s4.s3.s2.s1.gameover = gameover2;
  ```
  Short-circuit: if `self.s6`'s own `gameover` is already `true` (set by the plain-fix path,
  before any garbage logic runs), neither the overflow scan nor the final `intersect` recheck
  runs — the shift/overwrite still runs unconditionally, only the boolean computation is
  skipped, matching the `if !gameover2` guards above.

- **§4-T7c′. `garbage_row` — the one function with no `T7.v` counterpart at the free-function
  level** (`GarbageGrid`'s per-row content, realized directly for the `Vec<Vec<_>>`
  representation instead of as a `Grid` record, skill §2):
  ```rust
  fn garbage_row<P: Params>(hole: i64, w: i64) -> Vec<Option<t1::model::PieceOrExtra<P>>> {
      assert!(0 <= hole && hole < w, "ValidHoles: hole {hole} outside [0, {w})"); // spec: ValidHoles
      (0..w)
          .map(|x| if x == hole { None } else { Some(t1::model::PieceOrExtra::Extra(Garbage)) })
          .collect()
  }
  ```

- **§4-T7d. `rem_gen_garbage` is a field**, set every `fix_piece` call, read by `net.rs`
  immediately after — the same pattern `t2::model::Machine::cleared_lines`/`combo` already
  establish for "state the caller reads post-call rather than a return value."

- **§4-T7e. `receive_garbage`/`receive_gameover`/`receive_disconnect` — three methods, no
  shared dispatch.** `net.rs` already knows a wire message's tag (§15.3), so there is no `enum`
  to match on model-side. `receive_garbage` takes no `from` (sender-agnostic `+=`);
  `receive_gameover`/`receive_disconnect` take `from` (update that sender's view slot, redirect
  `target` if it pointed at `from`). Neither of the three checks `connected` internally —
  `connected` has no Rust counterpart (§0.1); the gate is enforced by `net.rs` simply not
  calling them when the local link is down, not by an internal check:
  ```rust
  pub fn receive_garbage(&mut self, amount: i64) {
      self.garbage += amount; // spec: garbage[pl] += n
  }

  pub fn receive_gameover(&mut self, from: usize) {
      if self.target == from {
          self.target = self.redirect_target_from(from); // §4-T7e′
      }
      self.gameover_view[from] = true;
  }

  pub fn receive_disconnect(&mut self, from: usize) {
      if self.target == from {
          self.target = self.redirect_target_from(from);
      }
      self.connected_view[from] = false;
  }
  ```

- **§4-T7e′. `redirect_target_from` — private helper, shared by both `receive_*` methods and
  by `fix_piece`'s own target update.** `T7.v`'s `view'`/`PlayingView'` closures both special-
  case `from`/`pl` as *not playing*, even though their own view-array slot hasn't been written
  yet at the point `NextTarget` runs — Rocq computes `target`/the view field as simultaneous
  updates from the same pre-state; Rust's sequential field writes need the closure to carry the
  same override explicitly, or an update-ordering argument (skill §4b) that doesn't actually
  hold here (the closure reads `self.gameover_view`/`self.connected_view` while
  `next_target`'s search runs, and `self` is only mutated *after* that call returns, so no
  ordering hazard exists either way — the explicit override is what keeps the *semantics*
  correct, not what keeps the *borrow* correct):
  ```rust
  fn redirect_target_from(&self, from: usize) -> usize {
      let (gameover_view, connected_view) = (&self.gameover_view, &self.connected_view);
      next_target(
          |pl2| if pl2 == from { false } else { playing_view(gameover_view, connected_view, pl2) },
          self.my_index,
          from,
          gameover_view.len(),
      )
  }
  ```

- **§4-T7f. `DisconnectPlayer` has no `Machine` method.** Its effect touches only
  `connected`/`messages` — neither is `Machine` state. Realized entirely by `net.rs` (§15.4):
  the host, on detecting its own link to `pl` has failed, marks that locally and relays a
  `Disconnect` wire message to every other connected peer. `pl = Host` disconnecting is realized
  by nobody's code at all — the host process ceasing to exist *is* the effect; every other
  peer's own link-to-host timeout is what surfaces it, via `notice_disconnection` (below).

- **§4-T7g. `notice_disconnection`** — called by `net.rs` on locally detecting the link to the
  host has failed (a reliable-channel timeout, §15.2), regardless of cause. Flips
  `self.connected_view[self.my_index]` only, idempotently (the `connected s pl` half of `T7.v`'s
  own guard is the caller's responsibility — §0.1 — only the "have I not already noticed" half
  is checkable inside `Machine`):
  ```rust
  pub fn notice_disconnection(&mut self) -> bool {
      if !self.connected_view[self.my_index] {
          return false; // already noticed — idempotent
      }
      self.connected_view[self.my_index] = false;
      true
  }
  ```

- **§4-T7h. `drop_piece` — an explicit `winner_multi` guard `T7.v` doesn't show at this level,
  required by Rust's in-place mutation.** `T7.v`'s own `DropPiece` has no guard of its own —
  `NewPieceYXState` produces a *fresh, discardable* Rocq state value, so a `WinnerMulti` player's
  relocation, followed by `FixPiece`'s own internal guard rejecting the fix, simply returns
  `None` overall, with nothing ever observably mutated (Rocq state is immutable). Rust's
  `new_piece_yx_state` mutates `self.s6.s4.s3.s2.s1.py`/`.px` in place — without an explicit
  guard *before* that mutation, a `WinnerMulti` player's relocation would commit and never be
  undone, even though the `fix_piece` call that follows correctly rejects. This is the same
  category of pitfall skill §4b warns about (sequential mutation where Rocq has a single
  simultaneous/immutable step), just surfacing one call deeper than usual:
  ```rust
  pub fn drop_piece(&mut self, bag_new: &[P::Piece], holes: impl Fn(i64) -> i64) -> bool {
      if winner_multi(&self.gameover_view, &self.connected_view, self.my_index) {
          return false; // req-flow — guards the relocation below, not just the trailing fix
      }
      let gy = self.s6.gy;
      let px = self.s6.s4.s3.s2.s1.px;
      t1::model::new_piece_yx_state::<P>(gy, px, &mut self.s6.s4.s3.s2.s1); // spec: NewPieceYXState
      self.fix_piece(bag_new, holes) // req-piece-drop; re-checks winner_multi, harmlessly redundant
  }
  ```

---

## 5. Free functions emitted by `model.rs` (`T7.v` source order)

`playing_view`, `winner_multi`, `next_target`, `generated_garbage`, `gen_rem_garbage`,
`garbage_row` (§4). None are generic over `Params` beyond what they actually touch (skill §1):
`playing_view`/`winner_multi`/`next_target` take plain `&[bool]`/closures, no `P` at all;
`generated_garbage`/`gen_rem_garbage` take plain `i64`/`bool`; only `garbage_row` needs `P`, to
name `P::CellExtra`'s `Garbage` value in `PieceOrExtra::Extra`.

---

## 6. `t7::model::Params` and `t7::model::Machine<P>`

### 6.0 `Params` trait

```rust
// spec: T7.v's new Parameters (Player, Host, PlayerEqb, PlayerNext, PlayerCount) are runtime
// roster facts, not Params items (§0.2) — this trait adds nothing.
pub trait Params: t6::model::Params {}
```

Empty, following `t5/t4`'s precedent (an explicit, per-type "opts into T7" marker) rather than
`t2/t3`'s "import the supertrait directly" — T7 introduces a genuinely new wrapping struct
(unlike `t6`, which had nothing to wrap at all and skipped the trait entirely,
`t6/implementation.md` §6.0), so the marker earns its keep the same way it does at `t4`/`t5`.

### 6.1 `Machine<P>` and constructor — `Init bags H` (`T7.v`)

```rust
pub struct Machine<P: Params> {
    pub s6: t6::model::Machine<P>,
    pub my_index: usize,
    pub garbage: i64,
    pub target: usize,
    pub gameover_view: Vec<bool>,   // own view only — len = player_count
    pub connected_view: Vec<bool>,  // own view only
    pub rem_gen_garbage: i64,       // spec: FP.RemGenGarbage — read by the caller after fix_piece
}

impl<P: Params> Machine<P> {
    /// spec: Init. `player_count > 1` and `my_index < player_count` are asserted here, once,
    /// at the point the roster is frozen — the closest Rust analogue to `PlayerCountPositive`
    /// (§0.2: not a `check_axioms::<P>()` conjunct, since neither value is a `Params` item).
    pub fn new(
        my_index: usize,
        player_count: usize,
        bags_fn: impl FnMut(u64) -> Vec<P::Piece>,
        piece_source: impl FnMut() -> P::Piece,
    ) -> Self {
        assert!(player_count > 1, "T7::Machine is for multiplayer only — single-player uses t6::model::Machine directly");
        assert!(my_index < player_count);
        let s6 = t6::model::Machine::new(bags_fn, piece_source); // spec: s6Init pl := T6.Init (bags pl) (H pl)
        let mut gameover_view = vec![false; player_count];
        gameover_view[my_index] = s6.s4.s3.s2.s1.gameover; // spec: Init's gameoverView (obsd=obs case)
        let m = Machine {
            target: (my_index + 1) % player_count, // spec: target := PlayerNext
            gameover_view,
            connected_view: vec![true; player_count], // spec: connectedView := PlayerCount>1 (asserted true)
            garbage: 0,
            rem_gen_garbage: 0,
            my_index,
            s6,
        };
        if CHECK_INVARIANTS { check_invariants(&m); }
        m
    }
}
```

### 6.2 `move_piece`/`rotate_piece`/`hold_piece`/`rotate_kick_piece`

Full uses (§1), identical shape:
```rust
pub fn move_piece(&mut self, dy: i64, dx: i64) -> bool {
    if winner_multi(&self.gameover_view, &self.connected_view, self.my_index) {
        return false;
    }
    let fired = self.s6.move_piece(dy, dx);
    if CHECK_INVARIANTS { check_invariants(self); }
    fired
}
```
(`rotate_piece(cw)`, `hold_piece(bag_new)`, `rotate_kick_piece(cw)` — same shape, delegating to
`self.s6`'s matching method; `rotate_kick_piece` needs `use t6::model::RotateKickPieceExt;` in
scope, the same import `t6/implementation.md` §15.2 already requires of its own callers.)

### 6.3 `fix_piece` — §4-T7c/§4-T7d

```rust
pub fn fix_piece(&mut self, bag_new: &[P::Piece], holes: impl Fn(i64) -> i64) -> bool {
    if winner_multi(&self.gameover_view, &self.connected_view, self.my_index) {
        return false;
    }
    if !self.s6.fix_piece(bag_new) {
        return false; // T6's own guard failed — matches option_map's None case, zero mutation below
    }
    // materialization always proceeds from here — no further guard. Full body: §4-T7c.
    let gameover2 = /* §4-T7c's shift/overwrite/recheck, ending with self.s6...gameover = gameover2 */;
    self.gameover_view[self.my_index] = gameover2;
    if self.rem_gen_garbage > 0 && !gameover2 {
        // §4-T7e′'s from-exclusion isn't needed here — next_target's own
        // `pl2 != self` check already rejects `self.my_index` as a candidate
        // regardless of what `playing_view` says about it, so the plain
        // closure (no override) is equivalent to FP.PlayingView' at this call site.
        self.target = next_target(
            |pl2| playing_view(&self.gameover_view, &self.connected_view, pl2),
            self.my_index, self.target, self.gameover_view.len(),
        );
    }
    self.garbage = 0; // req-multi-garbage-cancel: consumed by materialization; the target is credited on delivery, not here (receive_garbage)
    if CHECK_INVARIANTS { check_invariants(self); }
    true
}
```

### 6.4 `fall_step`

Same disjoint-guard sequencing every prior layer's own `fall_step` uses — no guard of its own,
both branches already run one:
```rust
pub fn fall_step(&mut self, bag_new: &[P::Piece], holes: impl Fn(i64) -> i64) -> bool {
    if self.move_piece(-1, 0) { return true; }
    self.fix_piece(bag_new, holes)
}
```

### 6.5 `drop_piece` — §4-T7h

### 6.6 `notice_disconnection` — §4-T7g

### 6.7 `receive_garbage`/`receive_gameover`/`receive_disconnect` — §4-T7e

### 6.8 Read-through access

No new getters beyond `t6::model::Machine`'s own public fields, reached as `self.s6.…` — same
convention every prior layer's naming map already follows (§3).

### 6.9 `check_axioms::<P>()`

```rust
/// spec: T7.v's own axiom (PlayerCountPositive) is not a Params-level fact (§0.2) — checked
/// instead as a runtime assertion in Machine::new. Pure delegation here.
pub fn check_axioms<P: Params>() {
    t6::model::check_axioms::<P>();
}
```

### 6.10 `check_invariants::<P>(s)`

```rust
/// Layered on t6::model::check_invariants; the purely-representational conjuncts (skill §6.5)
/// this layer adds have no Rocq counterpart beyond SelfViewAccurate (checked here, not left to
/// proofs.md alone — the naming map's §3 entry lists it among Rocq invariants realized only as
/// a proof obligation at lower layers; T7 is the one layer that actually stores a
/// gameover_view to check it against).
pub fn check_invariants<P: Params>(s: &Machine<P>) {
    t6::model::check_invariants(&s.s6);
    let n = s.gameover_view.len();
    assert!(s.garbage >= 0);
    assert!(s.target < n);
    assert_eq!(s.connected_view.len(), n);
    assert_eq!(s.gameover_view[s.my_index], s.s6.s4.s3.s2.s1.gameover, "SelfViewAccurate");
}
```

---

## 7. `t7::model`'s constants

```rust
pub const CHECK_AXIOMS: bool = true;
pub const CHECK_INVARIANTS: bool = false;
```
Same module-level shape as every prior layer's own `model.rs`.

---

## 8. `proofs.md` — scope

`proofs.md` does not exist in this repository. What follows is what it must establish:

1. **Scope.** Safety only, as every prior `proofs.md`.
2. **αₚₗ, per player.** `s6 αₚₗ(σ) = α₆(σ.machines[pl].s6)`; `garbage`/`target`/
   `gameover_view`/`connected_view` map directly (primitive fields, no coercion). `connected`/
   `messages` are **not** read off any `Machine` field (§0.1) — defined directly against
   `net.rs`'s own connection/queue state, the same way a wrapping-module proof states a
   correspondence for state that genuinely lives outside the wrapped `Machine` (skill §7,
   adapted: here the "outside" state is the network layer, not another formal module).
3. **Move/Rotate/Fall/Hold/RotateKick, non-materializing Fix — full-use transfer**, per player,
   exactly as every prior layer's own argument (§1).
4. **Materializing Fix — no-use, full argument, per player.** The shift-based materialization
   (§4-T7c) must be shown to realize the same crop `T7.v`'s own `CroppedMg'`/`Gameover'`
   definitions specify — an *extensional* argument (skill §4f/§3.2), not structural, the same
   discipline `t1::model::fix_piece`'s own clear-line fusion already required one layer down.
5. **Drop — composite, no separate argument** beyond §4-T7h's guard-placement note.
6. **`receive_garbage`/`receive_gameover`/`receive_disconnect` — cross-machine argument.** Each
   realizes one `Receive` event: a queue pop on the sender/receiver pair, in `net.rs`'s own
   reliable-delivery state (§15.2), not anything `Machine` itself tracks.
7. **`notice_disconnection` — stutter w.r.t. `s6`, single-`Machine`.**
8. **`DisconnectPlayer` — realized by nobody's `Machine`, argued against `net.rs`/host reality
   directly** (§4-T7f).

---

## 9. Tests (`tests/`)

- **`test_instance.rs`** — a **new** fixture (cannot `include!` `t1`'s verbatim, unlike every
  prior layer: `t1`'s `TestInstance` has `CellExtra = Infallible`, and T7 needs `Garbage`). Its
  own small `Piece`/grid/rotation data (mirroring `t1/tests/test_instance.rs`'s own scale and
  reasoning — a compact board, two hand-picked piece shapes), plus a `Garbage` marker and its
  `Colored` impl, then `impl t1::model::Params for TestInstance { type CellExtra = Garbage; ... }`.
  A 3-player roster fixture (`PLAYER_COUNT = 3`) for the multiplayer-specific suites below.
- **`oracle.rs`** — reuses `t6`'s own oracle for the `s6` portion (§0.1's reuse principle
  applied to testing scope); hand-rolls `garbage`/`target`/view-array logic independently, the
  same independence discipline every prior oracle follows.
- **`model_unit_test.rs`** — golden vectors: garbage generation/cancellation (`GeneratedGarbage`/
  `GenRemGarbage` truth tables, mirroring `t2/tests/model_unit_test.rs`'s own scoring-table
  style), materialization (unobstructed, overflow-to-gameover, forbidden-zone-recheck-after-
  materialization), `drop_piece` reaching the same materialized result as an equivalent
  `fall_step` sequence ending in a fix, target round-robin across a 3-player trace, each
  `receive_*` method's field update, `notice_disconnection`'s idempotency, §4-T7h's guard
  (a `WinnerMulti` `drop_piece` leaves `py`/`px` byte-identical to before the call).
- **`model_properties_test.rs`** — `proptest`: `winner_multi`/`next_target` never return `self`
  except the documented no-alternative case; differential oracle over every snapshot field.
- **`model_fuzz_test.rs`** — multi-instance harness: several `Machine`s in one process, each
  one's outgoing values (`rem_gen_garbage`, `gameover_view[my_index]` after a fix) wired
  directly into others' `receive_garbage`/`receive_gameover`/`receive_disconnect` calls — no
  socket, no `net.rs` — exercises the full event set including disconnect/notice without
  networking, the same harness shape §0.4 already commits to reusing as `net.rs`'s design
  precedent (§15.2).

---

## 10. Acceptance oracle

1. Every `T7.v` definition with a §3 mapping is realized; every "not emitted"/"no `Machine`
   method" entry is absent from `model.rs`.
2. `connected`/`messages` are not fields anywhere in `model.rs`.
3. `fix_piece` calls `self.s6.fix_piece(bag_new)` first, unconditionally runs §4-T7c's
   shift/overwrite after (no `player_count = 1` branch anywhere in `model.rs`), short-circuits
   the overflow/`intersect` checks but not the shift/overwrite when `self.s6`'s `gameover` is
   already `true`, and returns `false` with zero mutation if the inner call fails.
4. `drop_piece` guards `winner_multi` **before** relocating (§4-T7h), and calls `self.fix_piece`
   (T7's own), never `self.s6.drop_piece`.
5. `receive_garbage` takes no `from`; `receive_gameover`/`receive_disconnect` do.
6. No method checks `connected` internally (it doesn't exist to check).
7. `holes` is passed fresh per `fix_piece`/`fall_step`/`drop_piece` call site by the caller
   (`session.rs`/`app.rs`), never persisted inside `Machine`.
8. `net.rs`, `session.rs`, `app.rs`, and `text.rs` are all `pub mod`-declared in `lib.rs`;
   `model.rs` still never imports any of them (§0.4).
9. `tests/` passes: unit + fuzz fully; properties under `proptest`.

---

## 11. Instantiation (`instance.rs`)

```rust
use t1::model::Params;

/// No `T7.v` counterpart (§0.1's Colored discussion) — the reserved "not a real piece" cell
/// content, unit-valued: garbage rows carry no further information (unlike a real Piece, whose
/// identity picks a color; every garbage cell renders identically, §14.2).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Garbage;

impl t1::view::Colored for Garbage {
    fn color(&self) -> [f32; 4] {
        GARBAGE_BLOCK_COLOR // §14.2
    }
}

/// A new marker type, distinct from `t1::instance::Tetris` (unlike every prior layer's own
/// `instance.rs`, which adds a `Params` impl *for* `t1::instance::Tetris` directly) — the only
/// thing that differs is `CellExtra`, but `Params` bundles every item into one trait, so a
/// distinct `CellExtra` needs a distinct implementing type. Every other item delegates to
/// `t1::instance::Tetris`'s own values rather than restating them — the identical pattern
/// `t4`'s/`t5`'s/`t6`'s own `tests/test_instance.rs` already use for their `TestInstanceWide`
/// marker (a second type reusing another's `Params` values while differing in one respect),
/// applied here to a `src/instance.rs`, not a test fixture.
pub struct Tetris;

impl Params for Tetris {
    type Piece = t1::instance::Piece; // the exact same real Piece type — its own Colored impl
                                       // (rs_t1_src_instance.rs) already applies, unchanged
    type CellExtra = Garbage;

    const PW: i64 = <t1::instance::Tetris as Params>::PW;
    const FY: i64 = <t1::instance::Tetris as Params>::FY;
    const FX: i64 = <t1::instance::Tetris as Params>::FX;

    fn piece_all() -> &'static [Self::Piece] { <t1::instance::Tetris as Params>::piece_all() }
    fn initial_main_grid() -> &'static Vec<Vec<bool>> { <t1::instance::Tetris as Params>::initial_main_grid() }
    fn forbidden_grid() -> &'static Vec<Vec<bool>> { <t1::instance::Tetris as Params>::forbidden_grid() }
    fn rot_grid(p: Self::Piece, r: u8) -> &'static Vec<Vec<Option<Self::Piece>>> { <t1::instance::Tetris as Params>::rot_grid(p, r) }
    fn initial_y(p: Self::Piece) -> i64 { <t1::instance::Tetris as Params>::initial_y(p) }
    fn initial_x(p: Self::Piece) -> i64 { <t1::instance::Tetris as Params>::initial_x(p) }
}

// t2::model::Params through t6::model::Params, t7::model::Params: empty/delegating marker
// impls, the same mechanical shape every prior layer's own instance.rs already uses.
impl t2::model::Params for Tetris {}
impl t3::model::Params for Tetris {}
impl t4::model::Params for Tetris {
    const NEXT_LEN: i64 = <t1::instance::Tetris as t4::model::Params>::NEXT_LEN;
}
impl t5::model::Params for Tetris {}
impl t7::model::Params for Tetris {}
```
`piece_color` is **not** re-exported here — `t7::view` never routes a locked cell's color
through a closure at all (`t1::view::draw_grid` dispatches via `Colored` directly, §0.1); only
`draw_piece`/`draw_ghost`/`draw_preview`/`draw_hold_box` still need a `piece_color` closure, and
`t1::instance::piece_color` is imported directly from `t1::instance` at those call sites, same
path every prior layer already uses.

---

## 12. Generator determinism rules

Inherit `t1`–`t6/implementation.md` §12's "reuse over restatement" verbatim.

---

## 13. `instance.rs` parameters

`NEXT_LEN` unchanged from `t1::instance::Tetris`'s own (delegated, §11). No parameter beyond
`CellExtra = Garbage` is genuinely new to this layer.

---

## 14. `view.rs`

### 14.1 Public API

```rust
pub fn render<P: Params>(
    constants: &t6::view::RenderConstants,
    machine: &Machine<P>,
    banner: Option<&t6::view::Banner>,
    opponents: &[OpponentView<P>],
    font: Option<&Font>,
)
where
    P::Piece: t1::view::Colored,
    P::CellExtra: t1::view::Colored,
{
    t6::view::render(constants, &machine.s6, t1::instance::piece_color, banner, font); // own board, unchanged
    draw_side_regions(constants, machine, piece_color, opponents, font);               // §14.2 + §14.3
}

/// T7's own two additions alone — the gauge and the strip, without the
/// own-board half. `S8` (§15.0) draws a filler board beside them.
pub fn draw_side_regions<P: Params>(
    constants: &t6::view::RenderConstants,
    machine: &Machine<P>,
    piece_color: impl Fn(P::Piece) -> [f32; 4],
    opponents: &[OpponentView<P>],
    font: Option<&Font>,
) { /* draw_garbage_gauge (§14.2), then draw_opponent_minis (§14.3) */ }
```
Own board reuses `t6::view::render` on `&machine.s6` whole — unlike every prior layer, which
splices a new draw call *between* existing ones (a ghost, a preview column), T7's two additions
are self-contained regions of the canvas (a side gauge, a strip of minis) that don't interleave
with anything `t6::view::render` already draws, so calling it as an opaque whole (rather than
its individual sub-procedures, skill §7) is the direct realization here, not a rejected
alternative — there's nothing to interleave with.

### 14.2 Garbage gauge

Vertical bar, one `cellSize`-height segment per unit of `machine.garbage`, clamped at `HM`,
single flat color (`GARBAGE_GAUGE_COLOR`), positioned in the panel margin — no `T7.v`
counterpart (rendering only). Deliberately distinct from `GARBAGE_BLOCK_COLOR` (§11), which is
what a locked garbage cell in `mg` renders as via `Colored`: the gauge warns about garbage not
yet materialized, so it renders differently from the block it eventually becomes.

### 14.3 `OpponentView<P>` and the mini-grid strip

```rust
/// No T7.v counterpart — populated by `Session::opponent_views` from received State broadcasts
/// (§15.3), never through Machine's own fields (an opponent's board is never local state).
pub struct OpponentView<P: Params> {
    pub player_index: usize,
    pub name: String,
    pub mg: Vec<Vec<Option<t1::model::PieceOrExtra<P>>>>,
    pub p: P::Piece,
    pub py: i64,
    pub px: i64,
    pub pr: u8,
    pub gameover: bool,
    pub connected: bool,
}
```
**Where the strip goes.** Fixed-size canvas region regardless of `opponents.len()`; mini cell
size computed to tile all entries in rows × columns within that region — more opponents shrink
each mini, never grow the strip.

The region is the window's right margin **beyond `t4::view`'s preview column** — from
`t4::view::compute_layout::<P>(constants).right_origin + panel_width` to `screen_width()`, not
from the main grid's own right edge. The distinction is the whole of it: `t1::view` centers the
grid, so the right margin equals `origin_x` and *looks* free, but `t4/implementation.md` §14.2
already spends the first `panel_width` of it on the "Next" column ("the right (preview) panel
reuses the left panel's own `panel_width`"). Starting the strip at the grid edge would therefore
draw the minis straight over the preview pieces — the correct left-to-right ordering is hold
panel, grid, Next column, then minis. What is genuinely untouched is only what remains past the
preview column, which is nonempty at ordinary window sizes because `panel_width` is clamped at
`PANEL_MAX_PX` while `origin_x` keeps growing with the window. On a window too narrow to leave
anything over, the strip's own `strip_w <= 0` early-out drops the minis entirely rather than
overlapping — degrading by omission, the same clip/clamp precedent the hold box and
`preview_count` already set.

The garbage gauge is unaffected: at `cell_size/3` wide it fits inside the gap between the grid's
right edge and `right_origin`, where §14.2 already puts it.

`render` is `t6::view::render` followed by **`draw_side_regions`**, which is `pub` and carries
the gauge and the strip alone. `S8` (§15.0's mid-match filler) needs exactly that half: there the
own-board region shows a `t6::model::Machine` filler game while the real `Machine<P>` is alive
but headless, so the strip and the gauge must render off the latter while the board renders off
the former. A mini renders as a flat, uniformly-gray placeholder before that player's first `State`
has arrived; once known, a mini is drawn dead (flat gray, overriding `Colored`) once `gameover`
or `!connected` — either alone is sufficient. With more than one opponent, the mini whose
`player_index` equals `machine.target` is outlined with a thicker border — the current garbage
target is otherwise ambiguous; with exactly one opponent, no override is drawn (the target can
only ever be that one player).

---

## 15. `main.rs`/`session.rs`/`net.rs`/`app.rs`/`text.rs` — networking

### 15.0 Screens

Ten screens, `S1`–`S10` (this file's own naming, used throughout this section and §4/§14), each a
DOM-free macroquad state: a `step_*` function (`app.rs`) that mutates the screen's own state and
returns an outcome, and a matching `draw_*` function. With no widget toolkit at all, each screen's
**actions are keys (or a gamepad button) rather than clicks**.

| `App` variant | id | shown | actions |
|---|---|---|---|
| `ModeSelect` | `S1` | "Single Player" / "Multi Player" | `[1]` → `Single`; `[2]` → `RoleSelect` |
| `RoleSelect` | `S2` | "Host" / "Join" | `[1]` → `Host`; `[2]` → `Join` |
| `Single` | `S1`'s SP branch | the T6 board alone | ordinary game input |
| `Host` | `S3` | name field; "Add player" button (`AddConnection::Idle`) → a paste field for the joiner's code, no host code shown yet (`EnteringCode`, §15.1a′) → the host's own code for that pairing, itself shown as a read-only field (`Connecting`, auto-clears on Join); the joiner list; "Start game" button, greyed with "Not enough players." until there's a joiner | `[↑]/[↓]`/gamepad D-pad move focus among the 3 stops (§15.1a), `[Enter]`/gamepad button 0 activates the focused stop, `[Ctrl+N]`/`[Ctrl+S]` remain as power-user aliases for Add/Start, `[Esc]` cancels the paste box or leaves the lobby (§15.1a′), `[Ctrl+C]`/`[Ctrl+V]` copy/paste the focused stop |
| `Join` | `S4` | name field; own code, shown as a read-only field, initially focused; the "paste the host's code" field, always editable (§15.1a′ — no gate); "Connect" button | `[↑]/[↓]`/gamepad D-pad move focus among the 4 stops, `[Enter]`/gamepad button 0 activates the focused stop, `[Ctrl+C]`/`[Ctrl+V]` copy/paste the focused stop |
| — | `S5` Rejoin | — | none: `S5`'s only action is automatic, so it is `Session::rejoin` called in passing, with no frame on which it would be drawn |
| `Waiting` | `S6` | `t6::model::Machine` filler game; roster; "Waiting for host…" | ordinary game input |
| `Playing { filler: None }` | `S7` | `t7::model::Machine`; strip + gauge (§14) | ordinary game input |
| `Playing { filler: Some(_) }` | `S8` | filler game + a live strip/gauge off the headless real `Machine` | ordinary game input |
| `Winner` | `S9` | "You win" / "Winner: `<name>`"; "Rematch"; "Leave" | `[1]` Rematch, `[2]` Leave |
| `HostLost` | `S10` | "Connection to host lost."; "Return to menu" | `[1]` |

`S8` is deliberately **not** its own `App` variant: it is `S7` with a filler running. The real
`Machine<Instance>` stays alive underneath — still pumped, still fed `receive_garbage`/
`receive_gameover`/`receive_disconnect` — so `winner_multi`/`find_winner` stay current and the
mini strip keeps rendering (`draw_side_regions`, §14.1, is exactly the half of `render` that
still runs off the real `Machine` while `S8`'s own board region shows the filler instead).

**`S7` → `S8` is gated, not immediate.** The frame `gameover_view[my_index]` first flips `true`,
`filler` stays `None` for at least `GAMEOVER_FILLER_DELAY_SECS` (1s) — during that window `S7`
keeps rendering the real `Machine`, whose own "GAME OVER" (`draw_game_over`, `t2::view`) is what
the player actually sees, rather than being silently swapped for a filler in the same frame the
flag flips (which would skip the banner entirely). Only once that delay has elapsed **and** any
key or gamepad button has been pressed (`t1::misc::any_action_just_pressed`, the same primitive
`Single`'s own restart-on-keypress uses) does `filler` become `Some(fresh_single())`. Once in
`S8`, the filler carries its own "Game over. Waiting for the game to finish." label
(`draw_gameover_filler_overlay`) so it reads as a holding pattern, not a fresh single-player game.

`S10` is reached from `S6`/`S7`/`S8` whenever the link drops while no winner has resolved; a
resolved winner takes `S9` instead even if the connection is lost immediately after. The code
consults `find_winner` before `noticed_disconnect` for exactly that ordering.

**`find_winner`** — has no `T7.v` counterpart and lives in
`session.rs`, not `model.rs`: it is the "exactly one player still `playing_view`" fold over
`gameover_view`/`connected_view`, and `winner_multi(self)` is its `Some(my_index)` special case.

### 15.1 Lobby and roster

Two roles, chosen at `S2`'s role-select screen, reached from `S1`'s "Multi Player": **Host** or
**Join**. The host performs one STUN
lookup (§15.2) per prospective joiner and generates a short connection code (public address +
local address + a random nonce) to share out-of-band (voice call, chat — a short string, not a
file); each joiner does the same and pastes both codes in. Once a joiner's reliable channel to the host is
up (§15.2's handshake), the joiner sends `Join { name }`; the host assigns the next free roster
index (`Host` is always index `0`, by convention — its own slot is filled at lobby creation, not
via a `Join` message it sends itself), rebroadcasts `Players { roster }` to everyone connected so
far, and repeats per additional joiner. On "Start," the host freezes `player_count`, sends
`Start { player_count, my_index }` (a distinct `my_index` per joiner) to each, and every peer —
host included — constructs its own `Machine::new(my_index, player_count, ...)` (§6.1) at that
point, not before.

#### 15.1a Name entry, focus, and the ordered code exchange

**Names are literal, per-role defaults, not inferred from the environment.** `S3`'s name field
seeds `"Host"`, `S4`'s seeds `"Player"` — both freely editable until the name matters (`Start`
for the host, `Join` for a joiner). A blank field falls back to that same literal rather than
announcing an empty string, so the roster never shows a nameless slot (`entered_name`'s
`fallback` parameter).

**Focus is a clamped index into a fixed set of stops** (`HostLobby`/`JoinLobby`'s own doc
comments — `move_focus`), navigated with `[↑]/[↓]` or gamepad D-pad up/down, `[Tab]` kept as a
"move down" alias. It clamps at both ends rather than wrapping: a short, linear, top-to-bottom
form has no natural "next" destination past its last stop. `S3` has 3 stops (name, Add-player/
Start's Add-player button or the joiner's-code field depending on `AddConnection`'s state,
Start game); `S4` has 4 (name, "Your code" — read-only but focusable/copyable, initially
focused — "Host's code", Connect). `[Enter]`/gamepad button 0 (`South`, `Action::gamepad_button`'s
own "button 0 = South" convention) activates whichever stop is focused: a button fires its
action, a text field submits (`S4`'s Host's-code stop) or is otherwise a no-op. Keystrokes/paste
apply only to the focused editable field; macroquad's `get_char_pressed` drains one global queue,
so the frame polls it **once** into a `TextEdit` and applies that to the focused field only — a
field polling the queue itself would starve the others, and an unfocused one would swallow
keystrokes meant for the focused one. Holding `[Backspace]` autorepeats after `BACKSPACE_DELAY`
(0.35s), every `BACKSPACE_ARR` (0.05s) thereafter — a separate, independently-tuned timer from
gameplay's own `DAS_DELAY`/`ARR` (`process_input`), reusing `RepeatTimer`'s shape but not its
instance, so retuning one can never silently retune the other.

The focused stop's field/button is drawn in `CODE_COLOR` (the same light green used for the
connection code itself); everything else stays dim. There is no bold font asset loaded, so this
color change is the whole of "focused" — no separate weight.

**`[Ctrl+C]` copies whichever stop is focused — the name field, either screen's own connection
code, or the joiner's-code/host's-code entry field, whichever text a given stop holds — a button
stop (`S3`'s "Add player"/"Start game", `S4`'s "Connect") has nothing to copy.**
`[Ctrl+V]` pastes into whichever editable stop is focused. §15.1's exchange is out-of-band and the
code is 32 characters of base32.

**Mode Select (`S1`) and Role Select (`S2`) share the same up/down + `[Enter]`/gamepad-button-0
model**, via a loop-local `menu_index` (not part of `App` — see `App::ModeSelect`'s doc comment
on why a payload there would force every `std::mem::replace(&mut app, App::ModeSelect)` placeholder
call site to supply a dummy value) rendered the same `CODE_COLOR`-highlight way. The
digit-key shortcuts (`[1]`/`[2]`, read from the OS-translated character stream, not a fixed
`KeyCode` — AZERTY etc.) work as an alias alongside arrows/gamepad/Enter.

**Neither direction goes through miniquad's own clipboard**
(`clipboard_set`/`clipboard_get`), which on Linux is unsound both ways, for two *different*
reasons — fixing only the write side leaves the read side broken by the write side's own fix:

- **Writing is broken on both of miniquad's Linux backends, independently of anything this app
  does.** On X11 (miniquad's default `LinuxBackend`, so this is the path taken even inside a
  Wayland session, via XWayland) the selection owner answers only `target == UTF8_STRING` and
  denies everything else; `TARGETS` appears nowhere in its X11 code. Modern clipboard consumers,
  XWayland's own bridge included, ask `TARGETS` first to discover formats, get a denial, and
  conclude the selection offers nothing. `XSetSelectionOwner` succeeds regardless, so nothing
  surfaces as a failure. On native Wayland it offers the MIME type `"UTF8_STRING"`, an X11 atom
  name rather than a MIME type; Wayland clients request `text/plain;charset=utf-8`, match no arm
  of the request handler, and get an empty fd either way.
- **Reading breaks as a consequence of fixing writing.** Once `copy_out` (below) shells out to
  `wl-copy` to work around the point above, the text lands on the *Wayland* compositor's
  clipboard — but this app is still reading through the X11 backend's `XConvertSelection`
  against the X `CLIPBOARD` selection. Nothing on the X side owns that selection unless
  XWayland's own clipboard bridge is both present and willing to forward it, which is
  compositor-dependent and not something this app can assume; the request comes back with no
  property set, `clipboard_get` returns `None`, and paste silently does nothing. Reading is not a
  passive operation unaffected by the write side's own backend problem: the write side's own
  workaround (below) is exactly what removes the selection owner the read side otherwise
  depends on, so fixing only the write side would leave the read side broken.

On Linux the two directions differ. `paste_in` shells out to whichever of `wl-paste`/`xclip -o`/
`xsel -o` is installed for reading, falling back to `clipboard_get` only as a last resort — which
still covers the one case that was never broken, a real X11 application (not this one) holding
the selection. This is the same hand-rolled-over-dependency instinct §15.2 already applies to
STUN and the reliability layer, rather than taking on a clipboard crate and its X11 stack.
`copy_out` does not attempt a comparable X11 fallback chain: `xclip`/`xsel` were tried the same
way for writing and never worked reliably from this app's own X11-client window, so **X11 copy is
not implemented** — `copy_out` only ever shells out to `wl-copy`, and only when `WAYLAND_DISPLAY`
shows a real Wayland session for it to talk to. The write-side helper daemonizes after reading
stdin, as any selection owner must, so the spawn does not block the frame loop; the read-side
helpers are ordinary one-shot child processes whose captured stdout is the result. On every other
platform miniquad's own implementation is fine both ways and is used unchanged.

**Every copy is printed to the console, never silent.** Regardless of platform or whether
`copy_out` actually reached the system clipboard, `copy_to_clipboard` prints
`<field name>: <field content>` — covering "your name", "your code", "host's code", and "joiner's
code" — so the content is always reachable from the terminal the game was launched from, X11
included. The status line separately reports what the clipboard attempt itself did, without
naming which mechanism was tried: "Text copied to the clipboard and printed to the console." on
success, "`<tool>` unavailable; content copied to the console." when the tool isn't installed,
"`<tool>` failed; content copied to the console." when it ran but didn't take the text, or the
X11-specific "Copy not implemented on X11; content printed to the console." when there was no
`WAYLAND_DISPLAY` to try `wl-copy` against. The read side has no equivalent on-screen message: a
failed paste leaves the field unchanged, which is already visible as "nothing happened," and every
candidate in `paste_in`'s own chain, `clipboard_get` included, ends in `None` on failure rather
than a panic.

#### 15.1a′ `S3`'s connection sub-flow — `AddConnection`

`S3`'s "Add connection" is a four-phase sub-flow, `AddConnection` (`Idle` /
`EnteringCode(TextInput)` / `Discovering { pending, joiner_code }` / `Connecting { code, peer_id }`):
a paste box for the joiner's own code opens first, with nothing minted and no host code shown;
once that code is entered, this pairing's own STUN lookup runs on a background thread
(`Discovering` — `PendingEndpoint`, §15.2 below), so entering it never blocks the frame loop; only
once that lookup resolves and the connection succeeds does the host's own code for that specific
pairing appear (`Connecting`).

**What's minted and what's displayed are the same value, by construction.** `Connecting`'s `code`
field is captured from the *same* `Endpoint` that `poll_add_discovery` goes on to call
`connect_to` with — captured before that call consumes it — so there is no second endpoint for
the display to drift from.

**A fresh endpoint per joiner is required, not merely convenient.** `NetWorkerHandle::register`
calls `socket.connect(peer)`, which locks a UDP socket to exactly one remote peer for its
lifetime — this is what makes the star topology's "no joiner ever punches a hole to another
joiner" hold at all (§15.2's own closing paragraph: "one `UdpSocket` per connection"). A
connection code names one specific socket's STUN-discovered address, so one code is tied to one
socket is tied to one joiner; §15.1 already says "one STUN lookup per prospective joiner ... and
repeats per additional joiner." Reusing one socket/code across simultaneous joiners is not a
viable alternative: a shared socket can only ever be `connect()`-locked to one peer, so a second
joiner's traffic would have nowhere valid to land.

**One connection in flight at a time.** `begin_add` (`[Ctrl+N]`) is a no-op unless `Idle`: only
one paste-box-then-code dialog is ever open at once. `poll_add_completion`, called every frame,
resolves the specific `peer_id` recorded in `Connecting` to its *current* slot in
`session.peers` via `Peer::id` — not a `Vec` position, since a `Leave` elsewhere in the lobby
(§15.1b) can splice an earlier peer out and shift every later one down while this pairing is
still in flight — and auto-clears back to `Idle` once that joiner's `Join` has actually landed
(`index` going from `None` to `Some`), or once the peer is gone entirely without ever joining;
either way the roster line, or its absence, becomes the visible confirmation, and `[Ctrl+N]` is
available again for the next joiner.

**`[Esc]` cancels the innermost open thing.** While `EnteringCode` (the paste box is open),
`[Esc]` calls `cancel_add` — back to `Idle`, nothing minted, the whole lobby not left. In every
other state (`Idle`, `Discovering`, `Connecting`, or no `S3` sub-dialog at all) `[Esc]` keeps its
ordinary meaning: leave the lobby entirely, back to `S2`. Leaving mid-`Discovering` drops the
`PendingEndpoint`; its background thread finishes its one STUN round trip and exits normally with
nowhere to send the result.

**`S4`'s two fields are both always reachable — no lock is needed.** The host's code for a given
pairing does not exist until the host has already processed that joiner's own code (minted only
once `Discovering` resolves, above), so there is no invalid code a joiner could paste before the
host has one to give — both of `S4`'s fields stay open for input the whole time.

#### 15.1b `Leave`, rematch, and the match-generation counter

Three lobby-flow features beyond the base `Join`/`Players`/`Start` exchange (§15.1), each
addressing a specific gap that exchange alone leaves:

- **`Leave`** — sent by a joiner leaving from `S9`. The host splices that
  slot out of `peers`, shifts every later slot's roster index down, and re-broadcasts `Players`.
  Unlike a mid-match disconnect (§15.4), a `Leave` slot is *not* kept as a phantom. Host-only in
  effect, and ignored once a `Machine` exists — renumbering a frozen roster mid-match would
  invalidate every index already in flight. A leaving **host** sends nothing at all: its own
  departure is exactly what every other client's `DisconnectPlayer pl = Host` case already
  reasons about (§4-T7f).
- **Rematch** — the host's post-game screen *is* its pre-match `S3`, and a
  joiner re-sends `Join` over the connection it already has (`S5`). `Session::reset_for_rematch`
  drops the `Machine`, roster, boards, and disconnect latch while keeping every `Connection`;
  the host additionally clears peer indices so the fresh roster is rebuilt from the `Join`s that
  follow — a peer that leaves instead of rematching simply never sends one. The host and a joiner
  press Rematch independently, so a joiner's rejoin `Join` can arrive before the host has pressed
  its own Rematch (and thus before the host's `reset_for_rematch` has run) — the host's `Join`
  handler still rejects it (`self.started()` is still true), and a message sent only once would be
  lost for good. So `Join` isn't sent just once: a joiner resends it on the same period as the
  §15.2-step-5 lobby keepalive (both fold into `Session::send_keepalive`), for as long as no match
  has started — a harmless no-op once the host has already assigned an index, and otherwise the
  retry that survives the ordering race.
- **The match-generation counter** — `match_gen`, incremented once per
  `Start` (a rematch's included), carried on the `Routed` envelope, and checked on receipt: a
  message tagged with a generation this peer has left is discarded. Without it a `Garbage` or
  `State` still in flight when a match ended could land in the rematch that follows, against a
  roster whose indices need not even mean the same players. `Join`/`Players`/`Start`/`Leave` are
  lobby messages and travel untagged, outside the envelope entirely. Named `match_gen`, not
  `gen`: `gen` is a reserved keyword from edition 2024 on, and every crate here is edition 2021.

### 15.2 NAT traversal and the reliable channel

Per connection (host ↔ each joiner — the star topology means no joiner ever punches a hole to
another joiner):
1. **STUN.** A minimal, hand-rolled client: one UDP Binding Request to a public STUN server,
   parse the `XOR-MAPPED-ADDRESS` attribute from the response. No dependency — the request/
   response shape (RFC 5389) is small enough that a hand-rolled parser stays short and fully
   auditable, the same preference for small, dependency-free, fully auditable protocol code this
   file applies throughout networking (this section's own reliability layer below, §15.1's
   clipboard exchange).

   A host's public address, as STUN reports it, is the specific external `ip:port` *mapping* this
   one socket's NAT assigned it — not merely the NAT's public IP. Two machines behind the same
   (e.g. carrier-grade) NAT get independent outbound mappings for their own sockets, each its own
   port, so a shared public IP does not collide: the code names the one mapping that actually
   leads back to this host's own socket. What this does assume is an ordinary (non-symmetric)
   NAT, the same assumption any STUN/hole-punching design makes — a symmetric NAT, which assigns
   a different external port per *destination*, would make the address STUN discovered (talking
   to the STUN server) unusable for a joiner's own hole-punch attempt (talking to the joiner);
   this crate does not detect or work around that case.
2. **Manual code exchange** (§15.1) — the only signaling step, no server involved.
3. **Simultaneous open.** Both sides send a few UDP packets, a few hundred ms apart, to the
   other's discovered address, tagged with the shared nonce so the first genuine reply is
   distinguishable from noise. Knowing the peer's address from the code exchange is not enough on
   its own: most NATs only forward an inbound packet from an address this socket has already sent
   an outbound packet *to* — the mapping is opened by outbound traffic, per destination, not
   merely by the socket existing. So each side still has to punch its own NAT open before the
   other's packets can arrive, regardless of who "knew" the address first; sending a few, a bit
   apart, is what tolerates the first one or two being dropped before both mappings are open.

   UDP rather than TCP for exactly this reason: hole-punching this way needs to send an
   unconnected-looking datagram to an arbitrary address with no prior handshake, which is what
   UDP already is — the TCP equivalent (a simultaneous-SYN "TCP hole punch") is far less reliably
   supported across real NAT/firewall implementations. TCP's own stream reliability and ordering
   would also be the wrong tool twice over here: `Garbage`/`Gameover`/lobby traffic gets its own
   reliable layer anyway (below), sized to this app's own needs, while `State` is deliberately
   best-effort — a lost or stale frame should be superseded by the next one, not held up behind a
   retransmit the way a TCP stream would.
4. **Handshake.** Once a tagged packet is received from the expected peer, a `Hello`/`HelloAck`
   pair (over the reliable framing below) confirms two-way delivery before `Join` is ever sent.
5. **Keepalive.** Once a match has started, no separate mechanism is needed — the periodic
   `State` broadcast (§15.3, ≥3 Hz) is far more frequent than any NAT mapping's inactivity
   timeout, and doubles as one for free. But `State` only exists once a `Machine` does, i.e.
   after `Start` — before that, the `S3`/`S4`/`S6` lobby and waiting room have nothing following
   the one-shot handshake, so both sides instead send a bare `Ping` (§15.3) on a short period
   (well under the disconnect timeout, §15.4) for as long as no match has started.

**Step 1 runs off the frame thread.** A STUN round trip can take a few seconds under packet loss
or against an unreachable server; `session::PendingEndpoint` spawns `Endpoint::discover()` on a
background thread and hands the result back over a channel (`session::endpoint_discovered`, the
same status-message logic a synchronous `mint_endpoint` also uses), so entering the Join screen
or a host's "Add connection" (§15.1a′) never blocks the frame loop on it. This is the one-shot,
one-lookup analogue of `NetWorkerHandle`'s own background-thread-plus-channel shape (§15.5).

**Reliable, ordered delivery** (carries `Garbage`/`Gameover`/`Disconnect`/`Join`/`Players`/
`Start`/`Hello`/`HelloAck`): a per-connection sequence number, acknowledged by the receiver;
unacknowledged sends are retransmitted on a short timer; a receiver buffers an out-of-order
arrival and only delivers up through the next *contiguous* sequence number — a small, fully
custom protocol (no `T7.v` counterpart; this is exactly the "reliable, no loss/duplication/
reordering" network axiom `T7.v` assumes, realized rather than assumed).

**Best-effort delivery** (carries `State` only): no sequence/ack/retransmit — a monotonic
counter lets a receiver discard a State packet older than the last one already applied, nothing
more. A stale or dropped `State` is superseded by the next one within a fraction of a second; it
carries no formal-model guarantee to uphold (§14.3's `OpponentView` is rendering-only).

Both kinds of framing share one `UdpSocket` per connection (a one-byte tag distinguishes them),
avoiding a second punched hole per peer.

**Hardening beyond this section's own guarantees**, none of it changing what's observable absent
a hostile or malfunctioning peer: `ReliableSender` caps its own unacknowledged backlog at
`MAX_UNACKED_MESSAGES`, evicting the single oldest entry first, so a peer that keeps a connection
superficially alive but never acks anything cannot grow it without bound. `ReliableReceiver` caps
its own out-of-order reorder buffer at `MAX_REORDER_WINDOW`, dropping — and deliberately not
acking — anything further out, so a peer that never sends the packet that would close a gap
cannot grow that buffer without bound either. And `decode_message` bounds decompression against a
per-connection byte cap sized off that connection's own board dimensions
(`net::recommended_max_decoded_bytes`), so a small, highly-compressible payload cannot inflate to
an unbounded size on the connection thread.

### 15.3 Wire format

```rust
#[derive(Serialize, Deserialize)]
enum Payload {                                        // carried inside a Routed envelope only
    Garbage { amount: i64 },                          // spec: GarbageMessage
    Gameover,                                          // spec: GameoverMessage
    Disconnect,                                        // spec: DisconnectMessage
    State {                                            // rendering-only, best-effort channel
        p: /* Piece, instance-specific */, py: i64, px: i64, pr: u8,
        mg: /* flattened cell grid */, gameover: bool,
    },
    Join { name: String },                             // lobby-only
    Players { roster: Vec<String> },                   // lobby-only
    Start { player_count: usize, my_index: usize, match_gen: u64 }, // lobby-only
    Leave,                                             // lobby-only (§15.1b)
    Hello { nonce: u64 },                              // handshake-only (§15.2)
    HelloAck { nonce: u64 },                           // handshake-only
    Ping,                                               // lobby-only keepalive (§15.2 step 5)
}

#[derive(Serialize, Deserialize)]
enum Destination { Single(usize), Broadcast }          // Broadcast: every player but `from`

#[derive(Serialize, Deserialize)]
struct Message {                                       // the envelope (§15.4 relay, §15.1b match_gen)
    from: usize, to: Destination, match_gen: u64, body: Payload,
}

#[derive(Serialize, Deserialize)]
enum WireMessage {
    Untagged(Payload),                                 // lobby/handshake — no envelope, no match_gen
    Routed(Message),                                    // application traffic — see Message above
}
```
`Garbage`/`Gameover`/`Disconnect`/`State` are always sent as `Routed`, never `Untagged` — the
split into `Payload` (every message kind) and the minimal `Untagged`/`Routed` discriminator
exists so a `Routed` envelope cannot wrap another envelope (no more `WireMessage` self-reference)
and so the lobby-vs-application distinction — only application traffic carries `from`/`to`/
`match_gen`, only it is filtered by `match_gen` — lives at the type's top level rather than being
implicit in which variant a message happens to be. `Destination::Broadcast` means "every player
but `from`," never "the host" specifically: a message meant for exactly one recipient, host
included, is `Single(that player's index)` (`Garbage`, addressed to the sender's own `target`,
which may legitimately resolve to the host's own index `0`) — a joiner's physical send always
goes to the host regardless of `to`'s value, since a joiner has exactly one socket; `to` names the
*logical* final recipient(s) for the host to relay toward, not the next physical hop. `State`
carries no `seq` field of its own — best-effort sequencing lives in the outer packet framing's
sequence number (§15.2), not duplicated inside the payload.

Encoded as JSON (`serde`/`serde_json`) then deflate-compressed (`flate2`) before the reliable/
best-effort framing header is prepended; decoded in the reverse order on receipt. `net.rs` is
the only module that ever names `WireMessage` — `model.rs` never constructs or inspects one
(§0.4).

### 15.4 Host relay

The host maintains one reliable channel per joiner (not a broadcast socket — `T7.v`'s own star
topology, §0.1). On receiving a `Garbage`/`Gameover` from one joiner addressed onward (per that
joiner's own `Machine::target`/broadcast-to-everyone-else semantics — read off `rem_gen_garbage`/
`gameover_view[my_index]`, §4-T7d, exactly as any peer would for its own outgoing messages), the
host forwards it over the *target* joiner's own channel — a physical relay, not a model-level
concept (`T7.v`'s `messages` already models this as "whoever the host is currently relaying
between," §0.1). On detecting a joiner's channel has gone silent past a timeout, the host applies
`DisconnectPlayer`'s effect locally (§4-T7f) and relays `Disconnect` to every *other* connected
joiner. The host is a peer like any other for its own gameplay — it runs its own `Machine`
exactly as every joiner does, with `my_index = 0`.

### 15.5 Threading

One background thread **per `Session`, not per connection**, owns every `UdpSocket` and
reliability state machine that session has open, round-robining across them with a short
per-socket read timeout — not one OS thread per connection, and not `mio`/`epoll`/async: at the
connection counts a lobby ever reaches (host plus a handful of manually-paired joiners),
near-zero-latency event wakeup buys nothing a game loop already running at 60 Hz needs, and a
hand-rolled poll loop needs no new dependency, matching this file's own STUN client and
reliable-channel protocol (§15.2) in staying small and fully auditable.

`net::NetWorkerHandle::spawn()` starts that thread and returns a cheaply-`Clone`-able handle;
`Session` holds one (`new_host` mints its own, since the host lobby's `S3` starts with zero
connections; `new_joiner` is handed the one its caller already minted to make its first
connection, §15.1a′). `NetWorkerHandle::register(socket, peer, local_nonce, max_decoded_bytes)`
runs `socket.connect(peer)`/`set_read_timeout` synchronously on the caller's own thread (§15.2
steps 3–4); only handing the socket itself to the worker thread crosses a channel, drained
between round-robin passes. `max_decoded_bytes` is a decode-size bound (§15.2's hardening
paragraph) computed from the concrete instance's board dimensions
(`session::max_decoded_message_bytes`) and threaded straight through to the worker thread's
`decode_message` calls — `net.rs` has no `Instance` of its own to compute it from. The
`Connection` it returns carries an `incoming`/`outgoing` `mpsc` pair: decoded application events
are pushed into `incoming`, which the per-frame game loop drains with `try_recv()` (`Session::
pump`); outgoing messages are pushed into `outgoing`, drained and actually written to the socket
by the worker thread alone. Never a blocking read on the frame thread, satisfying "the game must
stay playable" regardless of network conditions.

Each round-robin pass, per connection: drain that connection's outgoing queue (assigning sequence
numbers, recording for retransmit), resend anything past `RETRANSMIT_INTERVAL`, then one bounded
`socket.recv` capped at the per-socket read timeout — so no one connection's silence can stall the
next connection's turn, or the worker's own next check of newly-registered/removed connections, by
more than that bound. That same bound is what caps how long any connection this thread owns can
ever be kept waiting behind another's turn — worst case, one full round costs (connection count) ×
(read timeout), comfortably under `RETRANSMIT_INTERVAL` at the connection counts §15.1 ever
reaches.

Removing a connection (a `Leave`, §15.1b, or the whole `Session` going away) tells the worker to
stop servicing it and returns immediately — no thread to join, since the socket was never that
connection's own thread to begin with. The worker thread needs no explicit shutdown call either:
it idles without touching a socket whenever it owns zero connections, and exits the moment every
handle/connection sharing it has dropped.

Outgoing sends go the other way: `Session::fire_and_broadcast` (`session.rs`) samples
`machine.gameover_view[machine.my_index]`/`machine.target` immediately **before** the
`fix_piece`/`fall_step`/`drop_piece` call it wraps, runs that call, and — if it may have fixed —
hands both pre-call values plus `rem_gen_garbage` (read and cleared via `take_rem_gen_garbage`) to
`Session::broadcast_after_fix`, which pushes the resulting `WireMessage`(s) into a connection's
`outgoing` channel; the worker thread alone ever touches a socket. Sampling `target` before the
call matters: `fix_piece` (§4-T7d) advances it to the next candidate in the same call that
produces this clear's garbage, so reading `machine.target` after the call would address the
*next* target, not the one this garbage is for. `app.rs`'s `step_playing_gameplay` is what calls
`fire_and_broadcast` per action/gravity tick; `main.rs` only drives that function, never reads
`rem_gen_garbage`/`target` itself.

### 15.6 `misc.rs`/`Action` — unchanged

```rust
pub use t6::misc::*;
```
T7 adds no player-facing action; the network events (`Receive`/`Disconnect`/`Notice`) are never
player input, dispatched from `net.rs` instead of a keybinding.

### 15.7 Everything else

`shuffle_bag`/`make_bags_fn`/`fresh_holes` (`session.rs`) and `fall_period`/`RunState`/
`after_action`/`process_input`'s DAS/ARR engine (`app.rs`) — unchanged in shape from
`t6/implementation.md` §15, generic over `t7::model::Machine<P>` instead of
`t6::model::Machine<P>`, reading `machine.s6.s4.s3.s2.…` (one hop deeper). `holes` (§4-T7c′) is
constructed the same way `bags_fn`/`piece_source` already are — a fresh RNG per call site, never
persisted on `Machine`.

**`holes` draws an independent column per row.** `T7.v` constrains it only by `ValidHoles`
(`0 ≤ holes y < WM`), so both a per-row column and a single shared one are admissible
refinements and the choice is the implementation's — but it is a *material* choice, not a
cosmetic one: with every row of a delivery holed in the same column, the stack gains a clean
vertical shaft the player drops an I-piece down to clear the whole delivery at once, which is
not what garbage is meant to cost. So each row draws its own.

The draw is **memoized by row**, which is what makes `holes` a *function* of `y` rather than a
generator: `ValidHoles` is asserted at every `holes(y)` invocation and §4-T7c may evaluate a
given row more than once, so a fresh draw per call would make `holes` non-deterministic within a
single `fix_piece`. The memo pins each row's column for the lifetime of one closure — which is
one call site, since the closure is built fresh at each (§15.7 above).
