# proofs.md — refinement proof, the Rust system ⊨ `T7.v`

Not a delta over `t6/proofs.md` in the sense `t5/proofs.md` → `t6/proofs.md` was:
every prior layer's obligation was "one `Machine<P>` refines the previous layer's
`Machine<P>`." `T7.v`'s own state (`connected`, `messages`) has no counterpart
inside any single `Machine<P>` — it is realized outside `model.rs` entirely
(`implementation.md` §0.4, §1). So the obligation here is **the Rust *system*
refines `T7.v`**, per player: `α` and every per-event argument span
`t7::model::Machine<P>` plus `t7::session::Session`'s and `t7::net`'s
lobby-and-relay layer, never `model.rs` alone.

`T7RefinesT6` (`T7.v`'s own definition) is a separate, already-stated fact about the
two Rocq specs (`T7.v` refines `T6.v`) — taken as given, not re-derived. The
obligation discharged in this file is Rust ⊨ `T7.v`, never Rust ⊨ `T6.v` directly.

**§§3, 7a, 8, 10 argue against compiled code.** `net.rs`, `session.rs`,
`instance.rs`, `view.rs`, and `main.rs` all exist; every claim below cites
the actual `net.rs`/`session.rs` source it is about, not `implementation.md`
§15's design contract alone.

## 0. Result

No unresolved gap. Three accepted, bounded divergences, each argued rather
than closed outright:

- `fix_piece`'s own `if connected s pl then SendMessages ... else messages s`
  gate, for the *acting* player's own connectivity, cannot be matched
  step-for-step in every case (§7a).
- The choice of `i64` (not a saturating/checked type) for `garbage`/
  `rem_gen_garbage`, and the defensive `amount.clamp(0, hm)`
  `Session::apply_local` applies to a received `Garbage.amount` before
  calling `receive_garbage` (§12).
- `ReliableSender::send`'s `MAX_UNACKED_MESSAGES` eviction (`net.rs`), which
  can drop a reliable message permanently rather than merely delay it, under
  a precondition (~1024 outstanding unacked sends to one peer) this app's own
  traffic volume cannot reach against a peer that is not already effectively
  dead (§8).

Two further points are load-bearing enough to call out up front, both argued
in full: `receive_gameover`/`receive_disconnect`'s target redirect and the
`from ↦ true` override in `redirect_target_from` (§6, §8), and the host's own
synchronous `receive_disconnect` call in `Session::check_timeouts`, which
collapses two `T7.v` steps (`DisconnectPlayer`, then the host's own
`ReceiveMessage`) into one real action (§10).

## 1. Scope

Safety only, per skill convention — same as every prior `proofs.md` in this
tower. Excluded from `T7RefinesT6` (hence from any "this Rust step *is* this
`T6.v` step" claim, `T7RefinesT6`'s own `H4`/`H5` hypotheses): a
materializing `Fix` (`remGarbage > 0`), including one reached via `Drop`.
This file's own obligation (Rust ⊨ `T7.v`) is not so excluded: every Rust
step, materializing or not, is argued against `T7.v`'s `Next` directly
(§4–§9 below).

## 2. `PlayerCount = 1`

`T7.v` describes this case too (its own header comment) but
`t7::model::Machine::new` refuses to construct at all unless
`player_count > 1` (an `assert!`, `implementation.md` §0.2/§6.1) —
single-player is realized entirely by `t6::model::Machine<P>` directly,
selected by `main.rs` before any `t7::model::Machine<P>` exists
(`implementation.md` §0). So `PlayerCount = 1` is discharged by
`t6/proofs.md` in full: `T7.v` reduces definitionally to `T6.v` at
`PlayerCount = 1` in every action that branches on it (`FixPiece`'s own
`if (PlayerCount =? 1)%nat then UpdatePlayer s pl s6' else ...`;
`Init`'s `connectedView`/`connected` are `PlayerCount >? 1`, both `false`;
`Receive`/`Disconnect`/`Notice` are unreachable since nothing is ever
`connected`). Nothing in this file's remaining sections applies to that
regime — `model.rs` itself contains no `player_count = 1` branch anywhere
(the acceptance-oracle check `implementation.md` §10.3 asks for).

## 3. State mapping `α : Σ → T7.State`, per player

`Σ` is the full system configuration: every player's `t7::model::Machine<P>`
instance, each `Session`'s own lobby/roster state (`Session::peers`,
`Session::role`, `Session::match_gen`), and the network layer (`net.rs`'s
per-connection `ReliableSender`/`ReliableReceiver`/`BestEffortReceiver` state
plus the host's own relay step in `Session::handle_routed`/`forward`). Per
field, in `T7.v`'s own field order, for a fixed player `pl`:

- `s6 α(σ) pl = α₆(σ.machines[pl].s6)` — `α₆` unchanged, imported from
  `t6/proofs.md` (`t6::model::Machine<P>` is a type alias for
  `t5::model::Machine<P>`, `implementation.md` §1 of `t6/implementation.md`
  — no new field, so no new coercion here either).
- `garbage α(σ) pl = σ.machines[pl].garbage`; `target`, `gameoverView`,
  `connectedView` likewise — direct field reads, no coercion. All four are
  typed identically on both sides up to the Rocq `ℕ`/Rust `i64` (`garbage`)
  or `usize` (`target`)/`Player`/`bool` correspondence every naming-map
  entry in `implementation.md` §3 already fixes; §12 below discharges the
  one place this typing choice is load-bearing (`garbage` never going
  negative).
- `connected α(σ) pl` — not read off any `Machine<P>` field (none exists —
  `connected`/`messages` are realized entirely in `net.rs`/`session.rs`).
  Realized as: for `pl ≠ Host`, `true` iff the host's own `Peer::connected`
  for that player's slot is still `true` — a flag `Session::check_timeouts`'s
  `Role::Host` branch sets `false` exactly once, on that peer's
  `seconds_since_last_activity()` first exceeding `DISCONNECT_TIMEOUT_SECS`,
  never reset afterward; for `pl = Host`, no Rust quantity represents it at
  all — `connected(Host)` becoming `false` is the host process itself
  ceasing to exist, unobservable to `α` directly (§7 below argues this
  case). `Peer::connected` is the *declared* fact the rest of the system
  observes and acts on — `net.rs`'s own
  `Connection::seconds_since_last_activity`, backed by each connection's own
  `last_activity` timestamp updated on every packet `service_one` receives,
  *is* the detection mechanism, not a proxy for one — leaving one corner
  case accepted as a bounded, harmless divergence rather than closed
  outright — see §7a.
- `messages α(σ) from to` — the concrete in-flight sequence from `from` to
  `to`, realized by `net.rs`'s `ReliableSender`/`ReliableReceiver` pair on
  the one connection carrying that pair's traffic: for `to = Host`, whatever
  `from`'s own `ReliableSender::unacked` map (in `send` order, by sequence
  number) has not yet had its ack processed by `on_ack`; for `to ≠ Host`,
  the same at the host's own relay step (`Session::handle_routed`, which
  calls `self.forward` immediately on a fully-reassembled, in-order delivery
  from `ReliableReceiver::on_packet` — the star topology means every
  non-host-to-non-host path is physically two hops, but `T7.v` models it as
  one queue directly between `from` and `to`; the host relay processes one
  incoming reliable-channel delivery fully, in sequence order, before
  forwarding it onward and accepting the next — matching a single FIFO
  queue's own semantics, a refinement detail rather than an extra invariant
  to carry). `ReliableReceiver::on_packet` (`net.rs`) — per-connection
  sequence number, acked via `TAG_ACK`, retransmitted every
  `RETRANSMIT_INTERVAL` by `ReliableSender::due_retransmits` until acked,
  delivered only up through `next_expected`'s next contiguous run — is
  exactly `T7.v`'s own "no message loss, no duplication, no reordering"
  network axiom (its own header comment), realized rather than
  assumed, subject to the bounded, accepted divergence §8 notes for
  `ReliableSender`'s own `MAX_UNACKED_MESSAGES` eviction.

Well-definedness: `net.rs`'s star topology (one `Connection` per `(pl,
Host)` pair, `Session::new_joiner`/`add_peer`) gives exactly one reliable
channel per such pair, so `connected`/`messages` are total functions of
`σ`, matching `T7.v`'s own totality.

## 4. `move_piece`/`rotate_piece`/`hold_piece`/`rotate_kick_piece`, non-materializing `Fix` — full-use transfer

Each method's guard is `if winner_multi(&self.gameover_view,
&self.connected_view, self.my_index) { return false; }` — a direct
transcription of `WinnerMulti` (`T7.v`'s own definition: the `1 <? PlayerCount`
conjunct is true unconditionally under §2's regime, so the guard reduces to
the `ForallPlayers` clause, which `winner_multi`'s `(0..n).all(...)` loop
realizes cell-for-cell against `playing_view`, itself `PlayingView`
verbatim). When the guard fires, the method touches nothing and returns
`false` — matches `MovePiece`/`RotatePiece`/`HoldPiece`/`RotateKickPiece`'s
`else None` branch exactly. When
it doesn't, each delegates to the identical `self.s6.<method>` call `T6.v`'s
own definition names (`option_map (UpdatePlayer s pl) (T6.<Action> ...)`).
`UpdatePlayer` (`T7.v`'s own definition) touches only `s6` (via the delegated
call) and, conditionally, `gameoverView`'s own `(pl, pl)` cell (`T6.gameover
s6'`, `SelfViewAccurate`'s own coupling — §9 below); every other field
(`garbage`, `target`, `connectedView`, `connected`, `messages`) is
`unchanged` per `UpdatePlayer`'s record literal. `model.rs` writes none of
those fields in any of these four methods — verified by inspection of
`fix_piece`'s own header comment / the method bodies themselves, matching
by construction (disjoint field writes), not a per-field runtime check. A
non-materializing `Fix` (`remGarbage = 0` after `self.s6.fix_piece`) is
covered by §5's collapse argument below, not restated here.

## 5. Materializing `Fix` — no-use, full argument

`self.s6.fix_piece(bag_new)` runs first, unconditionally once the
`winner_multi` guard has passed, computing full `T6` semantics
(score/level/hold/`cleared_lines`/`perfect_clear`/`mg`/`gameover` from the
piece placement alone) — exactly `T6.FixPiece bagNew H2 (s6 s pl)`
(`FixPiece`'s own argument to `option_map`). If it returns `false`,
`fix_piece` returns `false` immediately,
with zero further mutation (`model.rs`'s own early `return false;`) —
matches the `None` case of `T6.FixPiece`'s result under `option_map`.

**Case `remGarbage = 0` (`NoRemGarbage` holds, `T7.v`'s own definition).** Then
`eff_rem` computes to `0` (`rem_garbage.min(hm)` with `rem_garbage = 0`): the
shift/overwrite block does not run. `gameover2` is initialized to
`self.s6.gameover()`, left unmodified by the skipped `if
!gameover2 && rem_garbage > 0` guard (its `rem_garbage > 0` conjunct is
false), then recomputed via the trailing `t1::model::intersect` call
(reached because the `!gameover2` guard immediately before it only skips
this recompute when already `true`). This recompute reads
`self.s6.mg()` — literally the same grid `self.s6.fix_piece` just
produced, untouched by the (skipped) shift — so
`t1::model::intersect(P::forbidden_grid(), ..., self.s6.mg(), 0, 0)`
recomputes exactly the boolean `T1.Correct`'s own forbidden-zone clause
already pins `self.s6.gameover()` to (an invariant of the inherited
`T6`-level state, not argued fresh here — `t1/proofs.md` through
`t6/proofs.md` establish it, only used). So `gameover2 =
self.s6.gameover()` exactly, and the whole block reduces to: `self.garbage
= 0` (matching `FixPiece`'s own `garbage := λ pl2, if pl2=?pl then 0 else
...` field), `self.rem_gen_garbage` set (a read-only bookkeeping field
with no `T7.v` counterpart, harmless — never read by any guard in
`model.rs` itself), `self.gameover_view[self.my_index]` set to the same
value it already held. The target-redirect guard (`self.rem_gen_garbage >
0 && !gameover2`) is exactly `FixPiece`'s own guard on its `target` field
(`(0 <? remGenGarbage)%nat && ! gameover'`) — under
`NoRemGarbage`, `rem_gen_garbage = gen_garbage - garbage` (clamped at 0) is
`0` exactly when `garbage ≥ gen_garbage`, the same condition that forces
`rem_garbage = garbage - gen_garbage = 0`; conversely `rem_garbage = 0 ⟹
gen_garbage ≥ garbage ⟹ rem_gen_garbage = gen_garbage - garbage`, which may
be positive — so `NoRemGarbage` does *not* force this guard shut, and
doesn't need to: `T7.v`'s own branch condition is independent of
`remGarbage`, so this case exercises exactly the same redirect `T7.v`
calls for, covered by §6 below. Net: under `NoRemGarbage`, `fix_piece`'s
only observable effect is `self.s6.fix_piece(bag_new)` plus `garbage := 0`
plus, possibly, the very redirect `T7.v` itself performs — i.e. it *is*
`T6.Next e6 (fₛ pl s7)`, matching `T7RefinesT6`'s own claim rather than
contradicting it (`H4` in `T7RefinesT6`'s statement excludes this call from
*that* proof's obligation via `NoMaterializedGarbage`'s right disjunct
`NoRemGarbage`, which is exactly this case — nothing here needs
re-deriving it).

**Case `remGarbage > 0`.** `T7RefinesT6`'s hypothesis `H4` excludes this
call from the T6-refinement claim entirely — no obligation there. This
file's own obligation (Rust ⊨ `T7.v`) still applies, and is a direct
transcription:

- `eff_rem = rem_garbage.min(hm)` — `T7.v`'s own `Grid` algebra (`FP.Mg'`,
  `FP.CroppedMg'`) crops unboundedly; the array representation
  needs the clamp explicit to keep indices in range. `rem_garbage ≥ hm ⟹
  eff_rem = hm`: `rotate_right(hm)` on an `hm`-length `Vec` is the identity
  permutation of indices, so the following fill loop (`0..hm`) overwrites
  every row — matching total replacement by `GarbageGrid`'s rows once its
  own height reaches or exceeds `hm`.
- **Overflow.** `rem_garbage ≥ hm ⟹ gameover2 = true` unconditionally, no
  scan needed — `T7.v`'s own crop drops the *entire* old `mg` in this
  regime (every row of `mg` sits at a post-shift offset `≥ hm`), so `Mg'
  s pl s6' holes ⊈ CroppedMg' s pl s6' holes` is forced true whenever
  `mg` has any occupied cell (`Gameover'`'s second
  disjunct) — and it always does at this point: this branch only runs
  when `gameover2` is still `false`, i.e. `T6.gameover s6'` is `false`,
  which means `self.s6.fix_piece` just placed the current piece's four
  cells in-bounds (a piece intersecting the forbidden zone would already
  have set `gameover` true, short-circuiting this branch via the `if
  !gameover2` guard) — those four cells are themselves occupied cells of
  `mg`, so `mg` is never all-empty here regardless of what was on the
  board before this fix. When `rem_garbage < hm`, the overflow scan (`(hm -
  rem_garbage..hm).any(...)`) reads rows `[hm - rem_garbage, hm)` of
  `self.s6.mg()` **before** the shift/overwrite block below mutates it
  (Rust statement order: the `if !gameover2 && rem_garbage > 0`
  block runs, and is fully evaluated, before the `if eff_rem > 0` block
  that mutates `mg`) — these are exactly the rows `T7.v`'s `mg ⊕
  (remGarbage, 0)` (`Grid` translation) pushes to `y ≥ hm`, i.e. exactly
  the rows `Full mg`'s crop drops. `mg' ⊈ croppedMg'` iff one of them is
  occupied, which is what the `.is_some()` scan tests cell-by-cell. Same
  value, same rows.
- **Shift/overwrite**: `self.s6.mg_mut().rotate_right(eff_rem as usize)`
  moves the `Vec`'s last `eff_rem` rows (indices `[hm - eff_rem, hm)`) to
  the front, sliding every other row up by `eff_rem` positions — old row
  `i` (for `i < hm - eff_rem`) lands at new index `i + eff_rem`, and the
  `eff_rem` rows now sitting at `[0, eff_rem)` hold whichever old rows used
  to occupy `[hm - eff_rem, hm)` (already accounted for by the overflow
  scan above, which read them *before* this call, and are about to be
  overwritten regardless — `rotate_right` moves `Vec` element handles,
  allocating nothing, so nothing is cloned only to be immediately
  discarded). This *is* `mg ⊕ (remGarbage, 0)`: every surviving old row
  ends up at exactly the index `T7.v`'s shift-by-`remGarbage` places it at,
  and no old row's content bleeds into any other index (a rotation is a
  bijection on indices). The following loop then overwrites rows `[0,
  eff_rem)` in place via `fill_garbage_row::<P>(&mut
  self.s6.mg_mut()[y as usize], holes(y))` — `T7.v`'s `GarbageGrid
  remGarbage holes (W InitialMainGrid)`, one row of occupied cells except
  the hole column (`fill_garbage_row`'s own `assert!` realizes
  `ValidHoles` per call), realized directly for the array
  (no intermediate `Grid` record, `implementation.md` §5) instead of via
  the `Grid`-algebra union `T7.v` uses; the union's semantics (row `y <
  remGarbage ↦` `GarbageGrid`'s content, row `y ≥ remGarbage ↦` shifted
  `mg`) is exactly what the rotation followed by this in-place fill
  realizes over disjoint row ranges, so no cell is written twice and none
  is left unwritten within `[0, hm)`.
  The trailing `self.s6.update_shadow_y()` call *does* have a `T7.v`
  counterpart: `FixPiece`'s materialization branch passes
  `FP.CroppedMg' s pl s6' holes` to `NewMainGridGameoverState`, which
  itself calls `T5.UpdateShadowY` to recompute `gy`
  against the new grid — exactly the refresh `self.s6.update_shadow_y()`
  performs here, for the same reason (`gy` was computed by the piece
  placement alone and is stale once garbage rows are spliced in). Not a
  new argument: `t5/proofs.md`'s own `gy`-refresh obligation already
  covers `t5::model::Machine::update_shadow_y`'s correctness; this call
  site is one more place that obligation discharges.
- **Forbidden-zone recheck** (short-circuited when `gameover2` is already
  `true`, per the `if !gameover2` guard immediately before the
  `t1::model::intersect` call) is the third disjunct of `T7.v`'s
  `Gameover'` (its own `ForbiddenGrid ∩ croppedMg' ⊈ ∅` disjunct), evaluated on
  the same post-shift `self.s6.mg()` that *is* `CroppedMg'` by
  construction (every write in the shift/overwrite step stays within `[0,
  hm)` — the array never grows past it, so cropping is free, matching
  `implementation.md` §4-T7c's own note that no explicit crop step is
  needed). Boolean `||` across the three disjuncts (`T6.gameover s6'`'s
  initial value, overflow, this recheck — `T7.v`'s `Gameover'`) is realized
  by the two guarded reassignments of `gameover2` in
  sequence, each a no-op once `gameover2` is already `true` — the same
  short-circuit `T7.v`'s own pure-boolean `||` permits regardless of
  evaluation order (Rust's is an optimization here, not a semantic
  difference, since neither guard has a side effect the other depends on).
- `self.garbage = 0`, `self.gameover_view[self.my_index] = gameover2` —
  `FixPiece`'s own `garbage`/`gameoverView` fields, cell for cell.
- **Redirect**: guard and computation both match `FixPiece`'s own `target`
  field exactly, `FP.PlayingView'` realized identically by the closure passed to
  `next_target` (`playing_view(&self.gameover_view, &self.connected_view,
  pl2)`, read *after* `self.gameover_view[self.my_index]` was just
  updated — matching `T7.v`'s own `gameoverView'` (`FP.GameoverView'`),
  which folds in the same just-written self-cell before `NextTarget`
  reads it, in `FixPiece`'s own redirect). §6's termination-lemma "case 2" (used generically,
  not re-derived per call site) confirms this call site never needs the
  `from ↦ true`-style override `redirect_target_from` carries: the search
  here starts at `target s pl` itself, a player whose own liveness *this*
  call cannot have changed (`pl ≠ target(pl)` by `TargetNotSelf`, so the
  one cell this call can move — `(pl, pl)` — is not the one being
  searched), so the wraparound candidate is provably still
  `PlayingView`-true without any forced override — `next_target`'s own
  `pl2 != self_` exclusion of `self.my_index` as a candidate (the comment
  `fix_piece`'s own body carries at this call site) is exactly this, and
  `T7.v` uses no override at its own corresponding call site either
  (`FP.PlayingView'` unmodified).

## 6. `next_target` termination lemma

Used by §5 (`fix_piece`'s own redirect) and §8
(`receive_gameover`/`receive_disconnect`, via `redirect_target_from`).
`next_target`'s only fallback is the loop completing all `player_count`
iterations without a hit, returning `self_` (`NextTargetAux`'s `fuel = 0`
case) — every use of `next_target` in `model.rs` must
never actually need this fallback while `Correct s7` holds and `NoWinner`
holds at the relevant post-state, or the Rust/spec field values would
diverge at a point the invariants are meant to prevent (they may still hit
the fallback when `NoWinner` fails — that is the winner case, and is
correct, per `model_unit_test.rs`'s own
`receive_gameover_redirects_target_round_robin` test).

**Claim.** For every reachable `s7` with `Correct s7` and `NoWinner s7'` at
the post-state `s7'` of the call in question, some candidate distinct from
`self_` and from the search's starting point is found strictly before the
search would need to wrap fully around.

**Proof.** A property of `T7.v` itself, independent of which realization
calls into it. `MessageSound`/the branch guard gives: the player the search is
walking away from (`from`, for §8's call sites) is truly not-playing
post-update (`gameover s from = true` or `connected s from = false`, hence
`Playing s' from = false`). `ViewSound`'s two clauses, read
contrapositively, give: any player truly playing at `s'` is
`PlayingView`-true to `pl` at `s'` (a view can lag calling someone dead
who's alive — never the reverse). `NoWinner s'` supplies two distinct
truly-playing players; at most one can be `pl` herself (excluded from
candidacy by `next_target`'s own `cur != self_` check), so at least one
genuine candidate `Y ≠ pl` exists and is `PlayingView`-true.
`NextTargetAux`'s walk visits every other player exactly once, in cyclic
order (`PlayerCyclicPermutation`), before it could ever revisit the walk's
own starting point — so `Y` is found at some step strictly before the
wraparound. ∎

**Two call sites, two conclusions**, realized here by the two Rust call
sites:

1. `redirect_target_from` (§8): the walk starts at `from`, the very player
   whose status just became "not playing." `T7.v`'s `FP.PlayingView'`/
   `ReceiveMessage`'s own `view'` closures both force `view'(from) = true`
   in the wraparound-avoidance sense used above — reversed as `false` in
   this repo's own naming (`redirect_target_from`'s closure returns
   `false` at `pl2 == from`, since it is searching *away from* `from`,
   the opposite framing from `T7.v`'s `FP.PlayingView'` computed inside
   `fix_piece` — see §8 for why the two closures' `from`-handling differ
   in this exact way while realizing the same underlying fact). The
   override matters exactly when `NoWinner s'` fails: without it, the walk
   would reach the wraparound point with the *stale* pre-update view of
   `from` (still "playing," since `self.gameover_view[from]`/
   `self.connected_view[from]` have not yet been written when
   `redirect_target_from` runs — `receive_gameover`/`receive_disconnect`
   call it *before* the corresponding field write, `implementation.md`
   §4-T7e′) and could return `from` again — a value `T7.v`'s own
   computation (using the *already-updated* `gameoverView'`) would not
   produce in the same edge case. The override closes exactly this gap;
   §11's field-level argument in §8 confirms the two are equivalent once
   the deferred write actually lands, which happens unconditionally,
   immediately after `redirect_target_from` returns.
2. `fix_piece`'s own redirect (§5): the walk starts at `target s pl`, a
   player whose liveness *this* call cannot have changed (the only cell
   `fix_piece` can move is `(pl, pl)`, and `target(pl) ≠ pl` by
   `TargetNotSelf`). So the wraparound candidate, `target s pl` itself, is
   provably still `PlayingView`-true regardless of whether `NoWinner s'`
   holds — no override is needed here, and `T7.v` uses none at this call
   site either (`FP.PlayingView'` unmodified).

## 7. `drop_piece` — no-use relocation, then §5 in full

The `winner_multi` guard runs **before** the relocation
(`t1::model::new_piece_yx_state`) — `implementation.md` §4-T7h's own
required deviation from `T7.v`'s literal shape: `T7.v`'s own `DropPiece`
has no guard of its own, because `NewPieceYXState` produces a fresh,
discardable Rocq value — a `WinnerMulti` player's relocation, followed by
`FixPiece`'s own internal guard rejecting the fix, simply yields `None`
overall with nothing ever observably mutated (Rocq state is immutable).
Rust's `t1::model::new_piece_yx_state` mutates `self.s6`'s own `py`/`px` in
place; without the explicit guard *before* that call, a `WinnerMulti`
player's relocation would commit and never be undone, even though the
trailing `fix_piece` call correctly rejects — the same category of
sequential-mutation-where-Rocq-has-a-single-simultaneous-step pitfall
`rotate_kick_piece` (`t6/proofs.md`) already had to account for one layer
down, surfacing one call deeper here. `model_unit_test.rs`'s own
`drop_piece_winner_multi_guard_leaves_state_untouched` is the operational
check for exactly this. Given the guard passes: the relocation itself
(`t1::model::new_piece_yx_state::<P>(gy, px, self.s6.s1_mut())`) is `T1.
NewPieceYXState (gy s pl, px s pl) pl s` wrapped in `UnchangedT7Part`
(nothing outside `s6` moves), touching only
`py`/`px` per that function's own spec (`t1::model::new_piece_yx_state`'s
own doc comment: "mg, p, pr, gameover, cleared_lines unchanged"). The
trailing `self.fix_piece(bag_new, holes)` call is `T7`'s own `fix_piece`,
not `self.s6.fix_piece`/`self.s6.drop_piece` — so garbage generation/
cancellation/materialization/redirect is not bypassed on a hard drop
(`model.rs`'s own comment: "re-checks winner_multi, harmlessly
redundant") — and is covered by §5 in full, no new argument needed
(`T7.v`'s own `DropPiece`, composing `FixPiece pl holes H1 bagNew H2
(NewPieceYXState ...)`).

## 7a. `FixPiece`'s own `connected s pl` gate — bounded divergence, not an exact match

A bounded, harmless divergence, argued directly against `session.rs`'s
actual code. `T7.v`'s own `FixPiece` gates `SendMessages` on `connected s pl`
(its own `messages` field) — the *acting* player's own connectivity, as tracked by the
network layer's ground truth, not `model.rs`. `model.rs` itself has no such
gate at all (`fix_piece` leaves `self.rem_gen_garbage` and
`self.gameover_view[self.my_index]` for the caller to read after the call
and act on, unconditionally); `Session::broadcast_after_fix` (called from
`fire_and_broadcast` right after every fixing call) likewise has no such
gate — it calls `self.send_routed`/`send_routed_from` unconditionally once
`rem_gen_garbage > 0 && pre_target != me` (or `now_gameover &&
!was_gameover`), which in turn calls `conn.outgoing.send(...)` on whatever
`Peer`/`Connection` it finds, without first checking that channel's own
liveness. For `pl = Host`: trivially satisfied, since the host's own
`connected` never meaningfully flips `false` within a live trace under this
file's scope (§7's own move: the host process dying ends the trace rather
than appearing as a mid-trace state). For `pl ≠ Host`: a genuine corner case survives — `pl`'s own
reliable channel to the host can go bad before the host's own
`check_timeouts`-based detection has caught up (α's `connected(pl)`, §3, is
the host's own *declared* `Peer::connected` fact, not `pl`'s own immediate
knowledge of her own link), so a trace exists where `T7.v`'s `FixPiece`
computes a `messages'` with a new entry appended (because α still says
`connected(pl) = true`) while the underlying UDP send from `pl`'s own
`service_one` call (`net.rs`) never reaches the host at all. This cannot be
closed by `pl` sending fast — `pl` has no way to observe the host's own
`Peer::connected` flag before deciding whether to attempt the send, and the
host-driven half of `DisconnectPlayer pl≠Host`'s own effect
(`Session::check_timeouts`'s broadcast) is realizable only by the host,
never by `pl` herself (§10). **Harmless:** neither `MessageSound` nor `LastMessagesGameoverDisconnect`
(`T7.v`'s only invariants mentioning `messages`) requires a message to be
*present* — both only constrain its *content* when one is. A message
`T7.v` would have appended, but that `pl`'s own already-dead channel drops
before the host has caught up, violates no conjunct of `Correct`; nothing
in this file's own safety scope (§1) is sensitive to the omission.
Liveness (a genuinely-sent `GarbageMessage`/`GameoverMessage` eventually
being *acted on*) is out of scope regardless.

## 8. `receive_garbage`/`receive_gameover`/`receive_disconnect` — cross-machine argument

Each realizes one `Receive` event: a queue pop between exactly one `(from,
pl)` pair (`ReceiveMessage`'s own definition). In-order, step-by-step — `messages from
to`'s FIFO shape (`LastMessagesGameoverDisconnect`) exists precisely so
"not yet delivered" *is* the queue; there is nothing left to reorder once
`α` is defined per §3.

- **Enqueued exactly once, by exactly one action.** A `GarbageMessage`/
  `GameoverMessage` is appended only inside `SendMessages`, called only
  from `FixPiece`, only when
  `connected s pl` (§7a) — realized as `Session::broadcast_after_fix`
  reading `machine.rem_gen_garbage` (via `take_rem_gen_garbage`, which
  reads-and-clears in one step) and
  `machine.gameover_view[machine.my_index]` exactly once per successful
  `fix_piece`/`fall_step`/`drop_piece` call (`Session::fire_and_broadcast`
  wraps each individual fixing call, sampling `was_gameover`/`pre_target`
  fresh each time, never batched across a frame) and pushing the
  corresponding `Payload` into `Connection::outgoing`, from which
  `service_one` assigns it the next sequence number via
  `ReliableSender::send` — one push, hence one sequence-numbered send, per
  one successful `T7.v` `FixPiece` step, matching one Rocq append per step,
  since `rem_gen_garbage`/`gameover_view[my_index]` are themselves written
  exactly once per `fix_piece` call (§5). A `DisconnectMessage` is appended
  only inside `DisconnectPlayer`, only for `pl ≠ Host` (its own `messages`
  field's guard) —
  realized by the host's own single detection-and-broadcast for that
  connection (`Session::check_timeouts`'s `Role::Host` branch,
  timeout-driven, `send_routed_from(pl, Broadcast, Payload::Disconnect)`),
  guarded by that same branch's own `!self.peers[slot].connected` check so a
  repeat firing is already excluded before any send is attempted —
  matching `DisconnectPlayer`'s own guard (`if connected s pl then ... else
  None`): once `connected s pl` flips `false`, a repeat event is excluded
  at the Rocq level too, and `Peer::connected` is exactly the Rust-side
  realization of that same fact (no other place `connected`'s Rust-side
  truth, §3, could un-flip). One case not present at the Rocq-event level
  at all: the host's own copy of this fact is applied synchronously, in
  the same `check_timeouts` iteration, rather than via a queued
  self-message — argued separately in §10.
- **Dequeued in order, exactly the message that was enqueued first.**
  `ReliableReceiver::on_packet` (`net.rs`) — sequence number, ack via
  `TAG_ACK`, retransmit via `ReliableSender::due_retransmits`, deliver only
  up through `next_expected`'s next contiguous run — is built to realize
  FIFO delivery directly: `service_one`'s receive branch processes one
  fully-reassembled, in-order `WireMessage` at a time, pushing it to
  `ConnState::event_tx`, an `mpsc::Sender` whose receiver end
  (`Connection::incoming`) `Session::pump` drains with `try_recv()` in a
  single pass per frame, itself FIFO — so `receive_garbage`/
  `receive_gameover`/`receive_disconnect` (reached via
  `Session::apply_local`, called from `Session::handle_routed`) are invoked
  with precisely that message's own payload, in send order, never a stale
  or reordered one. One accepted, bounded divergence: `ReliableSender::send`'s
  own `MAX_UNACKED_MESSAGES` eviction (`net.rs`) drops the single oldest
  unacked entry once a connection accumulates 1024 outstanding sends, and
  an evicted message is never retransmitted again — if it was genuinely in
  flight, `ReliableReceiver::next_expected` on the far end can then never
  advance past the resulting gap, and every later reliable message on that
  connection sits in `ReliableReceiver::pending` (or is silently dropped
  once it falls outside `MAX_REORDER_WINDOW`) rather than ever reaching
  `apply_local`. `net.rs`'s own doc comment on `ReliableSender::send`
  accepts this outright: reaching the cap requires ~1024 distinct reliable
  sends on one connection, which this app's own low-volume traffic
  (lobby/`Garbage`/`Gameover`/`Disconnect`/`Hello`/`Ping`) cannot produce
  against a peer that is not already thoroughly unresponsive — at which
  point `DISCONNECT_TIMEOUT_SECS` has independently already fired.
  `MessageSound`/`LastMessagesGameoverDisconnect` are not violated by a
  message that never arrives (same reasoning §7a already gives for a
  message that is never sent); only *reordering* or *duplication* of a
  delivered message would violate `T7.v`'s network axiom, and eviction
  produces neither.
- **The queue only shrinks, never grows, independent of other players'
  concurrent steps.** `messages s' from to` (`T7.v`'s pattern `m :: rest ↦
  rest`, `ReceiveMessage`'s `messages'`) shrinks by exactly the popped
  message, for the one `(from, to)` pair addressed — every other pair's
  queue is `messages s` unchanged (all three of `ReceiveMessage`'s own
  branches). `net.rs` realizes this the same way: each `ConnState` owns its
  own independent `ReliableSender`/`ReliableReceiver` and its own `mpsc`
  channel pair, and `worker_loop`'s round-robin (`service_one` called once
  per registered connection per outer iteration) processes one connection's
  incoming socket read fully before moving to the next, so processing one
  connection's own incoming message never touches another connection's
  buffer. This is `OtherS6Unchanged`'s counterpart for the network layer —
  needed so this argument doesn't have to account for interleaving with
  unrelated players' own steps.
- **Field-level match, each branch:**
  - `receive_garbage(amount)`: `self.garbage += amount` ≙ `garbage := λ
    pl2, if pl2=?pl then garbage s pl2 + n else garbage s pl2`
    (`ReceiveMessage`'s own `GarbageMessage` branch) — no `from` needed on
    either side (sender-agnostic `+=`,
    matching `T7.v`'s own branch, which never reads `from` either). No
    other field moves, either side. §11 discharges the `i64` range
    argument this relies on.
  - `receive_gameover(from)`: `self.gameover_view[from] = true` ≙ the
    `(pl, from)` cell of `gameoverView` (`ReceiveMessage`'s own
    `GameoverMessage` branch: `obs =? pl && obsd =? from`); redirect guard
    and computation covered by §6 case 1. No other field moves (`s6`,
    `garbage`, `connectedView` all pass through unchanged both sides, per
    that same branch's own record literal). One
    ordering note: `model.rs`'s
    `receive_gameover` computes the redirect (via
    `redirect_target_from`, reading the *pre-update* `gameover_view`)
    **before** writing `self.gameover_view[from] = true`, whereas `T7.v`
    computes `target`/`gameoverView`'s two cells as simultaneous updates
    from the same pre-state (`ReceiveMessage`'s single `let ... in ...
    Some {| ... |}` — both fields read the *same* `s`, one Rocq step).
    `redirect_target_from`'s own `pl2 == from ↦ false` override (§6 case
    1) is exactly what reconciles this sequencing difference: it forces
    the search to treat `from` as not-playing *before* the field write
    that would otherwise establish that fact, so the Rust two-step
    sequence (redirect first, field write second) computes the identical
    result the Rocq one-step simultaneous update does. Without the
    override, this specific ordering choice would be the divergence;
    with it, the two are equal by construction, not merely by
    coincidence of this file's own reachable states.
  - `receive_disconnect(from)`: `self.connected_view[from] = false` ≙ the
    `(pl, from)` cell of `connectedView` (`ReceiveMessage`'s own
    `DisconnectMessage` branch, same shape as
    `receive_gameover`'s `gameoverView` cell); redirect present on both
    sides, covered by §6 case 1 and the same ordering note as above,
    identically.

## 9. `notice_disconnection` — stutter w.r.t. `s6`, single-machine

`self.connected_view[self.my_index] = false` ≙ the `(pl, pl)` cell of
`connectedView` (`NoticeDisconnection`'s own record literal) — no other
field moves, either side. `T7.v`'s own guard has two conjuncts
(`! connected s pl && connectedView s pl pl`); `model.rs`'s own method
checks only the second
(`if !self.connected_view[self.my_index] { return false; }`) — the first
(`¬connected s pl`) is the caller's responsibility: `Session::check_timeouts`'s
`Role::Joiner` branch calls `m.notice_disconnection()` only once
`self.peers.first()`'s `seconds_since_last_activity() >
DISCONNECT_TIMEOUT_SECS` (its own link to the host, since a joiner has
exactly one connection), guarded by `!self.noticed_disconnect` so the call
site itself never repeats — which *is* the trigger condition for
`¬connected s pl` becoming true from `pl`'s own local vantage, not
something `model.rs` needs to reconstruct. The second conjunct (`hasn't
already noticed`) *is* checked inside `model.rs` too, making the method
idempotent by construction independent of the caller's own guard
(`model_unit_test.rs`'s own `notice_disconnection_idempotent` is the
operational check) — stronger than `T7.v`'s own guard requires (a
repeat call there would simply be `None`, a stutter; `model.rs` returns
`false` for the identical reason, rather than mutating a `false` to
`false`).

## 10. `Disconnect`

- **`pl = Host` — realized by nobody's `Machine<P>` or `Session`/`net.rs`
  logic.** `DisconnectPlayer`'s effect when `pl = Host` sets `connected'
  pl1 = false` for *every* `pl1` at once (its own `connected` field: the
  `pl =? Host` disjunct makes the guard unconditionally `false`) — "if the host is
  disconnected, everyone is." No Rust code realizes this as a step: the
  host process ceasing to exist *is* the fact `connected := λ _, false`
  becomes true of `α σ` at the next real step any surviving player takes —
  every other player's own `notice_disconnection` (§9) observes this
  indirectly, once its own `Connection::seconds_since_last_activity()`
  timeout to the host fires in that player's own `check_timeouts`'s
  `Role::Joiner` branch, but that firing is `NoticeDisconnection`, a
  separate `T7.v` event with its own argument (§9), not a re-derivation of
  `DisconnectPlayer(Host)` itself.
- **`pl ≠ Host` — realized by the host's own `Session::check_timeouts`**,
  never by any `Machine<P>`. On detecting, in its `Role::Host` branch, that
  `self.peers[slot].conn.seconds_since_last_activity() >
  DISCONNECT_TIMEOUT_SECS`, the host — as the relay for every other joiner
  — sets `self.peers[slot].connected = false` (once; the branch's own
  guard skips an already-`false` entry) and calls
  `self.send_routed_from(pl, Destination::Broadcast, Payload::Disconnect)`,
  which reaches every other connected peer over their own reliable channel
  (`send_routed_from`'s own `Role::Host` arm iterates `self.peers`, sending
  to each with `to.reaches(idx)` true and `p.connected` — every peer but
  the one that just dropped, since `self.peers` never holds "myself" as
  one of its own entries). This reproduces `DisconnectPlayer pl`'s two
  field changes directly: `connected` — only `pl`'s own entry flips
  (`DisconnectPlayer`'s own `connected' pl1 = if pl1 =? pl then false else
  connected s pl1`, since the `pl =? Host` disjunct is false), realized as
  `Peer::connected := false` for that one slot, §3's `connected α(σ)`
  reading it becoming permanently `false` for `pl`, unaffected for anyone
  else; `messages` — `DisconnectMessage` appended from `pl` to every `to ≠
  pl` (`DisconnectPlayer`'s own `messages` field), realized as one
  `Payload::Disconnect` push per recipient's own outbound reliable channel
  (`send_routed_from`'s per-peer loop), matching one append per `(pl, to)`
  pair for every connected `to ≠ pl`.
- **The host's own copy: `receive_disconnect(pl)` applied synchronously,
  not via a queued self-message.** `DisconnectPlayer`'s own record literal
  appends a `DisconnectMessage` from `pl` to *every*
  `to ≠ pl`, `to = Host` included (`pl ≠ Host` in this branch) — so `T7.v`
  models the host's own updated view of `pl` as arriving through the same
  queue-and-`ReceiveMessage` mechanism §8 argues for every other recipient,
  one further, logically separate step (`Next Host (Receive pl) s`). The
  same `check_timeouts` branch instead calls `m.receive_disconnect(pl)`
  directly on the host's own `Machine`, in the same real action as the
  broadcast above, rather than pushing a message to itself and later
  draining it back out of its own queue. This collapses two `T7.v` steps
  (`DisconnectPlayer pl`, then `ReceiveMessage Host pl`) into one Rust
  action — sound exactly because nothing else can observably occur between
  them: `DisconnectPlayer`'s own effect on every field but `(from = pl, to
  = Host)`'s queue entry is already fully applied before `ReceiveMessage
  Host pl` would run (no other player's step can touch `pl`'s or the
  host's own `s6`/`garbage`/`target`/view fields in between,
  `OtherS6Unchanged`/§11), and `ReceiveMessage`'s own `DisconnectMessage`
  branch reads only the message's `from` (`= pl`, fixed) and the
  pre-existing `gameoverView`/`connectedView`/`target` state
  `DisconnectPlayer` did not touch — so computing it immediately, from the
  state `DisconnectPlayer` just produced, yields the identical result
  computing it from any later state would (no other host-side event can
  fire strictly between these two Rocq steps in any trace this file's
  scope covers). `receive_disconnect`'s own redirect argument (§6 case 1)
  applies to this call site exactly as it does to the one reached via
  `apply_local` for every other player — it is one more instance of that
  generic argument, not a new case.

## 11. Representation invariant — `Correct`, by induction

Base case, `Init` (`T7.v`'s own definition) vs. `Machine::new`: `s6Init pl` ≙
`t6::model::Machine::new(bags_fn, piece_source)`, inherited `T6.Correct`
(not re-derived, `t5::model::check_invariants`'s own conjuncts); `garbage =
0`, `target = (my_index + 1) % player_count` ≙ `PlayerNext`. `gameoverView`
— `T7.v`'s `Init` sets the `(obs, obs)` diagonal to `T6.gameover (s6Init
obs)` and everything else `false` — `Machine::new` fills the
whole `Vec<bool>` `false` then overwrites only its own index
(`gameover_view[my_index] = s6.gameover()`) — each `Machine<P>`
instance only ever holds *its own* view (`implementation.md` §0.2), so the
array it stores realizes exactly the `obs = my_index` row of `T7.v`'s
two-argument function, `false` off-diagonal and `T6.gameover` on it —
matching. `connectedView` — all `true` ≙ `PlayerCount >? 1`, always `true`
under §2's regime (enforced by `Machine::new`'s own `assert!(player_count >
1)`). `SelfViewAccurate` (by the constructor's own `gameover_view[my_index]`
assignment, matching `check_invariants`'s own `SelfViewAccurate` conjunct
— `implementation.md` §6.10) and `TargetPlaying`/`TargetNotSelf` (vacuous
at `Init`, `NoWinner` holds since every real player starts alive and
connected) all hold immediately.

Inductive step, one clause per method (`t7::model::Machine<P>`'s own
public API — no other code path mutates a `Machine<P>`):

- **`OtherS6Unchanged`.** Every method above writes `self.s6` only on the
  receiver `self` — no method takes a second `&mut Machine<P>` or reaches
  into another player's fields; every cross-player effect goes through
  `receive_garbage`/`receive_gameover`/`receive_disconnect`/
  `notice_disconnection` (§8–§9), none of which touch `self.s6` at all
  (grep-verifiable: `self.s6` does not appear in any of the four bodies).
  Matches `T7.v`'s own shape (every action's record literal sets `s6 :=
  λ pl2, if pl2=?pl then s6' else s6 s pl2`).
- **`GameoverMonotone`/`GameoverViewMonotone`.** `self.s6.gameover()` only
  ever moves `false → true` (inherited monotonicity from `t1/proofs.md`
  through `t6/proofs.md`, not re-derived here); `gameover_view[i]` is only
  ever *set* to `true` (`receive_gameover`) or to `self.s6.gameover()`'s
  current value at the owner's own index (`fix_piece`) — the latter can
  only move `false → true` by the former fact (inherited monotonicity),
  never back. No method sets any `gameover_view` cell to `false`
  (grep-verifiable: `gameover_view[` is assigned in exactly two places in
  `model.rs`, both cited above).
- **`DisconnectedMonotone`/`DisconnectedViewMonotone`.** `connected`'s
  Rust-side realization (`Peer::connected`, §10) is set-once, never
  cleared, for the lifetime of a match — `Session::init_machine` (called
  from `start_match`, once per `Start`) is the only place a new roster
  begins, never a step within one run. `connected_view[i]` is only ever
  set to `false` (`notice_disconnection`, `receive_disconnect`), never
  back to `true` (same grep argument as above).
- **`SelfViewAccurate`.** The one place `self.s6.gameover()` can newly
  become `true` is inside a successful `self.s6.<method>` call; every
  method that can trigger this (`move_piece`/`rotate_piece`/`hold_piece`/
  `rotate_kick_piece`/`fix_piece`, via `T6`'s own logic) is immediately
  followed, in the same call, by `self.gameover_view[self.my_index]` being
  read-through-accurate: explicit in `fix_piece`
  (`self.gameover_view[self.my_index] = gameover2;`, the exact value
  `self.s6.gameover()` was just set to); for the other four, no explicit
  write exists because none of them can flip `self.s6.gameover()` at all
  from `false` to `true` without going through `T6`'s own `fix_piece`
  path — `move_piece`/`rotate_piece`/`hold_piece`/`rotate_kick_piece`
  never set `gameover` (inherited from `t1`–`t6`: only `fix_piece`'s own
  `intersect(forbidden_grid, ...)` recompute ever does). So
  `check_invariants`'s own assertion (`gameover_view[my_index] ==
  s6.gameover()`, its own `SelfViewAccurate` conjunct) is preserved by
  every method: the four delegating ones because the compared value never
  moves under them, `fix_piece` because it writes both in the same call.
- **`TargetNotSelf`/`TargetPlaying`.** Preserved trivially by every method
  that doesn't touch `target` (nothing relevant changes). For the two that
  do (`fix_piece`'s own redirect, `receive_gameover`/
  `receive_disconnect`'s via `redirect_target_from`), §6 establishes both:
  under `NoWinner` at the post-state, a genuine candidate `≠ self_` is
  always found before any wraparound, so the result is never `self_`
  (`TargetNotSelf`) and is always `PlayingView`-true at the post-state by
  construction of the search (`TargetPlaying`) — argued per call site in
  §5 and §6/§8 respectively, not restated here.
- **`ViewSound`/`MessageSound`/`NoSelfMessage`/
  `LastMessagesGameoverDisconnect`.** Properties of the network/message
  layer (§3), preserved by `session.rs`'s/`net.rs`'s actual code (§7a/§8/
  §10): a `GameoverMessage`/`DisconnectMessage` is only ever enqueued at
  the same step the corresponding truth (`gameover`/`connected`) becomes
  false→true/won't-revert — never before: `Session::broadcast_after_fix`
  reads `machine.gameover_view[machine.my_index]` *after* the `fix_piece`
  call that may have just set it, and `Session::check_timeouts`'s
  `Role::Host` branch sets `Peer::connected = false` at the same point
  that triggers the broadcast, never earlier — and `SendMessages`'s own
  `to =? pl` self-exclusion is realized by
  `Session::send_routed_from` never addressing an outbound message to its
  own connection (there is no connection from a peer to itself — `self.peers`
  holds only *other* players, §15.1's star topology) and by
  `handle_routed`'s own `Some(from) != self.my_index` check before ever
  calling `apply_local`, excluding a self-addressed broadcast from being
  applied to its own sender even if one somehow arrived — realizing
  `NoSelfMessage`.

## 12. Integer-range soundness

`garbage`/`rem_gen_garbage` are `i64` (`implementation.md` §6.1's own
naming-map choice), not a saturating or checked type — a real, if narrow,
divergence from `T7.v`'s own `garbage : Player → ℕ`, exact and unbounded.
`receive_garbage(&mut self, amount: i64)` computes `self.garbage +=
amount` with plain wrapping-on-overflow `i64` arithmetic in a `--release`
build (a debug build panics instead, via Rust's own debug-assertions
overflow check). This file does not accept silent wraparound as a
bounded-and-harmless divergence; it argues instead that overflow is
*unreachable*: `amount` is small, and `garbage` is drained to `0` on every
one of `pl`'s own subsequent materializing fixes (`generated_garbage`'s own
range — bounded above by `HM + 10`, since `GeneratedGarbage`'s
`NormalGarbage` clause never exceeds `clearedLines ≤ HM` and
`SpecialGarbage` is a fixed `10` — is the only source of a
`receive_garbage` `amount`, `implementation.md` §15.4's own relay reads it
straight from `rem_gen_garbage` with no further scaling). `check_invariants`
asserts `s.garbage >= 0` (`implementation.md` §6.10) but not an upper
bound — this file accepts that as sufficient given the argued-unreachable
overflow; the risk here is overflow panic/wrap, not precision loss, and the
same boundedness argument closes it.

**Receive-side clamp.** `Session::apply_local`'s `Payload::Garbage` arm
additionally clamps the wire-received `amount` to `[0, hm]`
(`amount.clamp(0, hm)`) before calling `receive_garbage` — hardening beyond
`T7.v`'s own `garbage : Player → ℕ`, which is exact and unbounded, and
beyond `ReceiveMessage`'s own unconditional `garbage[pl] += n`. This is a
real, but provably harmless, divergence: `fix_piece`'s own materialization
already clamps `eff_rem = rem_garbage.min(hm)` before ever touching the
array (§5), so any `garbage` value `≥ hm` produces the identical observable
outcome (total board wipe, `gameover2 = true`) as `garbage = hm` exactly
would — clamping the *stored* value earlier changes no later observable
step, and a negative `amount` (never legitimately produced by
`GeneratedGarbage`/`GenRemGarbage`, whose range is `[0, HM + 10]`, but
reachable here only from a malicious or corrupted peer, since `amount`
crosses the wire) would otherwise violate `check_invariants`'s own
`garbage >= 0` assertion were `CHECK_INVARIANTS` ever compiled on.

## 13. Summary

| method | argument |
|---|---|
| `move_piece`/`rotate_piece`/`hold_piece`/`rotate_kick_piece` | full-use transfer (§4) |
| `fix_piece`, `remGarbage = 0` | collapses to `self.s6.fix_piece` exactly (§5) |
| `fix_piece`, `remGarbage > 0` | no-use, full transcription of materialization (`rotate_right` + `fill_garbage_row`) + redirect (§5), redirect soundness via §6 case 2 |
| `fall_step` | disjoint-guard sequencing over `move_piece`/`fix_piece`, both above |
| `drop_piece` | no-use relocation, guarded before mutation (§4-T7h) + §5 in full (§7) |
| `receive_garbage`/`receive_gameover`/`receive_disconnect` | cross-machine, message-queue argument against `Session`/`net.rs` (§8), redirect soundness via §6 case 1, ordering reconciled by `redirect_target_from`'s override |
| `notice_disconnection` | stutter w.r.t. `s6`, `Session::check_timeouts`-detected trigger, idempotent by construction (§9) |
| `Disconnect`, `pl = Host` | realized by nobody — argued against reality (§10) |
| `Disconnect`, `pl ≠ Host` | realized by `Session::check_timeouts`'s own broadcast, plus the host's own synchronous self-`receive_disconnect` (a step-collapsing move, argued explicitly) (§10) |
| `Correct` | inductive, one clause per method (§11) |
| `garbage`/`rem_gen_garbage`'s range | `i64`, unclamped; overflow argued unreachable; the wire-receive clamp is a harmless, separate hardening (§12) |
| `fix_piece`'s outer `connected s pl` message gate | bounded, invariant-harmless divergence — not an exact match, argued against `Session::broadcast_after_fix` (§7a) |
| `ReliableSender`'s `MAX_UNACKED_MESSAGES` eviction | bounded, invariant-harmless divergence under an unreachable-in-practice precondition (§8) |
| `PlayerCount = 1` | out of scope — discharged by `t6/proofs.md` directly, never constructed here (§2) |
