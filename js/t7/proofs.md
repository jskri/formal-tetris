# proofs.md — refinement proof, the JS system ⊨ `T7.v`

Not a delta over `t6/proofs.md` in the sense `t5/proofs.md`→`t6/proofs.md` was. Every
prior layer's obligation was "one `Machine` subclass refines the previous layer's
`Machine`." `T7.v`'s own state (`connected`, `messages`) has no counterpart inside
any single `Machine` — it is realized by the network/controller layer instead. So
the obligation here is **the JS *system* refines `T7.v`** — `α` and every per-event
argument span `model.js` + `controller.js` + the physical network, not `model.js`
alone (`implementation.md` §8, verbatim).

`RefineT6` (`T7.v` lines 729–742) is a separate, already-stated fact about the two
Rocq specs (`T7.v` refines `T6.v`), taken here as given, not re-derived — consistent
with `t7_implementation_remarks.md`: the obligation discharged in this file is JS
against `T7.v`, never JS against `T6.v` directly.

## 0. Result

No unresolved gap. One accepted, bounded divergence, argued rather than
closed outright: `FixPiece`'s own `if connected s pl then SendMessages ...
else messages s` gate, for the acting player's own connectivity, cannot be
matched step-for-step in every case — a player's own channel can fail before
the host's detection has caught up, and only the host can realize
`DisconnectPlayer pl≠Host` (§10) — but the divergence is invariant-harmless
by the same reasoning §12 already uses for the `MAX_SAFE_INTEGER` cap (§5a).

Two further points are load-bearing enough to call out up front, both argued
in full where noted: `receiveGameover`/`receiveDisconnect`'s target
redirect and the `from ↦ true` override in their `view` closures (§7, §8), and
`garbage`'s cap at `MAX_SAFE_INTEGER` (§12).

## 1. Scope

Safety only, per skill convention. Excluded from `RefineT6` (hence from any
"this JS step *is* this `T6.v` step" claim): a materializing `Fix` — `remGarbage >
0` — including one reached via `Drop` (`T7.v`'s own header comment, lines
676–681). This file's own obligation (JS ⊨ `T7.v`) is not so excluded: every JS
step, materializing or not, is argued against `T7.v`'s `Next` directly (§4–§9).

## 2. `PlayerCount = 1`

`T7.v` describes this case too (header, lines 4–6) but `t7/model.js` refuses to
construct at all unless `PlayerCount > 1` (`AxiomsPlayer`, `checkAxioms`) —
single-player is realized entirely by `t6/model.js`, selected by the controller
before any `t7.Machine` exists (`implementation.md` §0, `t7_implementation_remarks
.md`). So `PlayerCount = 1` is discharged by `t6/proofs.md` in full: `T7.v` reduces
definitionally to `T6.v` at `PlayerCount = 1` in every action that branches on it
(`FixPiece`, line 290: `if PlayerCount =? 1 then UpdatePlayer s pl s6' else ...`;
`Init`'s `connectedView`/`connected` are `PlayerCount >? 1`, both `false`; `Receive`/
`Disconnect`/`Notice` are unreachable since nothing is ever `connected`). Nothing in
this file's remaining sections applies to that regime.

## 3. State mapping `α : Σ → T7.State`

`Σ` is the full system configuration: every player's `T7.Machine` instance, every
player's `controller.js` closure state (including the host's relay/heartbeat
bookkeeping, §15.4), and the physical network (WebRTC channels + host relay
buffering). Per field, in `T7.v`'s own field order:

- `s6 α(σ) pl = α_T6(σ.machines[pl].s6)` — `α_T6` unchanged, imported from
  `t6/proofs.md` (§2 there: `α_T6 = α_T5`, no new field).
- `garbage α(σ) pl = σ.machines[pl].garbage`; `target`, `gameoverView`,
  `connectedView` likewise — direct field reads, no coercion (all four are typed
  identically on both sides: `ℕ`, `Player`, `Player → bool` realized as
  `boolean[PlayerCount]`, ditto).
- `connected α(σ) pl` — not read off any `Machine` field (none exists, §6.9/§6.10 of
  `implementation.md`). For `pl ≠ Host`: true iff `pl` has not been declared
  disconnected by the host — realized by `!declaredDisconnected` on the host's
  own `playerData[pl]` entry, a flag only the host's own controller ever sets
  (§10 — `DisconnectPlayer pl≠Host`'s effect requires broadcasting
  `DisconnectMessage` to every other player, which only the host, as the
  relay, is positioned to do; `pl`'s own local observation of her channel — via
  `hostLostHandled`, §9 — is a *different* fact, her own belief about
  *herself*, not a proxy for this field). For `pl = Host`: **no JS quantity
  represents it** — `connected(Host)` becoming `false` is the host process
  ceasing to exist, unobservable to `α` directly (§10, "realized by nobody");
  every other player's own eventual `noticeDisconnection()` is a *separate*
  `T7.v` event (`NoticeDisconnection`, §9) reacting to that fact once
  detected, not a re-derivation of it. Not the raw `RTCDataChannel.readyState`
  for either case: a channel can sit in a degraded or ICE-`failed` state for
  some time before `declaredDisconnected` is set (heartbeat timeout, or
  `watchConnection`'s `onconnectionstatechange` callback, §10) — `connected`
  in this file tracks the *declared* fact the rest of the system observes and
  acts on, not raw transport state that nothing here reads directly. This
  leaves one corner case unresolved as an exact step-match, argued as a
  bounded, harmless divergence rather than closed outright: see §5a.
- `messages α(σ) from to` — the concrete in-flight sequence from `from` to `to`:
  for `to = Host`, whatever `sendToHost`/`sendToPlayer(0, ·)` has queued in the
  channel's send buffer and not yet been read by `applyIncoming`; for `to ≠ Host`,
  the same at the host's relay step (`broadcastFromHost`/`sendToPlayer`) — the star
  topology means every non-host-to-non-host path is physically two hops, but
  `T7.v`'s `messages from to` models it as one queue between `from` and `to`
  directly; the host relay never reorders (single-threaded, processes one incoming
  event at a time, forwards before accepting the next) and never drops (no channel
  write is skipped), so the two-hop physical path and the one-queue model agree on
  order and content — a refinement detail, not an extra invariant to carry. §5a is
  the one place a send can fail outright (channel not `'open'`) rather than
  merely being relayed; see there for why that doesn't break `Correct`.

Well-definedness: for the JS system there is always exactly one channel, and
hence exactly one `declaredDisconnected`/`hostLostHandled` flag, per `(pl, Host)`
pair (data channels are 1:1 between the two peers that negotiated them,
`createOfferConnection`/`createAnswerConnection`), so `connected`/`messages` are
total functions of `σ`, matching `T7.v`'s own totality.

## 4. `movePiece`/`rotatePiece`/`holdPiece`/`rotateKickPiece`, non-materializing `Fix` — full-use transfer

Each method's guard is `if (this.winner) return false;` — `winnerMulti(this.
gameoverView, this.connectedView, this.myIndex)`, a direct transcription of
`WinnerMulti` (`T7.v` lines 172–175: `PlayerCount >? 1` is true unconditionally in
this file's regime, §2, so the guard reduces to the `ForallPlayers` clause, which
`winnerMulti`'s loop realizes cell-for-cell). When `this.winner`, the method
touches nothing and returns `false` — matches `MovePiece`/`RotatePiece`/
`HoldPiece`/`RotateKickPiece`'s `else None` branch exactly (`T7.v` lines 213–223,
470–476, 486–490). When not, each delegates to the identical `this.s6.<method>`
call `T6.v`'s own definition names (`option_map (UpdatePlayer s pl) (T6.<Action>
...)`) — `UpdatePlayer` (lines 143–153) touches only `s6` (via the delegated call)
and, conditionally, `gameoverView`'s own `(pl, pl)` cell (`T6.gameover s6'`,
`SelfViewAccurate`'s own coupling, §11 below); every other field (`garbage`,
`target`, `connectedView`, `connected`, `messages`) is `unchanged` per
`UpdatePlayer`'s record literal. `model.js` writes none of those fields in any of
these four methods — matches by construction, not by a per-field check. A
non-materializing `Fix` (`remGarbage = 0` after `this.s6.fixPiece`) is covered by
§5's collapse argument, not restated here.

## 5. Materializing `Fix` — no-use, full argument

`this.s6.fixPiece(bagNew)` runs first, unconditionally, computing full
`T6` semantics (score/level/hold/`clearedLines`/`perfectClear`/`mg`/`gameover` from
the piece placement alone) — exactly `T6.FixPiece bagNew H2 (s6 s pl)` (`T7.v` line
346). If it returns `false`, `fixPiece` returns `false` immediately, with
zero further mutation — matches the `None` case of `T6.FixPiece`'s result under
`option_map`.

**Case `remGarbage = 0` (`NoRemGarbage` holds, `T7.v` lines 715–720).** Then
`effRem` computes to `0`: the shift/overwrite block does not run.
`gameover2` is computed as `this.s6.gameover`, left unmodified by the
skipped `if (!gameover2 && remGarbage > 0)` guard (its `remGarbage > 0` condition
is false), then recomputed via the trailing `T1Eng.intersect` call (since
`gameover2` is still whatever `this.s6.gameover` was — the `!gameover2` guard
immediately before it only skips this recompute when already `true`). This
recompute reads `s1.mg` — literally the same grid `this.s6.fixPiece` just produced,
untouched by the (skipped) shift — so `T1Eng.intersect(ForbiddenGrid, FY, FX, s1.mg,
0, 0)` recomputes exactly the same boolean `T1.Correct`'s own forbidden-zone clause
already pins `this.s6.gameover` to (this is what `Gameover pl s` states as an
implication, `T7.v` lines 611–612, and it holds as an invariant of the `T6`-level
state by inheritance — not argued fresh here, only used). So `gameover2 =
this.s6.gameover` exactly, and the whole block reduces to: `this.garbage = 0`
(matching `T7.v`'s `garbage := λ pl2, if pl2=?pl then 0 else ...`, lines 319–324),
`this.remGenGarbage` set (read-only bookkeeping field, no `T7.v` counterpart, §6.7
of `implementation.md`; harmless — never observed by any guard), `gameoverView[my
Index]` set to the same value it already held. The target-redirect guard
(`remGenGarbage > 0 && !gameover2`) is exactly `T7.v`'s own guard at the
corresponding branch (line 329, `(0 <? remGenGarbage) && !gameover'`) — under
`NoRemGarbage`, `remGenGarbage = genGarbage - garbage` is 0 exactly when
`garbage ≥ genGarbage`, the same condition that forces `remGarbage = garbage -
genGarbage = 0`; conversely `remGarbage = 0 → genGarbage ≥ garbage → remGenGarbage
= genGarbage - garbage`, which may be positive — so `NoRemGarbage` does *not* force
this guard shut, and it does not need to: `T7.v`'s own branch condition is
independent of `remGarbage`, so this case exercises exactly the same redirect
`T7.v` calls for, covered by §7 below. Net: under `NoRemGarbage`, `fixPiece`'s only
observable effect is `this.s6.fixPiece(bagNew)` plus the `garbage := 0` write plus,
possibly, the very redirect `T7.v` itself performs — i.e. it *is* `T6.Next
e6 (fₛ pl s7)`, matching `RefineT6`'s own claim, not contradicting it (`H4` in
`RefineT6`'s statement excludes this call from *that* proof's obligation, but
nothing here needs re-deriving it — `NoMaterializedGarbage`'s left disjunct,
`PlayerCount = 1`, is out of scope by §2; its right disjunct is this case).

**Case `remGarbage > 0`.** `RefineT6`'s hypothesis `H4` excludes this call from the
T6-refinement claim entirely (`NoMaterializedGarbage` fails) — no obligation there.
This file's own obligation (JS ⊨ `T7.v`) still applies, and is a direct
transcription:
- `effRem = min(remGarbage, HM)` — `T7.v`'s `Grid` algebra crops
  unboundedly via `∩ Full mg` (line 304); the array representation needs the
  clamp explicit to keep indices in range. `remGarbage ≥ HM ⟹ effRem = HM`: the
  shift loop's source range `[0, HM - effRem) = ∅`, so every old row is dropped —
  matching total replacement by `GarbageGrid`'s rows once its own height reaches
  or exceeds `HM`.
- **Overflow.** `remGarbage ≥ HM` ⟹ `overflow = true` unconditionally, no scan
  needed — `T7.v`'s own crop drops the *entire* old `mg` in this regime (every
  row of `mg` sits at an offset `≥ HM` post-shift), so `mg' ⊈ croppedMg'` is forced
  true whenever `mg` has any occupied cell — and a `T6.Correct` machine's `mg` is
  never all-empty once a piece has fixed (a fixed piece always leaves an occupied
  cell unless every row it touched was immediately cleared, in which case the
  *next* line down does; `HM ≥ 1` throughout). When `remGarbage < HM`, the
  overflow scan reads rows `[HM - remGarbage, HM)` of `s1.mg` **before** the
  shift/overwrite loop below overwrites them (the scan runs first, in source
  order) — these are exactly the
  rows `T7.v`'s `mg ⊕ (remGarbage, 0)` pushes to `y ≥ HM`, i.e. exactly the rows
  `Full mg`'s crop drops; `mg' ⊈ croppedMg'` iff one of them is occupied, which is
  what `T1Eng.occ` tests cell-by-cell. Same value, same rows.
- **Shift/overwrite**: decreasing `i`, source row `i` written to
  destination `i + effRem` — reversed order is load-bearing (a later destination
  can coincide with an earlier source once `effRem < HM`; increasing order would
  read an already-overwritten row). This *is* `mg ⊕ (remGarbage, 0)`. Rows `[0,
  effRem)` are then set to `garbageRow(holesFn(y), WM)` — `T7.v`'s `GarbageGrid
  remGarbage holes (W InitialMainGrid)`, one row of occupied cells except the
  hole column, realized directly for the array (no intermediate `Grid` record,
  `implementation.md` §5) instead of via the `Grid`-algebra union `T7.v` uses; the
  union's semantics (row `y < remGarbage` ↦ `GarbageGrid`'s content, row `y ≥
  remGarbage` ↦ shifted `mg`) is exactly what the two loops realize over disjoint
  row ranges, so no cell is written twice and none is left unwritten within `[0,
  HM)`. The trailing `this.s6.updateShadowY()` call *does* have a `T7.v`
  counterpart: `FixPiece`'s materialization branch passes `CroppedMg'` to
  `NewMainGridGameoverState`, which itself calls `T5.UpdateShadowY` (`T7.v`
  line 312) to recompute `gy` against the new grid — exactly the refresh
  `this.s6.updateShadowY()` performs here, for the same reason (`gy` was
  computed by the piece placement alone and is stale once garbage rows are
  spliced in). Not a new argument: `t5/proofs.md` §3's `gy`-refresh obligation
  already covers `T5.UpdateShadowY`'s own correctness; this call site is one
  more place that obligation discharges, not a divergence from `T7.v`.
- **Forbidden-zone recheck** (short-circuited when `gameover2` is already
  `true`, per `implementation.md`'s explicit note) is the third disjunct of `T7.v`'s
  `gameover'` (line 308, `ForbiddenGrid ∩ croppedMg' ⊈ ∅`), evaluated on the same
  post-shift `s1.mg` that *is* `croppedMg'` by construction (every write stays
  within `[0, HM)` — the array never grows past it, so cropping is free). Boolean
  `||` across the three disjuncts (`this.s6.gameover`'s initial value, `overflow`,
  this recheck) is realized by the two guarded reassignments of `gameover2` in
  sequence, each leaving it unchanged once already `true` — same short-circuit
  `T7.v` itself permits (its own `||` needs no evaluation order, being a pure
  boolean expression; JS's is an optimization, not a semantic difference).
- `this.garbage = 0`, `gameoverView[myIndex] = gameover2` —
  `T7.v` lines 319–324, 335–337, cell for cell.
- **Redirect**: guard and computation both match `T7.v` lines
  325–334 exactly, `playingView'`/`view` built identically (`!gameoverView' &&
  connectedView`, read *after* `gameoverView[myIndex]` was just updated —
  matching `T7.v`'s own `gameoverView'`, which folds in the same just-written
  self-cell before being read by `NextTarget`, line 312–313). §7's termination
  lemma (used generically, not re-derived per call site) confirms this call never
  needs `T7.v`'s `from ↦ true` override: the search here starts at `target s pl`
  itself, a player whose own liveness this very call cannot have changed (`pl ≠
  target(pl)` by `TargetNotSelf`, so the one cell this call can move — `(pl, pl)`
  — is not the one being searched), so the wraparound candidate is provably still
  `PlayingView`-true without any forced override (§7, case 2).

## 5a. `FixPiece`'s own `connected s pl` gate — bounded divergence, not an exact match

`FixPiece`'s `messages` field is `if connected s pl then SendMessages s pl
remGenGarbage gameover' else messages s` — gated on the *acting* player's own
connectivity, not the recipient's. §5 above (and §8's enqueue argument) only
discuss `SendMessages`'s internal `to =? pl` self-exclusion; this is the outer
gate.

For `pl = Host`, this is trivially satisfied: `connected(Host)` is `true`
throughout any trace this file considers (its only path to `false` is the
host process itself dying, argued in §10 as ending the trace, not a state
within it), and the host's own sends are always local delivery
(`applyIncoming`/`broadcastFromHost`), never a real channel — the gate never
meaningfully fires `false` here.

For `pl ≠ Host`, `connected(pl)` is `!declaredDisconnected[pl]` (§3) — a value
the host's controller owns, not something `pl`'s own client can read
directly. `pl`'s own `sendToHost` call instead checks her own
`hostConn.readyState`/`hostLostHandled` (§9, fixed to fail fast rather than
silently drop) — a *different*, only loosely-correlated fact. So a genuine
corner case exists: the host hasn't yet set `declaredDisconnected[pl]` (α
says `connected(pl) = true`, so `T7.v`'s `FixPiece` requires
`SendMessages` to append a message), but `pl`'s own channel has already gone
bad, and her send fails. `T7.v`'s `connected` field is untouched by
`FixPiece` either way (`connected := connected s` in the record literal, both
branches), so there is no way to reclassify this JS step as the other
branch — this is a literal mismatch: `T7.v` computes a `messages'` with the
new entry appended; the JS `α(σ')` does not have it.

This is not closed by fail-fast sending (§9's fix narrows the *window* this
can happen in — from up to `HEARTBEAT_TIMEOUT_MS` down to whatever gap
remains between `pl`'s own channel actually failing and the host's own
detection running — but cannot eliminate it: `pl` still lacks the means to
learn `declaredDisconnected[pl]`'s live value before deciding whether to
attempt the send). Nor can `pl` close it herself: `DisconnectPlayer pl≠Host`'s
effect also requires broadcasting `DisconnectMessage` to every other player
(§10) — something `pl`, having just lost her own link to the host (the only
relay), has no means to do. The realization genuinely can only be the host's.

**Why this is harmless anyway (same shape as §12).** Neither `MessageSound`
nor `LastMessagesGameoverDisconnect` (`T7.v`'s only invariants that mention
`messages`) requires a message to be *present* — both only constrain its
*content* when one is. A message `T7.v` would have appended, but that `pl`'s
own dead channel drops before the host has caught up, violates no conjunct
of `Correct`: nothing downstream ever observes its absence as a violation,
only the safety scope this file claims (§1) — an exactly analogous move to
§12's `MAX_SAFE_INTEGER` clamp, which is also "a real divergence from the
spec's literal semantics" accepted because nothing in `Correct` is sensitive
to it. Liveness (a genuinely-sent `GARBAGE`/`GAMEOVER` eventually being
*acted on* by anyone) is explicitly out of scope (§1) regardless.

## 6. `dropPiece` — no-use relocation, then §5 in full

`T6Eng.T4Eng.assertPieceSet(bagNew)` throws before any mutation if
`bagNew` is malformed — defensive, mirrors `t5/model.js`'s own `dropPiece`
(the same `assertPieceSet` call there), no `T7.v` counterpart (`T4.PieceSet` is a
`Prop` hypothesis there, not a runtime check). The `this.gameover` guard is
likewise a fast-path, not new semantics: if already gameover, `this.s6.fixPiece`
inside the eventual `this.fixPiece` call would itself decline (inherited `T6`-level
guard), so `DropPiece` would return `None` regardless via `FixPiece`'s own
composition (`T7.v` line 484); short-circuiting before the relocation changes
nothing observable, matching the same reasoning `t5/proofs.md` §6 already gives for
this exact style of upfront check. The relocation itself (one `s1`
field copy: `mg`/`p`/`py`/`px`/`pr`/`gameover`/`clearedLines`) is the identical
pattern `t5/model.js`'s own `dropPiece` uses, reached through `T6.Machine`'s
inherited flattened `s1` accessor and `gy` field with no patch to `t5/model.js`/
`t6/model.js` — `T1.NewPieceYXState (gy s pl, px s pl) pl s`, `T7.v` line 478–479,
wrapped in `UnchangedT7Part` (nothing outside `s6` moves), matching
that only `s1`'s seven fields are touched here. The trailing `this.fixPiece(bagNew,
holesFn)` call is `T7`'s own `fixPiece`, not `this.s6.dropPiece` —
so garbage generation/cancellation/materialization/redirect is not bypassed on a
hard drop — and is covered by §5 in full, no new argument needed (`T7.v`'s own
composition, line 484: `FixPiece pl holes H1 bagNew H2 (NewPieceYXState ...)`).

## 7. `NextTarget` termination lemma

Used by §5 (`fixPiece`'s own redirect) and §8 (`receiveGameover`/
`receiveDisconnect`). `NextTargetAux`'s only fallback is its `fuel = 0` case,
returning `self` (`T7.v` lines 180–187) — every use of `nextTarget` in `model.js`
must never actually reach it while `Correct s7` holds, or the JS/spec field values
would diverge at a point invariants are meant to prevent.

**Claim.** For every reachable `s7` with `Correct s7` and `NoWinner s7'` at the
post-state `s7'` of the call in question, some candidate distinct from `self` and
from the search's starting point is found strictly before the search would need to
wrap fully around.

**Proof.** `MessageSound` (lines 556–558) plus the branch guard (`from` is the
sender of the `GameoverMessage`/`DisconnectMessage` just popped) gives: the player
the search is walking away from is truly not-playing post-update (`gameover s from
= true` or `connected s from = false`, hence `Playing s' from = false`, line 534).
`ViewSound`'s two clauses (lines 550–552), read contrapositively, give: any player
truly playing at `s'` is `PlayingView`-true to `pl` at `s'` (a view can lag calling
someone dead who's alive — never the reverse). `NoWinner s'` (lines 538–539)
supplies two distinct truly-playing players; at most one can be `pl` herself
(excluded from candidacy, `!(pl2 =? self)`), so at least one genuine candidate
`Y ≠ pl` exists and is `PlayingView`-true. `NextTargetAux`'s walk visits every
other player exactly once, in cyclic order (`PlayerCyclicPermutation`, lines
59–61), before it could ever revisit the walk's own starting point — so `Y` is
found at some step strictly before the wraparound. ∎

**Two call sites, two conclusions.**
1. `receiveGameover`/`receiveDisconnect` (§8): the walk starts at `from`, the very
   player whose status just became "not playing". `T7.v`'s `view'` forces
   `view'(from) = true` (line 364); `model.js`'s `view` closures in both methods
   carry the same override (`pl2 === from ? true : playingView(...)`). The
   override matters exactly when `NoWinner s'` fails: without it, the walk would
   reach the wraparound point with `view(from)` evaluating to the *post-update*
   value — `false` — and fall through to `NextTargetAux`'s own `self` fallback,
   disagreeing with `T7.v`'s own result there, which is `from` itself (a no-op,
   since `from` was already `target s pl`). The claim above shows this case never
   arises while `Correct` holds — but matching `T7.v`'s literal computation on
   every state the code can reach, not only the invariant-constrained subset, is
   the actual obligation, so the override is part of `model.js` regardless.
2. `fixPiece`'s own redirect (§5): the walk starts at `target s pl`, a player whose
   liveness *this* call cannot have changed (the only cell `fixPiece` can move is
   `(pl, pl)`, and `target(pl) ≠ pl` by `TargetNotSelf`). So the wraparound
   candidate, `target s pl` itself, is provably still `PlayingView`-true regardless
   of whether `NoWinner s'` holds — no override is needed here, and `T7.v` uses
   none at this call site either (`playingView'` unmodified, line 313).

## 8. `receiveGarbage`/`receiveGameover`/`receiveDisconnect` — cross-machine argument

Each realizes one `Receive` event: a queue pop between exactly one `(from, pl)`
pair (`T7.v` lines 358–406). This is an in-order, step-by-step argument, not a
reordering one — `messages from to`'s FIFO shape (`LastMessagesGameoverDisconnect`,
lines 572–577) exists precisely so "not yet delivered" *is* the queue; there is
nothing left to reorder once α is defined per §3.

- **Enqueued exactly once, by exactly one action.** A `GarbageMessage`/
  `GameoverMessage` is appended only inside `SendMessages` (`T7.v` lines 270–281),
  called only from `FixPiece`, only when `connected s pl` (line 343) — realized as
  `handleFixResult` (`controller.js`), called only from
  `fixFamily`, only when the preceding `fixPiece`/`dropPiece` call returned `true`
  (`fixFamily`'s own `fired`/`wasFix` guard) — one JS call per one successful
  `T7.v` `FixPiece` step, matching one
  Rocq append per step. A `DisconnectMessage` is appended only inside
  `DisconnectPlayer`, only for `pl ≠ Host` (line 433) — realized by **two**
  independent call sites in `controller.js`, each guarded by the same
  `declaredDisconnected` flag, checked and immediately set before any send: the
  heartbeat branch (`startHeartbeat`'s host case)
  and `watchConnection`'s `onFailed` callback for that player's own connection
  (wired up when a host-side connection is added, reacting to
  `pc.onconnectionstatechange === 'failed'`). Whichever fires first for a given
  `pl` sets `declaredDisconnected = true` before broadcasting; the other is then
  a no-op by its own guard (heartbeat: `continue`s past an already-declared
  player; `watchConnection`'s callback: returns early if
  `p.declaredDisconnected`) — so exactly one `DISCONNECT` is ever broadcast per
  `pl`, matching `DisconnectPlayer`'s own single-append shape regardless of
  which JS trigger realized it — matching `DisconnectPlayer`'s own guard (`if
  connected s pl then ... else None`, line 423): once `connected s pl` flips
  false, a repeat firing of the same event is already excluded at the Rocq
  level, and `declaredDisconnected` is exactly the JS-side realization of that
  same fact (there is no other place `connected`'s JS-side truth, §3, could
  un-flip).
- **Dequeued in order, exactly the message that was enqueued first.** `applyIncoming`
  dispatches on `msg.type` directly against the concrete message
  object the host relayed or the direct channel delivered — channels are
  created with `{ ordered: true }` (WebRTC's default
  `ordered: true` for the answer side as well), so delivery order equals send order on
  each hop, and the host relay (`hostHandleFromJoiner`, `joinerHandleFromHost`)
  processes one incoming `onmessage` event fully before the next is dispatched
  (single-threaded JS, no interleaving) — the physical channel realizes exactly
  the FIFO `messages` gives. `receiveGarbage`/`receiveGameover`/`receiveDisconnect`
  are called with precisely that message's payload, never a stale or reordered
  one.
- **The queue only shrinks, never grows, independent of other players' concurrent
  steps.** `messages s' from to` (`T7.v`'s pattern `m :: rest ↦ rest`, lines
  362–363) shrinks by exactly the popped message, for the one `(from, to)` pair
  addressed — every other pair's queue is `messages s` unchanged (all three
  branches, lines 368–402). JS realizes this the same way: `applyIncoming` reads
  and consumes exactly the one message it was invoked with; nothing else in
  `model.js`/`controller.js` mutates any other channel's buffer as a side effect
  of processing this one. This is `OtherS6Unchanged`'s counterpart for the
  network layer — needed so this argument doesn't have to account for
  interleaving with unrelated players' own steps, exactly as `implementation.md`
  §8 item 6 states.
- **Field-level match, each branch:**
  - `receiveGarbage(amount)`: `this.garbage = (this.garbage <= MAX_SAFE_INTEGER -
    amount) ? this.garbage + amount : MAX_SAFE_INTEGER` ≙
    `garbage := λ pl2, if pl2=?pl then garbage s pl2 + n else garbage s pl2`
    (line 369) up to the cap argued in §12 — no `from` needed on either side
    (sender-agnostic `+=`), matching `T7.v`'s own branch, which never reads
    `from` either (lines 366–375). No other field moves, either side.
  - `receiveGameover(from)`: `this.gameoverView[from] = true` ≙ the
    `(pl, from)` cell of `gameoverView` (line 385, `obs =? pl && obsd =? from`);
    redirect guard and computation covered by §7 case 1. No other field moves
    (`s6`, `garbage`, `connectedView` all pass through unchanged both sides —
    lines 378, 386–387).
  - `receiveDisconnect(from)`: `this.connectedView[from] = false` ≙ the
    `(pl, from)` cell of `connectedView` (line 398, same shape as `receiveGameover`'s
    `gameoverView` cell); redirect present on both sides, covered by §7 case 1
    identically to `receiveGameover`'s.

## 9. `noticeDisconnection` — stutter w.r.t. `s6`, single-machine

`connectedView[myIndex] = false` ≙ the `(pl, pl)` cell of
`connectedView` (`T7.v` line 449) — no other field moves, either side. `T7.v`'s own
guard (`! connected s pl && connectedView s pl pl`, line 443) is *not* checked in
JS: the caller (`noticeHostLost`) only invokes this
when its own heartbeat timeout or `watchConnection`'s `onFailed` callback (its
own connection to the host reaching `connectionState === 'failed'`) has just
fired, which is exactly the
trigger condition for `¬connected s pl` becoming true — a controller fact, not
something `α` needs to reconstruct (`implementation.md` §8 item 7). The second
conjunct (`connectedView s pl pl`, "hasn't already noticed") is not checked either;
its absence is harmless, not a divergence: the field write is idempotent
(`false ← false` on a repeat call is the same state as `T7.v`'s own `None` — no
transition — since the observable successor state is identical either way, and
nothing downstream distinguishes "stuttered" from "fired redundantly" for this
field). `noticeDisconnection` also returns no boolean, unlike every other
`Machine` method — a real deviation from the "every action returns a fired/not-
fired boolean" convention (`rocq-to-js` skill), but not one that affects this
proof: `controller.js` never reads a return value from this call.

## 10. `Disconnect`

- **`pl = Host` — realized by nobody.** `DisconnectPlayer`'s effect when `pl =
  Host` sets `connected' pl1 = false` for *every* `pl1` at once (line 431: the
  `pl =? Host` disjunct makes the guard `false` unconditionally) — "if the host is
  disconnected, everyone is." No JS code realizes this as a step: the host
  process ceasing to exist *is* the fact `connected := λ _, false` becomes true of
  (`α σ`) at the next real step any surviving player takes (`implementation.md` §8
  item 8) — every other player's own `noticeHostLost` (§9) observes this
  indirectly, once its own heartbeat-or-`connectionstatechange` detection fires,
  but that firing is
  `NoticeDisconnection`, a separate `T7.v` event with its own argument (§9), not a
  re-derivation of `DisconnectPlayer(Host)` itself.
- **`pl ≠ Host` — realized by the host's controller**, never by any `Machine`.
  Two call sites reproduce `DisconnectPlayer pl`'s two field changes directly,
  identically, via different triggers (§8): `startHeartbeat`'s host branch,
  on a `10` s `lastHeard` silence, and `watchConnection`'s
  `onFailed` callback for that connection (wired up when a host-side connection
  is added), on `pc.onconnectionstatechange` reaching `'failed'`. Either one, on
  first firing for a given `pl`: `connected` — only `pl`'s own entry flips
  (`connected' pl1 = if pl1 =? pl then false else connected s pl1` when `pl ≠
  Host`, since the `pl =? Host` disjunct is false, line 431) — realized as
  `p.declaredDisconnected = true` for that one player, §3's `connected α(σ)`
  reading that flag becoming permanently false for `pl`, unaffected for anyone
  else; `messages` — `DisconnectMessage` appended from `pl` to every `to ≠ pl`
  (line 433–436) — realized as `applyIncoming(msg)` (the host's own local delivery,
  §8) plus `broadcastFromHost(tag(msg), i)` (every other connected player), one
  send per recipient, matching one append per `(pl, to)` pair for every `to ≠ pl`.
  Whichever site fires first, the argument is the same — nothing here depends on
  which trigger detected the loss.

`implementation.md` §15.4 describes disconnection detection as either
`connectionState` reaching `'failed'` or a `10` s `STATE`-heartbeat timeout —
both realized in the code, as above; there is no third, `onclose`-based path.

## 11. Representation invariant — `Correct`, by induction

Base case, `Init` (`T7.v` lines 197–209) vs. `Machine`'s constructor: `s6Init` ≙
`new T6Eng.Machine(bagsFn)`, inherited `T6.Correct` (not
re-derived); `garbage = 0`, `target = PlayerNext(myIndex)`; `gameoverView` — `T7.v`'s
`Init` sets the `(obs, obs)` diagonal to `T6.gameover(s6Init obs)` and everything
else `false` — the constructor fills the whole array `false` then overwrites
only its own index (`this.gameoverView[myIndex] = this.s6.gameover`) —
each `Machine` instance only ever holds *its own* view (§4-T7b), so the array it
stores realizes exactly the `obs = myIndex` row of `T7.v`'s two-argument function,
which is `false` off-diagonal and `T6.gameover` on it — matching. `connectedView`
— all `true` ≙ `PlayerCount >? 1`, always `true` in this file's regime
(§2). `SelfViewAccurate` (per the constructor's own `gameoverView[myIndex]`
assignment) and `TargetPlaying`/
`TargetNotSelf` (vacuous at `Init`, `NoWinner` holds since every real player starts
alive and connected — no invariant needed beyond `Init`'s own field values, §2's
analogue already checked in the consistency review this file is written against)
all hold immediately.

Inductive step, one clause per method:

- **`OtherS6Unchanged`.** Every method above writes `this.s6` only inside the
  `Machine` instance the call was made on; `controller.js` never reaches into
  another player's `s6` directly (every cross-player effect goes through
  `receiveGarbage`/`receiveGameover`/`receiveDisconnect`/`noticeDisconnection`,
  §8–§9, none of which touch `s6` at all). Matches `T7.v`'s own shape (every
  action's record literal sets `s6 := λ pl2, if pl2=?pl then s6' else s6 s pl2`).
- **`GameoverMonotone`/`GameoverViewMonotone`.** `s6.gameover` only ever moves
  `false → true` (inherited monotonicity from `t1/proofs.md` up through
  `t6/proofs.md`, never re-derived here); `gameoverView[i]` is only ever *set* to
  `true` (`receiveGameover`) or to `this.s6.gameover`'s current value at
  the owner's own index (`fixPiece`) — the latter can only move
  `false → true` by the former fact, never back. No method sets any
  `gameoverView` cell to `false`.
- **`DisconnectedMonotone`/`DisconnectedViewMonotone`.** `connected`'s JS-side
  realization (`declaredDisconnected`, §10) is set-once, never cleared, for the
  lifetime of a match (`matchGen` resets it only across a `START`/rematch
  boundary — a fresh `Init`, not a step within one run). `connectedView[i]` is
  only ever set to `false` (`noticeDisconnection`, `receiveDisconnect`), never
  back to `true`.
- **`SelfViewAccurate`.** The one place `s6.gameover` can newly become `true` is
  inside a successful `this.s6.<method>` call; every method that can trigger this
  (`movePiece`/`rotatePiece`/`holdPiece`/`rotateKickPiece`/`fixPiece`, via `T6`'s
  own logic) is immediately followed, in the same call, by
  `this.gameoverView[this.myIndex] = this.s6.gameover` — explicit in `fixPiece`;
  for the other four, `UpdatePlayer`'s realization is folded directly
  into each getter/field being read live rather than snapshotted (§6.8 of
  `implementation.md`) — `this.gameover` (the getter) *is* `this.s6.gameover` read
  through, so `checkInvariants`' own assertion
  (`s.s6.gameover === s.gameoverView[s.myIndex]`) is the exact invariant, and every
  method that can move `s6.gameover` moves the paired cell in the same step. No
  method moves one without the other.
- **`TargetNotSelf`/`TargetPlaying`.** Preserved by every method that doesn't
  touch `target`, trivially (nothing relevant changes). For the two that do
  (`fixPiece`'s own redirect, `receiveGameover`/`receiveDisconnect`'s), §7
  establishes both: under `NoWinner` at the post-state, a genuine candidate
  `≠ self` is always found before any wraparound, so the result is never `self`
  (`TargetNotSelf`) and is always `PlayingView`-true at the post-state by
  construction of the search (`TargetPlaying`) — argued per call site in §5 and
  §8/§7 respectively, not restated here.
- **`ViewSound`/`MessageSound`/`NoSelfMessage`/`LastMessagesGameoverDisconnect`.**
  Properties of the network/message layer (§3), preserved by construction of
  `controller.js`'s relay: a `GameoverMessage`/`DisconnectMessage` is only ever
  enqueued (§8/§10) at the same step the corresponding truth (`gameover`/
  `connected`) becomes false→won't-revert — never before, per the enqueue sites
  identified in §8/§10 — and `SendMessages`'s own `to =? pl` exclusion (`T7.v`
  line 274) is realized by `handleFixResult` never addressing a message to
  `myIndex` (`to = preTarget`, always `≠ myIndex` by `TargetNotSelf`) and by the
  host's `DISCONNECT` broadcast excluding the disconnected player itself
  (`broadcastFromHost(tag(msg), i)`, excludes index `i`) — realizing
  `NoSelfMessage`.

## 12. Integer-range soundness

Every capped accumulator in the tower (`score`, and anything else gated by
`MAX_SAFE_INTEGER`, threaded through `T(...)`'s own `MAX_SAFE_INTEGER` parameter
and passed on to `T6Eng`'s own construction) is explicitly clamped before it
could lose `Number` precision, including `garbage`: `receiveGarbage` computes
`this.garbage = (this.garbage <= MAX_SAFE_INTEGER - amount) ? this.garbage +
amount : MAX_SAFE_INTEGER`; `checkInvariants` asserts `s.garbage <=
MAX_SAFE_INTEGER` alongside `>= 0` (one combined assertion, `garbage range
failed`).

The check runs on the two addends, before the addition, rather than on
`this.garbage + amount` itself: once that sum exceeds `MAX_SAFE_INTEGER`, the sum
is already a value JS cannot represent exactly, so comparing it against
`MAX_SAFE_INTEGER` is not a reliable test in general — only comparisons between
values still within the safe range are. `this.garbage` is within range by this
same invariant, and `amount` is `generatedGarbage`'s own small output (well under
`HM`) at every call this proof considers, so `MAX_SAFE_INTEGER - amount` is exact,
and the comparison against it is sound regardless of what value `MAX_SAFE_INTEGER`
itself is instantiated to — the pre-check form doesn't rely on any coincidence of
`Number.MAX_SAFE_INTEGER`'s own bit pattern the way testing the (already unsafe)
sum would.

`T7.v`'s `garbage : Player → ℕ` is exact and unbounded (Rocq `ℕ`), so the clamp is
a real divergence from the spec's literal semantics — but only in a regime
`Correct` doesn't reach in an ordinary match: `garbage` is drained to `0` on every
one of `pl`'s own successful materializing fixes (§5), so its growth between two
of `pl`'s own fixes is bounded in practice by human input cadence and
per-message garbage size (`generatedGarbage`'s output is small, well under `HM`);
the clamp has observable effect only on a trace where `pl` never fixes again
while receiving unboundedly many `GarbageMessage`s, which nothing else in this
proof depends on being possible or impossible.

The clamp introduces no divergence elsewhere: `genRemGarbage`'s subtraction
(`Math.max(0, garbage - genGarbage)`, called immediately after, with `genGarbage`
always small — bounded by `generatedGarbage`'s own small range, well under `HM`)
stays exact regardless of whether `garbage` sits at the cap, since
`MAX_SAFE_INTEGER` minus a small value remains exactly representable.

## 13. Summary

| method | argument |
|---|---|
| `movePiece`/`rotatePiece`/`holdPiece`/`rotateKickPiece` | full-use transfer (§4) |
| `fixPiece`, `remGarbage = 0` | collapses to `this.s6.fixPiece` exactly (§5) |
| `fixPiece`, `remGarbage > 0` | no-use, full transcription of materialization + redirect (§5), redirect soundness via §7 case 2 |
| `fallStep` | disjoint-guard sequencing over `movePiece`/`fixPiece`, both above |
| `dropPiece` | no-use relocation (mirrors `t5/model.js`) + §5 in full (§6) |
| `receiveGarbage`/`receiveGameover`/`receiveDisconnect` | cross-machine, message-queue argument (§8), redirect soundness via §7 case 1 |
| `noticeDisconnection` | stutter w.r.t. `s6`, controller-detected trigger (§9) |
| `Disconnect`, `pl = Host` | realized by nobody — argued against reality (§10) |
| `Disconnect`, `pl ≠ Host` | realized by the host's controller relay (§10) |
| `Correct` | inductive, one clause per method (§11) |
| `garbage`'s range | capped at `MAX_SAFE_INTEGER` in code, unbounded (exact `ℕ`) in the spec (§12) |
| `fixPiece`'s outer `connected s pl` message gate | bounded, invariant-harmless divergence — not an exact match (§5a) |
