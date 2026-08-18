# implementation.md — ImplementationInstructions for T7

Per-model instructions for the transformation

```
FormalModel (T7.v)  ×  ImplementationInstructions (this file)
      ── rocq-to-js skill ──▶  Code (model.js, view.js, controller.js, instance.js, index.html)
                             ×  Proofs (proofs.md)  ×  Tests (tests/)
```

Delta over `t6/implementation.md`. All references to `T7.v`/`T6.v`/`T1.v` are **by
definition name**.

## 0. Inputs, outputs, files reused

Codegen-time inputs: `T7.v`; `T6.v`/`t6/implementation.md` and predecessors;
this file; `rocq-to-js.md`.

`t7/model.js` implements multi-player (`PlayerCount > 1`) only. Single-player uses
`t6/model.js` directly, selected by the controller before any `t7.Machine` exists.

### 0.1 Files reused unchanged

| file | role in T7 |
|------|-----------|
| `lib/utils.js` | shared primitives |
| `t1/model.js` | T1 engine — reached as `T6Eng.T1Eng`; `intersect` reused directly (§4-T7c) |
| `t6/model.js` | T6 engine — imported as `T6`; called as `T6(...)` |
| `t6/view.js` | wrapped, not re-exported (§14) |

### 0.2 No prerequisite patch

No change to `t1/model.js`–`t6/model.js`. Materialization (§4-T7c) is new T7 logic
operating on the fixed-size array representation directly; it reuses `intersect`
(already exported by `t1/model.js`) for the forbidden-zone recheck and reuses no
other existing grid helper (those operate on the piece-over-mainGrid overlay shape,
not on materialization's row-shift shape).

### 0.3 `Player` is a match-time parameter, not an instance.js constant

`Player`, `PlayerCount`, `PlayerNext`, `Host` all derive from the roster, which
exists only once `START` fires (§15.1). `T(...)` (§7) takes `Player`/`HostIndex`
as arguments supplied by `controller.js` at that point, not at module load.

## 1. The refinement

`fₑ`: `Move`/`Rotate`/`Fix`/`Fall`/`Hold`/`Drop`/`RotateKick` map to their `T6`
event; `Receive`/`Disconnect`/`Notice`/`Stutter` map to `Stutter`. Excluded from
`RefineT6`: a materializing `Fix` (`remGarbage > 0`), including one reached via
`Drop`.

Per skill §7.1:
- `movePiece`/`rotatePiece`/`holdPiece`/`rotateKickPiece` — full uses, delegate to
  `this.s6`.
- `fixPiece` — full use when `remGarbage = 0`; no-use (new logic) when
  materializing.
- `dropPiece` — no-use for the relocation step (trivial, mirrors T5's own
  classification of that step), then inherits `fixPiece`'s own categorization for
  everything after.
- `noticeDisconnection`/`receiveGarbage`/`receiveGameover`/`receiveDisconnect` —
  no `T6.v` counterpart; touch no `s6` field (stutter w.r.t. `s6`, always).
- `DisconnectPlayer` — no `Machine` method exists (§4-T7f).

## 2. File layout

```
instance.js       # re-exports t6/instance.js; adds nothing (§11)
model.js          # T7 engine: wraps T6.Machine, adds garbage/target/gameoverView/
                   #   connectedView/remGenGarbage (§5-7)
view.js           # renderer: mini-grid strip, garbage gauge, wraps t6/view.js (§14)
controller.js     # network relay, lobby, waiting room (§15)
../vendor/
  fflate.js       # deflate/inflate, used by controller.js's rawSend/decodeMsg (§15.3)
index.html        # canvas + DOM overlay container (§15.8)
proofs.md         # refinement proof, delta over t6/proofs.md (§8)
tests/
  testInstance.js
  model.unit.test.js
  model.properties.test.js
  model.fuzz.test.js
  oracle.js
```

## 3. Naming map (T7.v → JS)

| T7.v | JS |
|------|----|
| `Player` (Parameter) | roster array of indices, supplied to `T(...)` at match start (§0.3) |
| `Host` | `Player[HostIndex]` — `HostIndex` a module parameter (§7) |
| `PlayerEqb` | not emitted — `Player` values are plain indices, compared with `===` directly (§7) |
| `PlayerNext` | `i => (i + 1) % PlayerCount` |
| `PlayerCount` | `Player.length` (derived) |
| `Message` (inductive) | not mirrored as a type — wire messages are tagged objects (`GARBAGE`/`GAMEOVER`/`DISCONNECT`/`STATE`), §15.3 |
| `State` (record) | the `T7.Machine` instance; fields below |
| `s6` | `this.s6` (a `T6.Machine`) |
| `garbage` | `this.garbage` (`number`) |
| `target` | `this.target` (`Player` index) |
| `gameoverView` | `this.gameoverView` — `boolean[PlayerCount]`, own view only (no observer index — a `Machine` only ever holds its own view) |
| `connectedView` | `this.connectedView` — `boolean[PlayerCount]`, own view only |
| `connected` | not stored (§6.9) |
| `messages` | not stored (§6.9) |
| `mg` (helper) | `this.s6.s1.mg` (not promoted, §6.8) |
| `gameover` (helper) | `this.s6.gameover` |
| `clearedLines` (helper) | `this.s6.clearedLines` |
| `UpdatePlayer` | not emitted — each method mutates `this` directly |
| `PlayingView` | `playingView(gameoverView, connectedView, pl2)` — free function, no observer parameter |
| `WinnerMulti` | `winnerMulti(gameoverView, connectedView, myIndex)` — free function |
| `NextTargetAux`/`NextTarget` | `nextTarget(playing, self, pl)` — free function |
| `Init` | `new eng.Machine(myIndex, bagsFn)` |
| `GeneratedGarbage` | `generatedGarbage(clearedLines, perfectClear)` |
| `GenRemGarbage` | `genRemGarbage(garbage, clearedLines, perfectClear)` → `[genGarbage, remGarbage]` |
| `GarbageGrid` | not emitted as a distinct function — folded into `fixPiece`'s materialization (§4-T7c) |
| `NewMainGridGameoverState` | not emitted — folded into `fixPiece`, sets `this.s6.s1.mg`/`this.s6.gameover` directly |
| `ValidHoles` | checked per-call, at each `holesFn(y)` invocation — throws, uncaught (§4-T7h) |
| `SendMessages` | not emitted — `fixPiece` returns only a boolean; `controller.js` reads `this.remGenGarbage`/`this.gameoverView[myIndex]` after the call to construct wire messages itself (§15.3) |
| `FixPiece` | `Machine.fixPiece(bagNew, holesFn)` |
| `ReceiveMessage` | split into three methods, no shared dispatch (§4-T7e): `receiveGarbage(amount)`, `receiveGameover(from)`, `receiveDisconnect(from)` |
| `DisconnectPlayer` | no `Machine` method (§4-T7f) |
| `NoticeDisconnection` | `Machine.noticeDisconnection()` |
| `FallStep` | `Machine.fallStep(bagNew, holesFn)` |
| `HoldPiece` | `Machine.holdPiece(bagNew)` |
| `RotateKickPiece` | `Machine.rotateKickPiece(cw)` |
| `DropPiece` | `Machine.dropPiece(bagNew, holesFn)` — relocate via `T1Eng.newPieceYXState`, then call `fixPiece` (§4-T7i), not `this.s6.dropPiece` |
| `Event`, `Next` | implicit (controller dispatch + method calls) |
| `NoWinner`, `Playing`, `ViewSound`, `MessageSound`, `NoSelfMessage`, `LastMessagesGameoverDisconnect`, `TargetNotSelf`, `TargetNotGameover`, `Gameover`, `Correct` | `proofs.md` only |
| `SelfViewAccurate` | also asserted at runtime, `checkInvariants` (§6.11) — not `proofs.md`-only |
| `OtherS6Unchanged`, `GameoverMonotone`, `GameoverViewMonotone`, `DisconnectedMonotone`, `DisconnectedViewMonotone`, `CorrectStep` | `proofs.md` only |
| `fₑ`, `fₛ`, `RefineT6`, `NoRemGarbage`, `NoMaterializedGarbage` | `proofs.md` only |

## 4. Per-definition translation rules

- **§4-T7a. Derivation.** `PlayerCount = Player.length`, `PlayerNext` as above,
  `Host = Player[HostIndex]`. `checkAxioms` asserts `PlayerCount > 1` and
  `0 <= HostIndex < PlayerCount`.

- **§4-T7b. View functions take arrays explicitly, no observer index.** A `Machine`
  only ever evaluates its own `gameoverView`/`connectedView`; `playingView`/
  `winnerMulti`/`nextTarget` take those arrays as plain arguments.

- **§4-T7c. Materialization** (`mg` array: row `0` = bottom). `this.s6.fixPiece
  (bagNew)` is called first (full T6 semantics — score, level, hold,
  `clearedLines`, `perfectClear`, and its own `mg`/`gameover` from the piece
  placement alone). If it returns `false`, `fixPiece` returns `false` immediately,
  nothing below runs. Otherwise, unconditionally (no `PlayerCount = 1` branch —
  never reached, §0):
  ```
  effRem = min(remGarbage, HM)   // remGarbage is unbounded (garbage has no cap) —
                                   // clamped so array indices stay in range (see below)
  gameover' = this.s6.gameover
  if (!gameover' && remGarbage > 0) {
    if (remGarbage >= HM) {
      overflow = true   // pushes the entire board off — no scan needed
    } else {
      // must read the top rows before the shift below overwrites them
      overflow = T1Eng.occ test on any cell in rows [HM - remGarbage, HM) of
                 this.s6.s1.mg — not plain truthiness (mg cells are false | Piece,
                 t1/implementation.md D1; `occ(c) = c !== false`)
    }
    gameover' = overflow
  }
  // shift always runs, regardless of gameover' — the stored grid always
  // reflects materialization, whatever caused gameover'
  if (effRem > 0) {
    for (let i = HM - effRem - 1; i >= 0; i--) this.s6.s1.mg[i + effRem] = this.s6.s1.mg[i];
    for (let y = 0; y < effRem; y++) this.s6.s1.mg[y] = garbageRow(holesFn(y), WM);
    this.s6.updateShadowY();
  }
  if (!gameover') {
    gameover' = intersect(ForbiddenGrid, FY, FX, this.s6.s1.mg, 0, 0);   // on the new mg
  }
  this.s6.gameover = gameover'
  ```
  The `this.s6.updateShadowY()` call is necessary only inside the `effRem > 0`
  branch: `this.s6.fixPiece(bagNew)` (called first, above) already spawned the
  new piece and computed `gy` (T5's `updateShadowY`) against the
  pre-materialization grid; splicing garbage rows in just now shifted that
  grid out from under it, leaving `gy` stale until recomputed against the new
  `this.s6.s1.mg`.

  `remGarbage` is unbounded — `garbage` accumulates via `receiveGarbage` with no
  cap, so it can exceed `HM`. The Rocq `Grid` algebra handles this for free
  (unbounded function, cropped to box at the end); the array representation
  needs `effRem` explicit, or the overflow scan reads a negative index and the
  overwrite loop silently grows the array past `HM`.

  Short-circuit: if `this.s6.gameover` is already `true`, neither the scan nor the
  `intersect` check runs — the shift/overwrite still runs unconditionally, only
  the boolean computation is skipped. The shift loop runs in **decreasing** `i`,
  not increasing: a destination index (`i + remGarbage`) can coincide with a later
  source index, so increasing order would read an already-overwritten row.

- **§4-T7d. `remGenGarbage` is a field**, set every `fixPiece` call, read by the
  controller immediately after — same pattern as `clearedLines`/`combo`.

- **§4-T7e. `ReceiveMessage` splits into three methods, no shared dispatch** — the
  wire layer already knows the message's tag. `receiveGarbage(amount)` takes no
  `from` (sender-agnostic `+=`). `receiveGameover(from)`/`receiveDisconnect(from)`
  require `from` (update the specific sender's view slot, check
  `target === from` for redirect). In `T7.v`, all three are gated on
  `connected s pl`; none of the three JS methods checks anything of the kind —
  `connected` has no JS counterpart (§6.9), so the caller only invokes them when
  the local link is up. The gate is enforced by not calling, not by an internal
  check.

- **§4-T7f. `DisconnectPlayer` has no `Machine` method.** Its abstract effect
  touches only `connected`/`messages` — neither is `Machine` state. Two
  realizations, both outside `model.js`:
  - `pl = Host`: no code runs. The host process being gone is the fact itself.
  - `pl ≠ Host`: realized by the host's controller, on detecting its own link to
    `pl` has failed — it forwards a `DISCONNECT` notification to every other
    player (§15.4). Never realized by `pl`'s own machine or by recipients'.

- **§4-T7g. `NoticeDisconnection`** — `Machine.noticeDisconnection()`, called by a
  player's own controller on locally detecting its own link-to-host has failed
  (heartbeat timeout or explicit close), regardless of cause (host crash or this
  player's own link specifically). Flips `this.connectedView[myIndex]` only.

- **§4-T7h. `holesFn`** — fresh, per-call memoizing function
  (`makeHolesFn(w)`), not persistent across calls (unlike `bagsFn`): `GarbageGrid`
  always indexes rows from `0` per materialization event. Each `holesFn(y)` result
  is asserted in `[0, w)` at the point of use; throws, uncaught, mirroring
  `assertPieceSet`'s role for `bagNew`.

- **§4-T7i. `DropPiece`** — realized as
  `T1Eng.newPieceYXState(this.s6.gy, s1.px, s1)` applied to `this.s6.s1` (same
  field copy `t5/model.js`'s own `dropPiece` uses, reached via `T6.Machine`'s
  inherited flattened `s1` accessor and `gy` field — no patch needed to
  `t5/model.js`/`t6/model.js`), then `this.fixPiece(bagNew, holesFn)` — T7's own
  `fixPiece`, not `this.s6.dropPiece`, so materialization isn't bypassed on a
  hard drop. `T6Eng.T4Eng.assertPieceSet(bagNew)` checked first, before any
  mutation, mirroring `t5/model.js`'s own defensive check.

## 5. Free functions

`playingView(gameoverView, connectedView, pl2)`,
`winnerMulti(gameoverView, connectedView, myIndex)`,
`nextTarget(playing, self, pl)`,
`generatedGarbage(clearedLines, perfectClear)`,
`genRemGarbage(garbage, clearedLines, perfectClear)`.
`makeHolesFn(w)` is not among these — it is controller-side (§15.7), not a
`model.js` definition.

`garbageRow(hole, w)` — one materialized garbage row, used by `fixPiece`'s
materialization step (§4-T7c): `w` cells, occupied except at column `hole`. No direct
`T7.v` counterpart (`GarbageGrid`'s per-row content, realized directly for the array
representation instead of as a `Grid` record). Occupied cells are stamped `'garbage'`,
not bare `true` — `mg`'s cell type at this layer is `false | Piece | 'garbage'`
(`t1/implementation.md` D1, widened here); `view.js`'s `pieceColor[cell] ?? gray`
fallback already renders an unrecognized key like `'garbage'` distinctly, with no
special-casing needed there. `garbageRow` is internal to `model.js` — not part of
its returned object (§7).

## 6. `T7.Machine`

### 6.1 Constructor — `Init bags H` (§4-T7a)

```js
constructor(myIndex, bagsFn) {
  if (CHECK_AXIOMS) checkAxioms();
  this.myIndex = myIndex;
  this.s6 = new T6Eng.Machine(bagsFn);
  this.garbage = 0;
  this.target = PlayerNext(myIndex);
  this.gameoverView = Array(PlayerCount).fill(false);
  this.gameoverView[myIndex] = this.s6.gameover;
  this.connectedView = Array(PlayerCount).fill(true);
  this.remGenGarbage = 0;
}
```

### 6.2 `movePiece`/`rotatePiece`/`holdPiece`/`rotateKickPiece`

Gated by `! winnerMulti(this.gameoverView, this.connectedView, this.myIndex)`;
delegate to `this.s6`.

### 6.3 `fixPiece(bagNew, holesFn)` — §4-T7c/d

### 6.4 `fallStep(bagNew, holesFn)`

Same guard; tries `movePiece(-1, 0)`, else `fixPiece(bagNew, holesFn)`.

### 6.5 `dropPiece(bagNew, holesFn)` — §4-T7i

### 6.6 `noticeDisconnection()` — §4-T7g

### 6.7 `receiveGarbage(amount)` / `receiveGameover(from)` / `receiveDisconnect(from)` — §4-T7e

### 6.8 Read-through getters

`level`/`combo`/`perfectClear`/`totalClearedLines`/`score`/`gameover` are
promoted as live getters from `t5/model.js` onward (confirmed against
`t5/model.js`'s own getter list, inherited unchanged through `t6/model.js`) —
`T7.Machine` redeclares each as `get <field>() { return this.s6.<field>; }`.
`hold`/`next_` are not promoted anywhere in the tower; nothing needs them
live, only via `snapshot()`, which reaches them correctly through
`T6Eng.snapshot` regardless.

`mg`/`clearedLines`/`p`/`py`/`px`/`pr` are T1-level-only fields, never promoted
above T1 — reachable solely via the flattened `this.s6.s1` accessor:
`get mg() { return this.s6.s1.mg; }`, and likewise for `clearedLines`/`p`/`py`/
`px`/`pr`. `p`/`py`/`px`/`pr` are promoted specifically at `T7.Machine` (not at
any lower level) so `broadcastState()` (`controller.js`) can read them live
without constructing a full `snapshot()` — which spreads through the whole
T1–T6 chain and copies fields that call never uses — just to discard most of
it; safe because the only consumer, `rawSend`'s `stringify → encode → deflate`
pipeline, runs synchronously start to finish and none of its steps mutate
what they're given, unlike `view.js`, which is why `snapshot()` wraps `mg`
read-only in the first place. `gy` (a T5-level field, `this.gy` there, not a
getter) is
likewise promoted at `T7.Machine` as `get gy() { return this.s6.gy; }`, for
the same `broadcastState()` reason.

### 6.9 `snapshot(machine)`

```js
function snapshot(machine) {
  return {
    ...T6Eng.snapshot(machine.s6),
    garbage: machine.garbage,
    target: machine.target,
    gameoverView: machine.gameoverView.slice(),
    connectedView: machine.connectedView.slice(),
    remGenGarbage: machine.remGenGarbage,
    myIndex: machine.myIndex,
  };
}
```

### 6.10 What is not stored: `connected`, `messages`

Neither is a `Machine` field. `connected` is a fact about reality — a `Machine`
represents only its own `connectedView[myIndex]`, maintained by
`noticeDisconnection`. `messages` is the physical relay (WebRTC channel state via
the host); nothing in `model.js` buffers or queues it.

### 6.11 `checkInvariants`

`checkInvariants(s, message, isOccupied = c => Piece.includes(c) || c === 'garbage')`
— T7 is the *one* layer whose own default isn't just `c => Piece.includes(c)`: it's
the layer that introduces the `'garbage'` sentinel (via `garbageRow`, §5), so its own
`mg` can legitimately contain cells no lower layer's default would accept. Delegates
to `T6Eng.checkInvariants(s.s6, message, isOccupied)` — every layer between `T1` and
here threads this parameter through untouched (`t2`–`t6/implementation.md` §6.9-ish
entries), so this override actually reaches `T1Eng.typeOK`, where cell types are
checked; asserts `garbage >= 0`, `0 <= target < PlayerCount`,
`gameoverView.length === connectedView.length === PlayerCount`.

`checkAxioms` additionally asserts `Piece.every(p => p !== 'garbage')` — `'garbage'`
is reserved at this layer the same way `false` is reserved at `T1`'s (D1/D8):
neither may collide with a genuine `Piece` id.

`checkInvariants` also asserts `s.s6.gameover === s.gameoverView[s.myIndex]` —
`SelfViewAccurate`, checked at runtime here rather than left to `proofs.md`
alone (contrast the naming-map §3 entry, which lists it among the Rocq
invariants realized only as a proof obligation elsewhere in this tower;
`T7.v` is the layer that actually stores a `gameoverView` to check it
against).

## 7. `model.js` exported function

```js
export function T(
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX, NextLen,
  Player, HostIndex,
  MAX_SAFE_INTEGER = Number.MAX_SAFE_INTEGER,
) {
  const T6Eng = T6(Piece, InitialMainGrid, ForbiddenGrid, RotGrid, InitialY, InitialX,
                    PW, FY, FX, NextLen, MAX_SAFE_INTEGER);
  const T1Eng = T6Eng.T1Eng;
  const PlayerCount = Player.length;
  const Host = Player[HostIndex];
  const PlayerNext = (i) => (i + 1) % PlayerCount;
  // Player values are plain indices — compared with === directly, no PlayerEqb.

  class Machine { ... }   // §6

  return { ...free functions (§5), T6Eng, T1Eng, checkAxioms, checkInvariants, Machine, snapshot };
}
```

`checkAxioms` asserts `0 <= HostIndex < PlayerCount`. `Player`/`HostIndex` are the
two required parameters not present in T1–T6's signatures (§0.3).

## 8. `proofs.md` (scope)

The target: **the JS system refines `T7.v`.** "The JS system" is model.js +
controller.js + network, not `model.js` alone: some `T7.v` events (`Disconnect`)
have no realization inside any `Machine` at all (§4-T7f), so `α` and the
per-event argument both span all three layers.

1. **Scope.** Safety only.
2. **`α : Σ → T7.State`**, where `Σ` is the full JS system configuration: every
   player's own `T7.Machine` instance, every player's own `controller.js`
   instance (including the host's relay/detection bookkeeping — §15.4), and the
   physical network (WebRTC channels/buffers). `α` is a function in the
   informal metatheory of this file, not code in either language — `α σ` is a
   `T7.State`. Per field, in Rocq application order, following the same
   convention as `t1/proofs.md`–`t6/proofs.md`: primitive fields (numbers,
   booleans) are used directly, no notation; structured fields go through the
   correspondence function that already exists for them (here, `α_T6`).
   - `s6 α(σ) pl = α_T6(σ.machines[pl].s6)`
   - `garbage α(σ) pl = σ.machines[pl].garbage`, similarly `target`,
     `gameoverView`, `connectedView`.
   - `connected α(σ) pl` — defined directly on `σ`'s network/controller state
     (no existing correspondence function to invoke, unlike `s6`): true iff
     `pl`'s link to the host is physically up. Not read off any `Machine` field
     (§6.9).
   - `messages α(σ) from to` — the actual in-flight message list from `from`
     to `to` in `σ`'s network state (buffered at the host relay for a star hop,
     or in transit on the direct channel).
3. **Move/Rotate/Fall/Hold/RotateKick, non-materializing Fix — full-use transfer**,
   per player, exactly as T1–T6's own arguments (each stays entirely within one
   `Machine`).
4. **Materializing Fix — no-use, full argument, per player.** Cite the
   `NoRemGarbage`-collapse argument from `T7Proofs.v` verbatim (unconditional
   `T1.Gameover` on any `T1.FixPiece` output; `TypeOK`-derived box computation) —
   the JS shift-based materialization (§4-T7c) realizes the same crop.
5. **Drop — composite, no separate argument.** The relocation step is a trivial
   no-use transfer (mirrors T5's own classification of that step); the call to
   `this.fixPiece` afterward is covered entirely by 3/4 above — nothing new to
   argue.
6. **`receiveGarbage`/`receiveGameover`/`receiveDisconnect` — cross-machine
   argument, not a single-`Machine` one.** Each realizes one `T7.v` `Receive`
   event: a queue pop on the sender/receiver pair. `T7.v`'s `messages` queues
   (§0.3 of `T7.v`'s own header) exist precisely so this is an ordinary,
   in-order step-by-step argument, not a linearizability/reordering one — the
   queue *is* "not yet delivered"; there is nothing left to reorder. Show: the
   corresponding wire message is enqueued exactly once, by exactly one sender
   action (`fixPiece`'s `remGenGarbage`/`gameoverView[myIndex]` transition, or a
   host-relayed `DISCONNECT`, §4-T7f); the queue only shrinks, never grows,
   independent of any other player's concurrent steps (`OtherS6Unchanged`'s
   `T7.v` counterpart) — needed so the argument doesn't have to account for
   interleaving with unrelated players' actions.
7. **`noticeDisconnection` — stutter w.r.t. `s6`, single-`Machine`.** Trigger
   condition (own link-to-host failure, locally detected) is a controller fact,
   not something `α` needs to reconstruct — only the resulting `connectedView`
   transition is compared.
8. **`Disconnect`, `pl = Host` — realized by nobody, not by `α` of any JS step.**
   Argue directly against reality: the host process ceasing to exist *is*
   `connected := λ _, false` becoming true of the corresponding `T7.State`; no JS
   trace step needs to map onto it for `α` to remain sound at the next state a
   real step does occur.
9. **`Disconnect`, `pl ≠ Host` — realized by the host's controller**, not by any
   `Machine`. Argue that the host's detection-and-relay action (§4-T7f) reproduces
   exactly `DisconnectPlayer pl`'s effect on `connected`/`messages` — again no
   `Machine`-level `α` transfer, since neither field lives in one.

## 9. Tests (`tests/`)

- `testInstance.js` — fixture `Player = [0, 1, 2]`, `PlayerCount = 3`.
- `oracle.js` — reuses T6's oracle for `s6`; hand-rolls garbage/target/view logic
  independently.
- `model.unit.test.js` — golden vectors: garbage generation/cancellation/
  materialization/overflow/forbidden-zone-after-materialization; `dropPiece`
  reaching the same materialized result as an equivalent `fallStep` sequence
  ending in a fix; target round-robin (3-player trace, `T7.v`'s own worked
  example); each `receiveX` method's field update; `noticeDisconnection`.
- `model.properties.test.js` — `winnerMulti`/`nextTarget` never return `self`
  except the no-alternative case; differential oracle over every snapshot field.
- `model.fuzz.test.js` — multi-instance harness: several `Machine`s in one
  process, each one's outgoing values wired directly into others'
  `receiveGarbage`/`receiveGameover`/`receiveDisconnect` calls, no transport —
  exercises the full event set including disconnect/notice without networking.

## 10. Acceptance oracle

The sole correctness criterion is refinement (§8): the JS system refines `T7.v`.
The checks below are necessary, not sufficient — passing all of them does not
itself establish refinement; failing any one of them does establish its absence.

1. Every `T7.v` definition with a §3 mapping is realized; every "not emitted"/"no
   `Machine` method" entry is absent from `model.js`.
2. `connected`/`messages` are not fields anywhere in `model.js`.
3. `fixPiece` calls `this.s6.fixPiece(bagNew)` first, unconditionally runs §4-T7c's
   shift/overwrite after (no `PlayerCount = 1` branch), short-circuits the
   overflow/`intersect` checks but not the shift/overwrite when `this.s6.gameover`
   is already `true`, and returns `false` with zero mutation if the inner call
   fails.
4. `dropPiece` calls `this.fixPiece` (T7's own), never `this.s6.dropPiece`.
5. `receiveGarbage` takes no `from`; `receiveGameover`/`receiveDisconnect` do.
6. No method checks `connected` internally (it doesn't exist to check).
7. `holesFn` is constructed fresh per `fixPiece`/`fallStep`/`dropPiece` call site,
   never reused across calls.
8. `tests/` passes: unit + fuzz fully; properties under `fast-check` when
   installed.

## 11. Instantiation (`instance.js`)

```js
export * from '../t6/instance.js';
```

`Player`/`HostIndex` are not instance.js constants — supplied to `T(...)` by
`controller.js` once the roster is frozen at `START` (§0.3, §15.1).

## 12. Generator determinism rules

Inherit predecessors' "reuse over restatement" verbatim.

## 13. `instance.js` parameters

None. See §11.

## 14. `view.js`

### 14.1 Public API

```js
export function render(canvas, constants, snapshot, pieceColor, banners, opponents, target) { ... }
```

`opponents`: `[{ playerIndex, name, mg, p, py, px, pr, gameover, connected }]`,
controller-supplied from `STATE`/`GAMEOVER`/`DISCONNECT` messages — never
through `snapshot()`. `target`: the local `Machine`'s own `target` field (or
`null` before a `t7.Machine` exists), used to highlight the current garbage
target in the mini-grid strip (§14.2).

### 14.2 Mini-grid strip

Fixed-size region of the canvas, reserved regardless of `PlayerCount`; individual
mini cell size computed to tile `opponents.length` entries in rows × columns
within that region — more opponents shrink each mini, never grow the strip.
Fixed cells use `pieceColor[cell] ?? gray` per cell (same fallback convention as
the main board's `drawGrid` — an unrecognized cell, e.g. a `'garbage'` sentinel,
renders gray automatically, no special-casing needed), except while a mini is
dead (gameover or disconnected, below), which overrides to a flat status color
regardless of cell content — that gray signals connectivity, not block identity.
Forbidden-zone tint kept; no grid lines, no ghost, no next/hold. Labeled by
`name`.

A mini renders as a flat, uniformly-grey placeholder before that player's `mg`
is known (no `STATE` received yet). Once `mg` is known, a mini is drawn dead —
cells in flat grey rather than `pieceColor` — once that player's `gameover` is
true or once `receiveDisconnect` has been received for them (`opp.connected
=== false`); either condition alone is sufficient.

With more than one opponent, the mini whose `playerIndex` equals `target` is
outlined with a thicker, red border instead of the ordinary grey one — the
current garbage target is otherwise ambiguous. With exactly one opponent no
border override is drawn: the target can only ever be that one player, so a
border would be redundant.

### 14.3 Garbage gauge

Vertical bar at `x = constants.PANEL_PX - gaugeWidth`, growing bottom-up, one
`cellSize`-height segment per unit of `snapshot.garbage`, clamped at `HM`, single
flat color.

### 14.4 Call order

T6's existing order, then the garbage gauge, then the mini-grid strip.

### 14.5 Lobby

DOM overlay, not canvas (§15.8).

## 15. `controller.js`

### 15.0 Screens

One DOM overlay state machine, `<canvas>` shown only in `S7`/`S8` (gameplay).

| screen | shown | actions | on action |
|---|---|---|---|
| `S1` Mode Select | "Single Player" / "Multi Player" buttons | click | SP → `t6/controller.js`'s `main()`, `t7` never loaded. MP → `S2` |
| `S2` Role Select | "Host" / "Join" buttons | click | Host → `S3`. Join → `S4` |
| `S3` Host Lobby | name field; "Add connection" button; per-pending-connection: offer paste-box + "Generate answer" button + generated answer (read-only, copy); joiner list (names, post-`JOIN`); "Start" button, enabled once joiner list `≥ 1` | paste offer, generate answer, `Start` | `Start` → freeze roster, send `START` to all, `HostIndex = 0`, own transition to `S7` |
| `S4` Join Screen | name field; own generated offer (read-only, copy); "paste host's answer" box; "Connect" button | `Connect` | apply pasted answer → connection opens → send `JOIN(name)` → `S6` |
| `S5` Rejoin | (rematch only) name pre-filled, no SDP exchange (existing connection reused) | automatic | send `JOIN(name)` over existing connection → `S6` |
| `S6` Waiting Room (pre-`START`) | `t6.Machine` filler game; joiner-name list from `PLAYERS`; "waiting for host" text | ordinary SP input | `START` received → `S7` |
| `S7` Gameplay | `t7.Machine`; mini-grid strip + garbage gauge (§14) | ordinary game input | own `gameover` → `S8`. `winnerMulti(self)` → `S9` |
| `S8` Mid-match Filler | `t6.Machine` filler game; mini-grid strip stays live (`t7.Machine` kept alive headless, §15.2); own link failing → `S10` | ordinary SP input | `findWinner() ≠ null` → `S9` |
| `S9` Winner Screen | "You win" (if `findWinner() = myIndex`) or "Winner: `<name>`"; "Rematch" button; "Leave" button | `Rematch` / `Leave` | Rematch, host → `S3` (fresh lobby, connections reused for rejoiners, still accepts brand-new ones). Rematch, joiner → `S5`. Leave, joiner → sends `LEAVE` to host (§15.1), → `S1`. Leave, host → `S1`, no message (the host process itself is what every other client's own `DisconnectPlayer pl = Host` case reasons about, §4-T7f) |
| `S10` Host Lost | "Connection to host lost."; "Return to menu" button | click | → `S1` |

`S8` is not a distinct value of the `screen` variable — `showScreen('S8')` is
never called. It is `screen === 'S7'` with `inMidMatchFiller` set:
`activeMachine()` branches on `inMidMatchFiller` first, ahead of the
`screen === 'S7'` check, so the filler `t6.Machine` drives input while `screen`
itself stays `'S7'`. This is why `processGameInput`'s own `screen === 'S6' ||
screen === 'S7'` gate (and the DOM overlay, hidden for both) needs no separate
`'S8'` case.

`S10` is reached from `S6`/`S7`/`S8` whenever `noticeDisconnection()` fires while
`findWinner()` is still `null` at that moment — a resolved winner takes `S9`
instead, even if the connection is lost immediately after. Mini-grids in
`S7`/`S8` grey out a player on either "no `STATE` received yet" or
"`receiveDisconnect` received for that player" (§14.2).

### 15.1 Roster and lifecycle

`JOIN` (host only): append `{ conn, name }` to `playerData`; reply `PLAYERS` to
every connected player, including the new one. `PLAYERS`: every client rebuilds
its local `playerData`/roster from the payload. `START`: no payload; freezes the
roster into `Player` (index = `playerData` position), constructs
`new T7Eng.Machine(myIndex, bagsFn)` via `T(..., Player, HostIndex)`, exits the
waiting room.

`LEAVE` (host only, sent by a joiner clicking "Leave" on the winner screen,
`S9`): evicts the sender's slot from `playerData` outright — splicing it out
and rebinding every later slot's `dc.onmessage` closure to its new, shifted
index — then re-broadcasts `PLAYERS` so every remaining client's roster/index
stays correct. Unlike a mid-match disconnect (§15.4), a `LEAVE` slot is not
kept around as a phantom for the next `startMatch()`.

### 15.2 Waiting room

Two entry points, one implementation: pre-`START`, and a player's own
`gameover` mid-match. Both instantiate a `t6.Machine` and reuse `t7/controller.js`'s
own input/fall-timer code — not `t6/controller.js`'s `main()`. During
mid-match waiting, the real `t7.Machine` is kept alive, headless, still fed
`receiveGarbage`/`receiveGameover`/`receiveDisconnect`, so `winnerMulti` stays
current. No waiting room after the match ends — the winner screen offers only
rematch (re-send `JOIN`) or not.

### 15.3 Message dispatch (star topology, host-relayed)

| message | payload | handler |
|---|---|---|
| `STATE` | `{ from, to: null, mg, p, py, px, pr, gameover }` | overwrite `opponents[from]` |
| `GARBAGE` | `{ from, to, amount }` | `machine.receiveGarbage(amount)` |
| `GAMEOVER` | `{ from, to: null }` | `machine.receiveGameover(from)` |
| `DISCONNECT` | `{ from, to: null }` | `machine.receiveDisconnect(from)` |
| `LEAVE` | `{ from }` | host evicts `from`'s slot (§15.1) |

Every message is `tag`-wrapped with the current match-generation counter (§15.5)
before sending, except `LEAVE` itself, `JOIN`, and `PLAYERS`, which are untagged
(§15.5). `to` is `null` on every broadcast message; only `GARBAGE` ever carries a
real recipient index, since it is the one message routed to a single target
(the sender's own `target` field) rather than relayed to everyone.

On the wire, every message is `JSON.stringify`'d then `deflateSync`'d
(`rawSend`) and, on receipt, `inflateSync`'d then `JSON.parse`'d (`decodeMsg`)
— both synchronous, so message order and content are unaffected; the table
above describes the payload before this encoding.

`STATE`: sent unconditionally right after a successful `Fix`; otherwise at
minimum `3` Hz — a single timer, always re-armed for `1/3` s from the last send
(natural tick or `Fix`), so `Fix`-triggered sends aren't delayed. First `STATE`
sent immediately at `START`.

### 15.4 Host responsibilities

Relay `STATE`/`GARBAGE`/`GAMEOVER` between all connected players. Detect an
ordinary player's disconnection via either of two paths — the peer
connection's own `connectionState` reaching `failed`, or a `10` s silence on
that player's `STATE`/`JOIN` heartbeat (`lastHeard`) — and on either, apply
`DISCONNECT` to the host's own view and broadcast it to every other player
immediately (there is no message buffer to flush: each `DISCONNECT` is
constructed and sent directly at detection time). Track
`declaredDisconnected` per player to prevent a duplicate broadcast if both
paths fire for the same player. No action for the host's own loss (§4-T7f).

### 15.5 Match-generation counter

Incremented once per `START` (including rematch). Tagged on `STATE`/`GARBAGE`/
`GAMEOVER`/`DISCONNECT`; receivers discard any message not matching their current
counter. `JOIN`/`PLAYERS` untagged.

### 15.6 Rematch

Host's post-game screen is its pre-match host screen. A joiner's rematch button
re-sends `JOIN` over the existing connection.

### 15.7 Randomness

`shuffleBag()` and `makeHolesFn(w)` are both controller-side; `makeHolesFn` is
constructed fresh at each `fixPiece`/`fallStep` call site.

### 15.8 Lobby — DOM overlay

Real `<button>`/`<textarea>` elements over the canvas, for SDP offer/answer
copy-paste and roster/name entry. Canvas is reserved for gameplay only. Gamepad
navigates the overlay via a focus index driven by the existing input-polling
loop (`button 0` → `.click()` on the focused element).

### 15.9 `index.html`

Canvas plus a DOM overlay container, toggled visible/hidden by lifecycle state
(lobby, waiting room, winner screen use the overlay; gameplay hides it).
