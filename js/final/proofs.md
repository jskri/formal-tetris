# proofs.md — refinement proof, `final/*.js ⊨ T7.v`

Not a fresh derivation. `final/` introduces no `model.js` of its own — every
import of `T` in `final/controller.js` and `final/sp_controller.js` resolves to
`../t7/model.js` or `../t6/model.js` unchanged (§2). So the state type, `α`,
`Correct`, and every per-event argument are exactly `t7/proofs.md`'s (multi-
player) or `t6/proofs.md`'s (single-player) — not re-derived here. This file's
own obligation is narrower: catalogue everything `final/` adds over `t7/`'s and
`t6/`'s own controllers, and show each addition is *no-use* with respect to the
refinement mapping — it never calls a `Machine`-mutating method beyond the set
`t7/proofs.md`/`t6/proofs.md` already cover, in an order or with arguments that
differ from what's already proven there.

## 0. Result

No obstruction found. `final/`'s entire new surface (`view.js`, `sound.js`,
`highscores.js`, and `controller.js`'s/`sp_controller.js`'s own added local
state and call sites) is either read-only against already-computed `Machine`
state, or a side effect (audio, `localStorage`, DOM/canvas) entirely disjoint
from `Σ`. No new call to a mutating `Machine` method is introduced; no existing
one is removed, reordered relative to another mutating call, or given
different arguments. `t7/proofs.md`'s and `t6/proofs.md`'s own conclusions
(including the accepted, bounded divergence at `t7/proofs.md` §5a — ported
into `final/controller.js` unchanged, §5 below) transfer without modification.

## 1. Scope

Safety only, inherited from `t7/proofs.md` §1 / `t6/proofs.md` §1. Nothing in
`final/` touches liveness either way.

## 2. `model.js` — unchanged, not present in `final/`

```
$ grep -rn "from '.*model.js'" final/*.js
final/controller.js:    import { T } from '../t7/model.js';
final/controller.js:    import { T as T6 } from '../t6/model.js';
final/sp_controller.js: import { T } from '../t6/model.js';
```

No `final/model.js` exists. `final/controller.js`'s `T7.Machine`/`T6Eng.Machine`
and `final/sp_controller.js`'s `T6.Machine` are the *same classes* `t7/proofs.md`
and `t6/proofs.md` already prove refine `T7.v`/`T6.v` — not subclasses, not
wrapped, not monkey-patched. This is the same style of argument
`t6/proofs.md` §2 makes for `T6.Machine` inheriting `T5.Machine` unchanged:
no projection lemma is needed for any `Machine` method beyond "this is
literally the class already proven," because it literally is.

`final/instance.js` is `export * from '../t7/instance.js';` — unchanged, same
argument as `t7/implementation.md` §11.

## 3. `final/controller.js` — multiplayer, new surface catalogued

Diffed against `t7/controller.js` (already proven, `t7/proofs.md`). Every
addition falls into one of the categories below (§3.1–§3.6); most are argued
once, generically, rather than per call site — §3.4 and §3.6 are the two
that need checking call site by call site.

### 3.1 `final/view.js` — read-only rendering, no `Machine` calls at all

`renderClearFlash`, `drawGarbageFlash`, `drawGameOverPartial` never import
`model.js`/`instance.js` (enforced by the same convention every `view.js` in
the tower follows) and take only plain data — a `snapshot()`, a raw grid
array, row indices, a progress float, a cell size — as arguments. None calls
any method on a `Machine`. They cannot affect `Σ`; they only draw pixels.
No-use, trivially — there is nothing here for `α` to even see.

### 3.2 `final/sound.js` — side-effecting, disjoint from `Σ`

`sfx.*`, `toggleMuted`, `isMuted` operate on a private, module-local
`AudioContext`/`muted` flag, imported by nothing in `model.js`/`instance.js`
and importing nothing from them. Every `sfx.X()` call site in
`final/controller.js` is placed strictly *after* the `Machine` call whose
outcome it reacts to has already returned (§3.4) — it reads no `Machine`
field and writes none. No-use: `Σ`, as `t7/proofs.md` §3 defines it, has no
audio component for this to touch.

### 3.3 New local state in `main()`'s closure

`clearAnim`, `garbageAnim`, `gameoverAt` are all new `let`-bound closure
variables — `t7/controller.js` has no lockout/timestamp gate on the filler's
restart at all (it restarts on the very next keypress after gameover);
`gameoverAt`/`RESTART_LOCKOUT_MS` add one. None of these three is read by
`α` — `t7/proofs.md` §3 defines `α` as a function of specific, named fields (`s6`,
`garbage`, `target`, `gameoverView`, `connectedView`, `connected`, `messages`);
adding fields to `Σ` that `α` never reads cannot change what `α` computes,
by construction — the same reasoning that lets `t7/proofs.md`'s own `Σ`
already include host relay/heartbeat bookkeeping (`declaredDisconnected`,
`lastHeard`, …) that most individual `T7.v` events never touch either.

`RESTART_LOCKOUT_MS`/`gameoverAt`'s only effect is delaying *when*
`enterWaitingRoom()` constructs a fresh `t6.Machine` for the mid-match filler
(`processGameInput`'s `!isT7 && m.gameover` branch, gated by `canRestart`).
The filler is explicitly outside `t7/proofs.md`'s own `T7.Machine`-level
argument (§0 there: single-player, i.e. the filler, is `t6/model.js`'s own
concern); delaying *when* a fresh `t6.Init` happens doesn't change that it
*is* one when it happens — `t6/proofs.md`'s own base case applies at whatever
wall-clock moment `enterWaitingRoom()` runs, unconditionally on timing.

### 3.4 Every new function's call sites, checked against the existing call set

`precomputeLock`, `onLocked`, `maybeAnimateGarbage` are the only new functions
that read `Machine` state (as opposed to `sfx`'s pure side effects). Checked
against every call site in `actionsFor`:

- `precomputeLock(py, px)` (`doFall`/`doDrop`) reads `getS1()` (`machine.s6.s1`
  or `machine.s1`) and calls `T6Eng.T1Eng.union`/`isFullLineb` — both already-
  exported, side-effect-free query helpers (`t1/model.js`), not new primitives
  invented here. Called *before* the mutating `movePiece`/`fixPiece`/
  `dropPiece` call in the same function, on the *pre*-mutation `s1` — this
  mirrors exactly what `fixPiece`'s own internal materialization logic
  computes from, just recomputed by the caller for animation purposes. A
  read before a write cannot itself be the write; the mutating call
  immediately following it is unchanged from `t7/controller.js`'s own
  (`machine.movePiece(-1, 0)`, `machine.fixPiece(...)`, `machine.dropPiece(...)`
  — same arguments, same order).
- `onLocked` and `maybeAnimateGarbage` are only ever called *after* the
  mutating call they react to has already returned `true` (`if (fixed) {
  onLocked(...); maybeAnimateGarbage(...); }`, both inside `doFall`/`doDrop`,
  strictly following the `machine.fixPiece`/`machine.dropPiece` call). Neither
  calls back into `machine`. `maybeAnimateGarbage` calls
  `t7eng.genRemGarbage(garbageBefore, s1.clearedLines, t7machine.s6.perfectClear)`
  — the same pure, already-exported free function (`t7/model.js` §5,
  `t7/implementation.md`) `fixPiece` itself calls internally, given the same
  post-mutation `clearedLines`/`perfectClear` `fixPiece` itself just computed
  from — reproducing, not altering, what already happened.
- Every `ACTIONS.X.effect` (`LEFT`/`RIGHT`/`HOLD`/`doRotate`) calls exactly
  the same `machine.<method>(...)` `t7/controller.js` calls, with an `sfx.*()`
  call inserted strictly after, gated on the same fired/not-fired boolean the
  call itself returns. No `machine` call's argument, guard, or position
  relative to another `machine` call changed.

`getS1()` itself is a read-only accessor (`isT7 ? machine.s6.s1 :
machine.s1`) — `machine.s6.s1` already exists as `T7.Machine`'s own flattened
accessor chain (`t7/implementation.md` §6.8); `getS1` adds no new field, only
a two-way branch over an existing one.

### 3.5 The fail-fast networking fix — identical port, already covered

`sendToHost`/`sendToPlayer`/`declarePlayerDisconnected`/`rawSend` in
`final/controller.js` are a verbatim port of the same functions in
`t7/controller.js`, fixed in the same commit this file's counterpart records
(`t7/proofs.md` §5a: the `FixPiece`-message-gate corner case is an accepted,
invariant-harmless divergence, not a re-derived argument here). One addition:
`sfx.disconnect()` inside `applyIncoming`'s `'DISCONNECT'` branch, placed
*after* `t7machine.receiveDisconnect(msg.from)` has already returned — no-use,
§3.2.

### 3.6 `activeMachine()`'s new `screen === 'S9'` branch — render path only

```js
function activeMachine() {
  if (screen === 'S9') return t7machine; // frozen at whatever it held when
                                          // gameover fired — S9 is the
                                          // match result, never the filler
  if (inMidMatchFiller) return t6machine;
  ...
```

New relative to `t7/controller.js`. Matters only for `frame()`'s own
`snap = t7eng.snapshot(m) / T6Eng.snapshot(m)` read (which machine's state gets
*drawn* on the winner screen) — `frame()`'s own dispatch never routes input to
`activeMachine()`'s result while `screen === 'S9'`
(`processGameInput`/`onTick` only run for `screen === 'S6' | 'S7'`, and
`maybeEnterWinnerScreen` calls `stopGravity()` before `showScreen('S9')`
regardless). No-use: this branch changes what gets rendered, never what gets
mutated.

## 4. `final/sp_controller.js` — single-player, new surface catalogued

Wraps `t6/model.js`'s `Machine` directly (§2) — `t6/proofs.md`'s refinement
applies unconditionally to any correctly-driven instance, independent of
which controller drives it (no controller.js discussion exists in
`t6/proofs.md` at all, by construction: `T6.v` has no network layer, so the
refinement obligation lives entirely at the `Machine` level).

- `precomputeLock`, `onLocked`, `attemptFall`, `attemptDrop` mirror §3.4's
  pattern exactly: read-before-write (`precomputeLock`, from `machine.s1`,
  before `machine.fallStep`/`machine.dropPiece`), react-after-write
  (`onLocked`, after the same call returns truthy). No new `machine` call, no
  reordering.
- `sfx.*` call sites in `ACTIONS`/`afterAction`/`handleGameover`: same
  strictly-after placement as §3.2/§3.4.
- `highscores.js` (`qualifies`/`recordScore`/`getHighScores`/
  `isStorageAvailable`): only reached from `handleGameover`, only after
  `machine.gameover` is already `true`, operating on `{ score, level, lines }`
  — three already-live getters read once and copied into plain numbers
  (`scoreInfo`), never a `Machine` reference itself. `localStorage` is no
  more part of `Σ` than `sound.js`'s `AudioContext` is (§3.2) — no-use for
  the same reason.
- `awaitingName`/`pendingScore`/`RESTART_LOCKOUT_MS`/`gameoverAt`: new local
  closure state, unread by any `α` (`t6/proofs.md` has no `α` construction
  spanning a controller at all — `Σ` there is just the `Machine` instance
  itself, so *any* controller-local variable is automatically outside it).

## 5. Conclusion

`final/`'s obligation reduces entirely to `t7/proofs.md` (multiplayer) and
`t6/proofs.md` (single-player), verbatim, plus §§3–4 above showing the added
surface is no-use. No new argument was needed beyond confirming, call site by
call site, that nothing new was inserted *between* an existing pair of
`Machine`-mutating calls, and that every new read either precedes a mutating
call on its pre-state or follows one on its post-state. `final/*.js ⊨ T7.v`
(multiplayer) and `final/*.js ⊨ T6.v` (single-player, via `t7/model.js`'s own
`PlayerCount = 1` delegation to `t6/model.js`, `t7/proofs.md` §2) both hold.
