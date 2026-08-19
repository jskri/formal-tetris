# implementation.md — `final/`, delta over `t7/implementation.md`

Not a fresh derivation. `final/` introduces no `model.js` of its own and no
new naming map — every `T7.v`/`T6.v` ↔ JS correspondence `t7/implementation.md`
already establishes (§§3–13 there) applies unchanged to the same classes,
imported directly. This file's own scope is narrower: the file layout, and
the surface `final/` adds on top — three small modules (`view.js`, `sound.js`,
`highscores.js`) plus each controller's own delta.

## 0. Files reused unchanged

`final/model.js` does not exist:

```
$ grep -rn "from '.*model.js'" final/*.js
final/controller.js:    import { T } from '../t7/model.js';
final/controller.js:    import { T as T6 } from '../t6/model.js';
final/sp_controller.js: import { T } from '../t6/model.js';
```

`final/controller.js`'s multiplayer path drives the same `T7.Machine`/
`T6Eng.Machine` `t7/implementation.md` documents; `final/sp_controller.js`'s
single-player path drives `t6/model.js`'s `T6.Machine` directly (never
`T7.Machine` — no filler-machine duality, unlike `t7/controller.js`'s own
mid-match filler at §15.2). `final/instance.js` is `export * from
'../t7/instance.js'` — same relationship `t7/implementation.md` §11 describes
one level down for `t7/instance.js` itself over `t6/instance.js`.

## 1. File layout

```
controller.js     # network relay, lobby, waiting room — delta over t7/controller.js (§5)
sp_controller.js  # single-player: wraps t6.Machine directly, no T7 involved (§6)
view.js           # clear-flash, garbage-flash, partial gameover overlay (§2)
sound.js          # procedural sfx (Web Audio), no assets (§3)
highscores.js     # localStorage hall of fame, SP-only (§4)
instance.js       # re-exports t7/instance.js; adds nothing (§0)
../vendor/
  fflate.js       # deflate/inflate, used by controller.js's rawSend/decodeMsg (§5)
index.html        # canvas + DOM overlay container — delta over t7/index.html (§7)
proofs.md         # refinement proof, delta over t7/proofs.md and t6/proofs.md
```

No `model.js`, no `tests/` (nothing here is a `Machine`-level primitive to
unit-test independently of `t6/`'s and `t7/`'s own suites).

## 2. `view.js`

Never imports `model.js`/`instance.js` (same convention as every `view.js` in
the tower, `t7/implementation.md` §14.1). Takes only plain data — a
`snapshot()`, a raw grid array, row indices, a progress float, a cell size —
never a `Machine` reference.

- **`renderClearFlash(canvas, constants, snapshot, mgBeforeClear, rows, progress, pieceColor)`**
  — freezes the pre-clear frame (board, hold, panel, preview; no falling
  piece, already merged into `mgBeforeClear`) and fades the full `rows` to
  white. `progress` is a curve value from the caller's animation timer — `0`
  is normal colors, `1+` is allowed (a Tetris's pulse can briefly overshoot;
  alpha is clamped). `mgBeforeClear` is a plain 2D array (`union()`,
  `t1/model.js`, never wraps its output) — `wrapGrid`, local to this file,
  adapts it to the `{ height, width, cell(y,x) }` shape `drawGrid` expects,
  since this file can't reuse `model.js`'s own `wrapGrid` (same
  never-imports-`model.js` rule).
- **`drawGarbageFlash(canvas, constants, rowCount, progress)`** — a hard,
  fast-cutoff flash (`progress` `0→1` maps directly to alpha `1→0`, no easing)
  on the bottom `rowCount` rows, drawn by the caller after its own normal
  `render()` for the frame. Deliberately not a fade-in.
- **`drawGameOverPartial(canvas, constants, cellSize)`** — dim + "GAME OVER"
  heading only, omitting the "press any key to restart" line
  `t1/view.js`'s `drawGameOver` draws. Used for the window between gameover
  and the restart prompt/input becoming active (§3.3, `RESTART_LOCKOUT_MS`).

## 3. `sound.js`

Procedural tones (Web Audio `OscillatorNode`/`GainNode`), no audio assets, no
music. `ctx`/`muted` are module-private (`let`, not exported) — `getCtx()`
lazily creates the `AudioContext` and resumes it if suspended (browsers
require a prior user gesture). `tone(ac, spec)` plays one oscillator envelope;
`beep(spec)` and `chord(specs)` are the two call shapes used elsewhere
(`chord` shares one `getCtx()` lookup across several tones fired together),
both no-ops while `muted`. `export const sfx` maps named events (`move`,
`rotate`, `lock`, `clear`, `tetris`, `garbage`, `gameover`, `disconnect`, …)
to `beep`/`chord` calls with fixed frequency/duration/gain per event.
`toggleMuted`/`isMuted` flip and read the module-private flag.

## 4. `highscores.js`

`localStorage`-backed, single-player only. `KEY = 'tetris-final-hof-v1'`
(versioned, so a later schema change doesn't have to migrate or crash on old
data); `MAX_ENTRIES = 10`. `load`/`save` are private, fail-soft (`try/catch`
around every `localStorage` call — corrupted data, storage full, or storage
disabled all fall back to `[]`/silent no-op rather than throwing).

- **`isStorageAvailable()`** — a real read/write probe, not an `undefined`
  check: some privacy configurations (e.g. blocking all storage, not just
  third-party) make every `localStorage` call silently no-op for every site,
  first-party included, so a probe is the only reliable signal.
- **`getHighScores()`** — returns the stored list as-is.
- **`qualifies(score)`** — true if the table isn't full, or `score` beats the
  current lowest entry. Checked before prompting for a name.
- **`recordScore(name, score, level, lines)`** — appends, sorts descending by
  score, truncates to `MAX_ENTRIES`, persists, returns the new list.

## 5. `controller.js` — delta over `t7/controller.js`

Diffed against `t7/controller.js`; everything below is additive.

**Networking — unchanged.** `sendToHost`/`sendToPlayer`/
`declarePlayerDisconnected`/`rawSend`/`decodeMsg`, the message-dispatch table,
and the wire encoding (`JSON.stringify` → `deflateSync` on send, `inflateSync`
→ `JSON.parse` on receipt) are a verbatim port of `t7/controller.js`'s own —
see `t7/implementation.md` §15, not restated here. One addition: `sfx.disconnect()`
inside `applyIncoming`'s `'DISCONNECT'` branch, placed after
`t7machine.receiveDisconnect(msg.from)` returns.

**New closure state (`main()`):**
- `clearAnim`, `garbageAnim` — animation timers for `view.js`'s
  `renderClearFlash`/`drawGarbageFlash`, driven by `frame()`'s own clock.
- `gameoverAt`, `RESTART_LOCKOUT_MS` — `t7/controller.js`'s mid-match filler
  (§15.2) restarts on the very next keypress after gameover; `final/`
  delays that by `RESTART_LOCKOUT_MS` so a last-second key mash during
  gameover doesn't immediately restart the filler.

**New functions:**
- **`precomputeLock(py, px)`** — reads `getS1()` (pre-mutation) and calls
  `T6Eng.T1Eng.union`/`isFullLineb`, both already-exported query helpers
  (`t1/model.js`), to compute what `renderClearFlash` needs. Called from
  `doFall`/`doDrop`, strictly before the mutating `movePiece`/`fixPiece`/
  `dropPiece` call in the same function.
- **`onLocked`**, **`maybeAnimateGarbage`** — called only after the mutating
  call they react to (`fixPiece`/`dropPiece`) has returned `true`.
  `maybeAnimateGarbage` calls `t7eng.genRemGarbage(garbageBefore,
  s1.clearedLines, t7machine.s6.perfectClear)` — the same free function
  `fixPiece` itself calls internally, given the same post-mutation values
  `fixPiece` just computed.
- **`getS1()`** — `isT7 ? machine.s6.s1 : machine.s1`, a two-way branch over
  `T7.Machine`'s existing flattened accessor chain (`t7/implementation.md`
  §6.8) — adds no new field.
- **`activeMachine()`** — new `screen === 'S9'` branch, returning `t7machine`
  frozen at whatever it held when gameover fired (`S9` is the match result,
  never the mid-match filler). Affects only which machine's `snapshot()` gets
  drawn on the winner screen; `frame()` never routes input through
  `activeMachine()`'s result while `screen === 'S9'`.

`sfx.*` call sites: every `ACTIONS.X.effect` (`LEFT`/`RIGHT`/`HOLD`/
`doRotate`) calls the same `machine.<method>(...)` `t7/controller.js` calls,
with an `sfx.*()` call inserted strictly after, gated on the same
fired/not-fired boolean the call returns.

## 6. `sp_controller.js` — single-player

Wraps `t6/model.js`'s `Machine` directly — no `T7Eng`, no host/joiner roles,
no data channel. Its own `constants`/`eng` are built from `t6/instance.js`,
independent of `final/controller.js`'s.

- `precomputeLock`, `onLocked`, `attemptFall`, `attemptDrop` mirror §5's
  pattern: `precomputeLock` reads `machine.s1` before `machine.fallStep`/
  `machine.dropPiece`; `onLocked` reacts after the same call returns truthy.
- `sfx.*` call sites in `ACTIONS`/`afterAction`/`handleGameover`: same
  strictly-after placement as §5.
- **Hall-of-fame flow** (`handleGameover`): on gameover, `isStorageAvailable()
  && qualifies(scoreInfo.score)` decides between `showNameEntry(scoreInfo)`
  (name-entry overlay, blocks restart via `awaitingName`) and
  `showHallOfFame(getHighScores(), null)` (skip straight to the board).
  Submitting a name calls `recordScore` and re-renders via
  `showHallOfFame(entries, pendingScore.score)`, which highlights the
  just-submitted entry. Both overlays (`.hof-name-input`/`.hof-name-submit`,
  `.hof-entries`/`.hof-play-again`) are built at startup by `buildOverlays(root)`
  and appended to `#game-root` — not present in `index.html`'s static markup
  (§7).
- `awaitingName`, `pendingScore`, `gameoverAt`, `RESTART_LOCKOUT_MS` — closure
  state; `RESTART_LOCKOUT_MS` gates the restart prompt the same way §5's does
  for the multiplayer filler, and additionally gates on `awaitingName` (no
  restart while the name-entry overlay is up).

## 7. `index.html` — delta over `t7/index.html`

Same `S1`–`S10` overlay divs and the same `<script type="module">` entry
point (`import { main } from './controller.js'`) as `t7/index.html`. Two
additions: the page title (`Tetris`, vs. `t7/index.html`'s `Tetris —
Multiplayer`, since this page also serves single-player from `S1`), and two
CSS rules, `.hof-entry`/`.hof-entry.highlight`, styling the hall-of-fame
overlay `sp_controller.js`'s `buildOverlays` constructs at runtime (§6) — no
corresponding static markup exists in this file for it.
