# implementation.md — `tfinal/`, delta over `t7/implementation.md`

Not a fresh derivation. `tfinal/` introduces no `model.js` of its own and no
new naming map — every `T7.v`/`T6.v` ↔ JS correspondence `t7/implementation.md`
already establishes (§§3–13 there) applies unchanged to the same classes,
imported directly. This file's own scope is narrower: the file layout, and
the surface `tfinal/` adds on top — four small modules (`view.js`, `sound.js`,
`mute.js`, `highscores.js`) plus each controller's own delta. Menu navigation,
the in-game menu and message validation are `t7/`'s own (`t7/menu.js`,
`t7/protocol.js`, `t7/implementation.md` §15.3a, §15.8a, §15.8b), imported
as is.

## 0. Files reused unchanged

`tfinal/model.js` does not exist:

```
$ grep -rn "from '.*model.js'" tfinal/*.js
tfinal/controller.js:    import { T } from '../t7/model.js';
tfinal/controller.js:    import { T as T6 } from '../t6/model.js';
tfinal/sp_controller.js: import { T } from '../t6/model.js';
```

`tfinal/controller.js`'s multiplayer path drives the same `T7.Machine`/
`T6Eng.Machine` `t7/implementation.md` documents; `tfinal/sp_controller.js`'s
single-player path drives `t6/model.js`'s `T6.Machine` directly (never
`T7.Machine` — no filler-machine duality, unlike `t7/controller.js`'s own
mid-match filler at §15.2). `tfinal/instance.js` is `export * from
'../t7/instance.js'` — same relationship `t7/implementation.md` §11 describes
one level down for `t7/instance.js` itself over `t6/instance.js`.

## 1. File layout

```
controller.js     # network relay, lobby, waiting room — delta over t7/controller.js (§5)
sp_controller.js  # single-player: wraps t6.Machine directly, no T7 involved (§6)
view.js           # clear-flash, garbage-flash, partial gameover overlay (§2)
sound.js          # procedural sfx (Web Audio), no assets (§3)
mute.js           # the in-game menu's Mute/Unmute item, "MUTED" badge (§3)
highscores.js     # localStorage hall of fame, SP-only (§4)
instance.js       # re-exports t7/instance.js; adds nothing (§0)
../vendor/
  fflate.js       # deflate/inflate, used by controller.js's rawSend/decodeMsg (§5)
index.html        # canvas + DOM overlay container — delta over t7/index.html (§7)
proofs.md         # refinement proof, delta over t7/proofs.md and t6/proofs.md
tests/
  highscores.test.js  # insertEntry's row among ties, normalize
```

No `model.js`: nothing here is a `Machine`-level primitive to unit-test
independently of `t6/`'s and `t7/`'s own suites. `tests/` covers
`highscores.js`'s pure helpers.

## 2. `view.js`

Never imports `model.js`/`instance.js` (same convention as every `view.js` in
the tower, `t7/implementation.md` §14.1). Takes only plain data — a
`snapshot()`, a raw grid array, row indices, a progress float, a cell size —
never a `Machine` reference.

- **`renderClearFlash(canvas, constants, snapshot, mgBeforeClear, rows, progress, pieceColor)`**
  — draws the pre-clear board (`mgBeforeClear`, the falling piece already
  merged into it) with the full `rows` fading to white, around the hold box,
  panel and preview of the live `snapshot`. Only the board is frozen; the
  controllers freeze the game itself for the flash's duration (§5, §6). `progress` is a curve value from the caller's animation timer — `0`
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
music. `ctx`/`muted`/`unavailable` are module-private (`let`, not exported) —
`getCtx()` lazily creates the `AudioContext` and resumes it if suspended
(browsers require a prior user gesture). `tone(ac, spec)` plays one oscillator
envelope; `beep(spec)` and `chord(specs)` are the two call shapes used
elsewhere (`chord` shares one `getCtx()` lookup across several tones fired
together), both no-ops while `muted`. `export const sfx` maps named events to
`beep`/`chord` calls with fixed frequency/duration/gain per event: `move`,
`rotate`, `hold`, `fix`, `drop`, `clear(lines)`, `perfectClear`,
`combo(count)`, `levelUp`, `gameover`, `garbageSlam(rows)`, `winner`,
`disconnect`, `hostLost`. `toggleMuted`/`isMuted` flip and read the
module-private flag.

Every `sfx` call is fail-soft and never throws. If Web Audio is missing, or
the `AudioContext` constructor throws, `unavailable` is set and sound stays
off for the rest of the page's life; an error while scheduling a tone is
caught and that tone is not played. The controllers call `sfx` in the middle
of a step's handling (for instance right after a lock, before the lock's
`GARBAGE`/`GAMEOVER` are sent), so a throw there would cut that handling
short.

Muting is toggled from the in-game menu's third item, on top of `t7/`'s
Continue/Quit, in both controllers. `mute.js`'s `muteItemLabel()` is "Mute"
or "Unmute", whichever activating it does. `toggleMute(root)` flips the flag
and shows or hides the "MUTED" badge (`#muted-badge`, `index.html`), which
keeps the state visible on every screen. There is no key binding.

## 4. `highscores.js`

`localStorage`-backed, single-player only. `KEY = 'tetris-tfinal-hof-v1'`
(versioned, so a later schema change doesn't have to migrate or crash on old
data); `MAX_ENTRIES = 10`. `load`/`save` are private, fail-soft (`try/catch`
around every `localStorage` call — corrupted data, storage full, or storage
disabled all fall back to `[]`/silent no-op rather than throwing).
`localStorage.setItem` replaces the stored value atomically, so a crash
mid-save cannot leave a partial table.

- **`normalize(parsed)`** — what `load` returns. A stored table is not trusted
  to be what `save` wrote (it can be edited by hand). Anything but an array
  is `[]`. Entries that are not records with finite numeric `score`/`level`/
  `lines` are dropped. Names go through `t7/protocol.js`'s `sanitizeName`
  (control characters dropped, clamped to `NAME_MAX_LEN`). The result is
  stable-sorted by score, highest first, and truncated to `MAX_ENTRIES`.
- **`insertEntry(entries, entry)`** — inserts after every entry scoring at
  least as much (an earlier equal score keeps its rank), truncates, and
  returns `{ entries, row }`, `row` being the new entry's own index, or `-1`
  if it did not make the table.

- **`isStorageAvailable()`** — a real read/write probe, not an `undefined`
  check: some privacy configurations (e.g. blocking all storage, not just
  third-party) make every `localStorage` call silently no-op for every site,
  first-party included, so a probe is the only reliable signal.
- **`getHighScores()`** — returns the stored list, normalized.
- **`qualifies(score)`** — true if the table isn't full, or `score` beats the
  current lowest entry. Checked before prompting for a name.
- **`recordScore(name, score, level, lines, date = Date.now())`** — sanitizes
  the name, inserts with `insertEntry`, persists, and returns `{ entries, row }`.
  The hall of fame highlights `row`, so tied scores are not all highlighted.

## 5. `controller.js` — delta over `t7/controller.js`

Diffed against `t7/controller.js`; everything below is additive.

**Networking, menus — unchanged.** `sendToHost`/`sendToPlayer`/
`declarePlayerDisconnected`/`rawSend`/`decodeMsg`, the message-dispatch table,
the validation of received messages (`t7/protocol.js`), the wire encoding
(`JSON.stringify` → `deflateSync` on send, `inflateSync` → `JSON.parse` on
receipt, bounded by `t7/protocol.js`'s `decodeWire`), menu navigation and
the in-game menu (`t7/menu.js`) are a verbatim port of `t7/controller.js`'s
own — see `t7/implementation.md` §15, not
restated here. Two differences:
- The in-game menu has a third item, Mute/Unmute (§3).
- `S1`'s single player is `sp_controller.js` (§6), not the in-controller
  `SP` screen. On `screen === 'SP'` this controller takes no input (keys,
  menu edges, in-game menu) and leaves the canvas size alone (`sizeCanvas`
  returns early). `sp_controller.js` owns both until its `onQuit` hands back:
  `dispose()`, `showScreen('S1')`, then `sizeCanvas()`.

One addition: `sfx.disconnect()` inside `applyIncoming`'s `'DISCONNECT'` branch, placed
after `t7machine.receiveDisconnect(msg.from)` returns.

**New closure state (`main()`):**
- `clearAnim`, `garbageAnim` — animation timers for `view.js`'s
  `renderClearFlash`/`drawGarbageFlash`, driven by `frame()`'s own clock.
- `gameoverAt`, `RESTART_LOCKOUT_MS` — `t7/controller.js`'s mid-match filler
  (§15.2) restarts on the very next keypress after gameover; `tfinal/`
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

**Flash sequencing.** A lock that both clears lines and materializes garbage
arms both flashes. The clear flash (180 ms, or 320 ms for a Tetris) is shown
first, then the garbage flash (130 ms): `garbageAnim.start` is set to the end
of the same lock's clear flash (`clearAnim.start + clearAnim.duration`),
because `onLocked` arms `clearAnim` just before `maybeAnimateGarbage` runs.
`frame()` draws the garbage flash only once `now >= garbageAnim.start`, and
never while `clearAnim` runs.

The clear flash is a line-clear delay. While it runs, `frame()` calls no
`processGameInput` and no gravity tick, and shifts `lastGravityAt` by every
flash frame, the same freeze the in-game menu applies to a local game. The
board it shows is the pre-clear one, so the game it hides cannot move or lock
a piece meanwhile. Network handlers keep running. The garbage flash draws the
live board and freezes nothing. During the clear flash, `renderClearFlash`
freezes the main area only. `frame()` then draws `t7/view.js`'s
`drawSideRegions` on top, so the garbage gauge and the opponents' boards stay
visible and live. The menu hint is drawn on every frame of a game screen,
flashes included.
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

Wraps `t6/model.js`'s `Machine` directly — no `t7eng`, no host/joiner roles,
no data channel. Its own `constants`/`eng` are built from `t6/instance.js`,
independent of `tfinal/controller.js`'s.

`main(canvas, root, { onQuit })` returns `dispose`, which stops the frame
loop and the hall-of-fame timer, removes every listener, and removes the
overlays it built and its in-game menu. The caller calls it from `onQuit`.
Without `onQuit` (the file launched on its own), Quit starts a new game.

- **Gravity** is frame-driven, like the multiplayer controller's:
  `lastFallAt`/`fallPeriodMs`, re-armed by `rescheduleFall` (level change,
  new game), with one `fallStep` whenever `now - lastFallAt >= fallPeriodMs`
  while playing.
- **Clear flash** freezes the game like the multiplayer controller's (§5):
  no input, no gravity, `lastFallAt` shifted by every flash frame.
- **In-game menu** (`t7/menu.js`'s `createGameMenu`, titled "Paused"):
  Continue / Quit / Mute|Unmute (§3). Pause (`[Esc]`/pad Start) opens it,
  only while playing, never on the gameover screens. It behaves like
  `t7/implementation.md` §15.8b's local-game case. The game is frozen (no
  input, no gravity, `lastFallAt` shifted by every frozen frame). Back or
  pause close it like Continue, which records every still-held action as
  already pressed. Quit calls `onQuit`. Entering from `S1`'s confirm records
  the same way, so a held pad button 0 does not rotate on the first frame.
  The "[Esc/Start button] menu" hint is drawn while playing with the menu
  closed.
- **Gameover screens** (name entry, hall of fame) are menus:
  - Back (`[Esc]`/pad East) calls `onQuit`, from both. Escape is also seen
    while the name field has focus.
  - Name entry: `[Enter]` or pad button 0 submits.
  - Hall of fame: "Play Again" is focused, and the pad moves among and
    activates its buttons.
  - After the lockout, pad button 0 also restarts, and so does any key other
    than Escape.
  - Each overlay carries a `menu` controls table.
- `precomputeLock`, `onLocked`, `attemptFall`, `attemptDrop` mirror §5's
  pattern: `precomputeLock` reads `machine.s1` before `machine.fallStep`/
  `machine.dropPiece`; `onLocked` reacts after the same call returns truthy.
- `sfx.*` call sites in `ACTIONS`/`afterAction`/`handleGameover`: same
  strictly-after placement as §5.
- `handleGameover` runs once per game (guarded on `gameoverAt`): a later
  action of the same input frame also ends in `afterAction` with gameover
  already true.
- **Hall-of-fame flow** (`handleGameover`): on gameover, `isStorageAvailable()
  && qualifies(scoreInfo.score)` decides between `showNameEntry(scoreInfo)`
  (name-entry overlay, blocks restart via `awaitingName`) and
  `showHallOfFame(getHighScores(), null)` (skip straight to the board).
  Submitting a name (sanitized, `maxLength = NAME_MAX_LEN`) calls
  `recordScore` and re-renders via `showHallOfFame(entries, row)`, which
  highlights the just-submitted entry's own row. Both overlays (`.hof-name-input`/`.hof-name-submit`,
  `.hof-entries`/`.hof-play-again`) are built at startup by `buildOverlays(root)`
  and appended to `#game-root` — not present in `index.html`'s static markup
  (§7).
- `awaitingName`, `pendingScore`, `gameoverAt`, `RESTART_LOCKOUT_MS` — closure
  state; `RESTART_LOCKOUT_MS` gates the restart prompt the same way §5's does
  for the multiplayer filler, and additionally gates on `awaitingName` (no
  restart while the name-entry overlay is up).

## 7. `index.html` — delta over `t7/index.html`

Same `S1`–`S10` overlay divs and the same `<script type="module">` entry
point (`import { main } from './controller.js'`) as `t7/index.html`. Three
additions: the page title (`Tetris`, vs. `t7/index.html`'s `Tetris —
Multiplayer`, since this page also serves single-player from `S1`), the
`#muted-badge` element and its CSS (§3), and two CSS rules,
`.hof-entry`/`.hof-entry.highlight`, styling the hall-of-fame overlay
`sp_controller.js`'s `buildOverlays` constructs at runtime (§6) — no
corresponding static markup exists in this file for it.
