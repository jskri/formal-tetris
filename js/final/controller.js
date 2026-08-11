import { T } from '../t7/model.js';
import { T as T6 } from '../t6/model.js';
import { render } from '../t7/view.js';
import { renderClearFlash, drawGarbageFlash, drawGameOverPartial } from './view.js';
import { sfx } from './sound.js';
import {
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX, NextLen, PieceColor,
} from '../t7/instance.js';

const T6Eng = T6(Piece, InitialMainGrid, ForbiddenGrid, RotGrid, InitialY, InitialX,
                  PW, FY, FX, NextLen);

const constants = {
  HM: InitialMainGrid.length,
  WM: InitialMainGrid[0].length,
  PW, FY, FX, NextLen,
  Piece,
  FH: ForbiddenGrid.length,
  FW: ForbiddenGrid[0].length,
  rotGrid: T6Eng.T1Eng.rotGrid, // needed by t5/view.js's drawing calls and t7/view.js's mini-strip
  PANEL_PX: 0,
  gridAreaWidth: 0, // set by sizeCanvas — excludes the mini-grid strip
};

const STUN_SERVERS = [{ urls: 'stun:stun.l.google.com:19302' }];
const STATE_HZ = 3;
const STATE_PERIOD_MS = 1000 / STATE_HZ;
const HEARTBEAT_TIMEOUT_MS = 10000;
const HEARTBEAT_CHECK_MS = 1000;

const DAS_DELAY = 170;
const ARR = 50;
const BANNER_MS = 1200;
const BASE_PERIOD = 1000;
const MIN_PERIOD = 16;
const EPS = 1e-6;

const CLEAR_ANIM_MS = 180;    // freeze-and-fade duration for a 1-3 line clear
const TETRIS_ANIM_MS = 320;   // longer, punchier duration for a 4-line clear
const SHAKE_AMPLITUDE = 6;    // px, decays to 0 over the Tetris animation
const GARBAGE_ANIM_MS = 130;  // short and brutal by construction, not level-scaled
const GARBAGE_SHAKE_BASE = 8; // px — harder than a Tetris shake; garbage should feel worse
const RESTART_LOCKOUT_MS = 1000; // no restart prompt/input for this long after the filler's
                                  // own gameover — a frantic last-second key mash shouldn't
                                  // instantly restart it

function normalCurve(t) { return t; }

// Ramps to white slightly ahead of the animation's end, then adds a decaying
// flicker on top so a Tetris reads as a pulse rather than a single fade.
function tetrisCurve(t) {
  const base = Math.min(1, t * 1.3);
  const flicker = Math.sin(t * Math.PI * 6) * (1 - t) * 0.4;
  return Math.max(0, Math.min(1, base + flicker));
}

function fallPeriod(level) {
  const base = Math.max(EPS, 0.8 - (level - 1) * 0.007);
  const secs = Math.pow(base, level - 1);
  return Math.max(MIN_PERIOD, Math.round(BASE_PERIOD * secs));
}

// Same keys/gamepad map as t6/controller.js — dropPiece is available at T7
// level too now (§4-T7i), so DROP is wired identically.
const KEYMAP = new Map([
  ['ArrowLeft', 'LEFT'], ['ArrowRight', 'RIGHT'], ['ArrowDown', 'DOWN'], ['ArrowUp', 'DROP'],
  ['z', 'CCW'], ['x', 'CW'], [' ', 'HOLD'],
]);
const GAMEPAD_MAP = new Map([
  [14, 'LEFT'], [15, 'RIGHT'], [13, 'DOWN'], [12, 'DROP'],
  [0, 'CCW'], [1, 'CW'], [3, 'HOLD'],
]);

function shuffleBag() {
  const a = Piece.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

function makeBagsFn() {
  const bags = [];
  return (i) => { while (bags.length <= i) bags.push(shuffleBag()); return bags[i]; };
}

// ── WebRTC — manual copy/paste signalling, no relay server ────────────────
// ICE gathering must complete before the SDP is shown/copied: there is no
// trickle-ICE channel once the blob has been pasted, so it must be complete.
// pc is the peer connection.
function waitIceComplete(pc) {
  if (pc.iceGatheringState === 'complete') return Promise.resolve();
  return new Promise((resolve) => {
    function check() {
      if (pc.iceGatheringState === 'complete') {
        pc.removeEventListener('icegatheringstatechange', check);
        resolve();
      }
    }
    pc.addEventListener('icegatheringstatechange', check);
  });
}

// Joiner is the offerer (a player joins by initiating contact — §15.0).
async function createOfferConnection() {
  const pc = new RTCPeerConnection({ iceServers: STUN_SERVERS });
  const dc = pc.createDataChannel('t7', { ordered: true });
  await pc.setLocalDescription(await pc.createOffer());
  await waitIceComplete(pc);
  return { pc, dc, sdpText: JSON.stringify(pc.localDescription) };
}

async function applyAnswer(pc, answerText) {
  await pc.setRemoteDescription(JSON.parse(answerText));
}

// Host is the answerer, given a pasted offer.
async function createAnswerConnection(offerText) {
  const pc = new RTCPeerConnection({ iceServers: STUN_SERVERS });
  let resolveDc;
  const dcPromise = new Promise((res) => { resolveDc = res; });
  pc.ondatachannel = (e) => {
    const ch = e.channel;
    resolveDc(ch);
  };
  await pc.setRemoteDescription(JSON.parse(offerText));
  await pc.setLocalDescription(await pc.createAnswer());
  await waitIceComplete(pc);
  return { pc, dcPromise, sdpText: JSON.stringify(pc.localDescription) };
}

export function main(canvas, root) {
  const ctx = canvas.getContext('2d');

  // ── lifecycle state ──
  let screen = 'S1';
  let matchGen = 0;
  let myIndex = null;
  let myName = '';
  let isHost = false;

  // Host-only. Index 0 is the host itself: conn = null, pc = null (never
  // dialed over the network, applied locally — §4-T7f/g).
  let playerData = []; // [{ name, conn, pc, lastHeard, declaredDisconnected }]

  // Joiner-only.
  let hostConn = null;
  let hostPc = null;
  let hostLostHandled = false; // guards against watchConnection() and the
                                // heartbeat both firing noticeHostLost()
  let roster = []; // names, index-aligned, joiner's own copy from PLAYERS
  let lastHostMessageAt = 0;

  // Gameplay
  let t7eng = null;    // this match's T7 engine instance (closure, not window)
  let t7machine = null;
  let t6machine = null; // filler, active during S6/S8
  let opponents = [];   // index-aligned: { name, mg, p, py, px, pr, gameover, connected }
  let inMidMatchFiller = false;

  // Input (shared across S6/S7/S8 — whichever machine is "active")
  let keyHeld = new Set();
  let prevHeld = {};
  let repeatTimers = {};
  let prevLevel = 1;
  let banner = null;
  let prevTotalClearedLines = 0;
  let lastGravityAt = 0;
  let currentGravityPeriod = fallPeriod(1);
  let gravityRunning = false;
  let clearAnim = null;   // { grid, rows, lines, start, duration } — line-clear flash
  let garbageAnim = null; // { rowCount, start, duration } — garbage-slam flash; only ever
                           // starts once clearAnim is null (frame()'s own priority), matching
                           // the model's own sequencing (own clear resolves before materialization)
  let gameoverAt = null;   // timestamp the T6 filler's gameover was detected; null otherwise —
                           // only the filler has an "any key restarts" flow to gate; T7's own
                           // gameover transitions straight to the filler/winner screen instead

  // Menu focus (S1/S2/S3/S4/S9/S10)
  let focusIndex = 0;
  let prevMenuHeld = {};

  let stateTimer = null;
  let heartbeatTimer = null;

  const nameOf = (i) => (isHost ? (playerData[i]?.name ?? '?') : (roster[i] ?? '?'));

  // ── screens ──
  const SCREEN_IDS = ['S1', 'S2', 'S3', 'S4', 'S6', 'S9', 'S10'];
  function showScreen(id) {
    screen = id;
    for (const s of SCREEN_IDS) {
      const el = document.getElementById(s);
      if (el) el.classList.toggle('hidden', s !== id);
    }
    focusIndex = 0;
    menuButtons()[0]?.focus();
  }

  function menuButtons() {
    const el = document.getElementById(screen);
    if (!el) return [];
    return Array.from(el.querySelectorAll('button:not([disabled])'));
  }

  // ── connection-state watcher ──
  // `'disconnected'` is not terminal — the ICE agent keeps retrying
  // connectivity checks on its own and can recover without any action here.
  // Only `'failed'` is authoritative: react to it immediately via `onFailed`
  // rather than waiting for the heartbeat's message-silence heuristic to
  // time out, and attempt restartIce() — a no-op unless a channel exists to
  // carry the resulting renegotiation to the peer (none does here, since
  // this app has no signaling beyond the initial manual offer/answer paste),
  // but harmless, and correct if that ever changes.
  function watchConnection(pc, onFailed) {
    pc.onconnectionstatechange = () => {
      if (pc.connectionState === 'failed') {
        pc.restartIce();
        onFailed();
      }
    };
  }

  // ── message envelope / transport ──
  function tag(msg) { return { ...msg, gen: matchGen }; }
  function rawSend(dc, msg) {
    if (dc && dc.readyState === 'open') { dc.send(JSON.stringify(msg)); return true; }
    return false;
  }
  // A failed send attempt is itself treated as detection, fail-fast, rather
  // than left as a silent drop for the heartbeat/watchConnection timers to
  // eventually notice on their own — otherwise `hostLostHandled` (this
  // player's own realization of `connected`, §3) could still read `true` for
  // a window after the channel has actually stopped accepting sends, during
  // which a `fixPiece`-triggered message would silently vanish with no
  // corresponding `T7.v` step to match it to (`t7/proofs.md` §5a).
  function sendToHost(msg) {
    if (hostLostHandled) return; // already declared — matches connected = false,
                                  // no send attempted
    if (!rawSend(hostConn, tag(msg))) noticeHostLost();
  }
  // Shared by the heartbeat's own timeout branch, watchConnection's onFailed
  // callback, and sendToPlayer's own fail-fast path below — all three are
  // realizations of the same `DisconnectPlayer pl` transition (`pl ≠ Host`),
  // so they share one guarded, idempotent implementation (§4-T7f, §10).
  function declarePlayerDisconnected(idx) {
    const p = playerData[idx];
    if (!p || p.declaredDisconnected) return;
    p.declaredDisconnected = true;
    const msg = { type: 'DISCONNECT', from: idx, to: null };
    applyIncoming(msg); // host's own view
    broadcastFromHost(tag(msg), idx);
    maybeEnterWinnerScreen(idx); // a disconnect can decide the match on its own,
                                  // same as a GAMEOVER can
  }
  function sendToPlayer(idx, msg) {
    if (idx === 0) return;
    const p = playerData[idx];
    if (!p || p.declaredDisconnected) return; // already declared — matches
                                               // connected = false, no send attempted
    if (!rawSend(p.conn, tag(msg))) declarePlayerDisconnected(idx);
  }
  function broadcastFromHost(msg, exclude) {
    for (let i = 1; i < playerData.length; i++) if (i !== exclude) sendToPlayer(i, msg);
  }

  // Applies an already-routed message to *this* client's own view — used both
  // by the host (for itself) and by every joiner (for everything from host).
  function applyIncoming(msg) {
    switch (msg.type) {
      case 'STATE':
        opponents[msg.from] = {
          // CHECK: OK to not copy msg.mg?
          playerIndex: msg.from,
          name: nameOf(msg.from), mg: msg.mg, p: msg.p, py: msg.py, px: msg.px, pr: msg.pr,
          gameover: msg.gameover, connected: true,
        };
        break;
      case 'GARBAGE':
        t7machine.receiveGarbage(msg.amount);
        break;
      case 'GAMEOVER':
        t7machine.receiveGameover(msg.from);
        if (opponents[msg.from]) opponents[msg.from].gameover = true;
        break;
      case 'DISCONNECT':
        t7machine.receiveDisconnect(msg.from);
        if (opponents[msg.from]) opponents[msg.from].connected = false;
        sfx.disconnect();
        break;
    }
  }

  // A player learns her own connection to the host is gone via noticeHostLost
  // (called from the heartbeat check / connection-close handler), not via any
  // DISCONNECT message — the host never appears as `from` in one (§4-T7f).

  // ── host relay ──
  function hostHandleFromJoiner(fromIdx, msg) {
    if (msg.type === 'JOIN') { hostHandleJoin(fromIdx, msg); return; }
    if (msg.type === 'LEAVE') { hostHandleLeave(fromIdx); return; }
    if (msg.gen !== matchGen) return; // stale — different match
    if (playerData[fromIdx]) playerData[fromIdx].lastHeard = performance.now();
    switch (msg.type) {
      case 'STATE':
        applyIncoming(msg);
        broadcastFromHost(msg, fromIdx);
        break;
      case 'GARBAGE':
        // TODO: replace 0 with HostIndex
        if (msg.to === 0) applyIncoming(msg);
        else sendToPlayer(msg.to, msg);
        break;
      case 'GAMEOVER':
        applyIncoming(msg);
        broadcastFromHost(msg, fromIdx);
        maybeEnterWinnerScreen();
        break;
    }
  }

  // A joiner who truly leaves (rather than rematching) must be evicted, not
  // left in playerData — otherwise it stays there indefinitely, dealt into
  // the next startMatch() by index as a permanently-grey ghost opponent still
  // carrying its old name. Splicing it out is only index-safe if every later
  // slot's dc.onmessage (each closes over its own fixed fromIdx from when it
  // was created) is also rebound to its new, shifted index, and every
  // remaining player is told their possibly-new yourIndex.
  function evictSlot(idx) {
    if (idx <= 0 || idx >= playerData.length) return;
    playerData.splice(idx, 1);
    for (let i = idx; i < playerData.length; i++) {
      const p = playerData[i];
      if (p && p.conn) p.conn.onmessage = (ev) => hostHandleFromJoiner(i, JSON.parse(ev.data));
    }
  }

  function hostHandleLeave(fromIdx) {
    evictSlot(fromIdx);
    broadcastPlayers();
    renderS3Joiners();
  }

  function joinerHandleFromHost(msg) {
    lastHostMessageAt = performance.now();
    if (msg.type === 'PLAYERS') { joinerHandlePlayers(msg); return; }
    if (msg.type === 'START') { joinerHandleStart(msg); return; }
    if (msg.gen !== matchGen) {
      return;
    }
    applyIncoming(msg);
    if (msg.type === 'GAMEOVER') {
      maybeEnterWinnerScreen();
    } else if (msg.type === 'DISCONNECT') {
      maybeEnterWinnerScreen(msg.from);
    }
  }

  // ── JOIN / PLAYERS / START (§15.1) ──
  function hostHandleJoin(fromIdx, msg) {
    // JOIN means "ready for the lobby round currently open". The only truly
    // unsafe moment to process one is mid-match (S7): 's3-start' evicts
    // every not-yet-joined slot for the round about to begin, and a JOIN
    // meant for that round could otherwise race the eviction. It's not
    // gated on screen === 'S3' specifically, though — a joiner's own
    // rematch click sends JOIN immediately (s9-rematch), which routinely
    // reaches the host while the host is still on S9 (game over, its own
    // Rematch not yet clicked) rather than back on S3 already. That JOIN is
    // legitimately for the *next* round and must still be recorded now, not
    // dropped — evictSlot() already keeps every fromIdx correctly rebound
    // across evictions, so there's no index-corruption risk in accepting it
    // early.
    if (screen === 'S7') return;
    if (!playerData[fromIdx]) return; // evicted since this JOIN was sent
    // fromIdx assigned at connection-accept time (see S3 wiring below); msg
    // carries the name.
    playerData[fromIdx].name = msg.name;
    playerData[fromIdx].joined = true;
    playerData[fromIdx].lastHeard = performance.now();
    broadcastPlayers();
    renderS3Joiners();
  }

  function broadcastPlayers() {
    const rosterNames = playerData.map((p) => p.name);
    for (let i = 1; i < playerData.length; i++) {
      sendToPlayer(i, { type: 'PLAYERS', roster: rosterNames, yourIndex: i });
    }
  }

  function joinerHandlePlayers(msg) {
    roster = msg.roster;
    myIndex = msg.yourIndex;
    renderS6Joiners();
  }

  function joinerHandleStart(msg) {
    matchGen = msg.gen; // authoritative — host's own increment, never guessed locally
    showScreen('S7');
    startMatch();
  }

  // ── match start ──
  function startMatch() {
    const Player = isHost ? playerData.map((_, i) => i) : roster.map((_, i) => i);
    const HostIndex = 0;
    const bagsFn = makeBagsFn();
    const eng = T(Piece, InitialMainGrid, ForbiddenGrid, RotGrid, InitialY, InitialX,
                  PW, FY, FX, NextLen, Player, HostIndex);
    t7eng = eng;
    t7machine = new eng.Machine(myIndex, bagsFn);
    opponents = Player.map((_, i) => (i === myIndex ? null : { playerIndex: i, name: nameOf(i), mg: null, gameover: false, connected: true }));
    inMidMatchFiller = false;
    prevLevel = 1;
    banner = null;
    prevTotalClearedLines = 0;
    clearAnim = null;
    garbageAnim = null;
    gameoverAt = null;
    canvas.style.transform = '';
    resetInput();
    retargetGravity();
    startStateTimer();
    broadcastState(); // immediate first STATE at START (§15.3)
  }

  // ── waiting room (S6 pre-START, S8 mid-match — same implementation, §15.2) ──
  function enterWaitingRoom() {
    t6machine = new T6Eng.Machine(makeBagsFn());
    clearAnim = null;
    garbageAnim = null;
    gameoverAt = null;
    canvas.style.transform = '';
    resetInput();
    retargetGravity();
  }

  function enterMidMatchFiller() {
    inMidMatchFiller = true;
    stopStateTimer();
    enterWaitingRoom();
    // t7machine is kept alive headless — still fed receiveGarbage/receiveGameover
    // (via applyIncoming/hostHandleFromJoiner) so findWinner() stays current.
  }

  function activeMachine() {
    if (screen === 'S9') return t7machine; // frozen at whatever it held when
                                            // gameover fired — S9 is the
                                            // match result, never the filler
    if (inMidMatchFiller) return t6machine;
    if (screen === 'S7') return t7machine;
    if (screen === 'S6') return t6machine;
    return null;
  }

  // ── winner / rematch (§15.0 S9, S15.6) ──
  function findWinner() {
    if (!t7machine) return null;
    const Player = t7machine.gameoverView.map((_, i) => i);
    for (const i of Player) {
      const view = (pl2) => t7eng.playingView(t7machine.gameoverView, t7machine.connectedView, pl2);
      let allOthersOut = true;
      for (const j of Player) if (j !== i && view(j)) allOthersOut = false;
      if (view(i) && allOthersOut) return i;
    }
    return null;
  }

  function stopped() {
    return !!t7machine && (t7machine.gameover || findWinner() === myIndex);
  }

  function maybeEnterWinnerScreen(disconnectedPl) {
    const w = findWinner();
    if (w === null) return;
    stopGravity();
    stopStateTimer();
    stopHeartbeat();
    if (w === myIndex) sfx.winner();
    document.getElementById('s9-message').textContent =
      (w === myIndex)
        ? (disconnectedPl !== undefined
            ? `You win! (your last opponent, ${nameOf(disconnectedPl)} was disconnected)`
            : 'You win!')
        : `You lose! Winner: ${nameOf(w)}`;
    showScreen('S9');
  }

  function noticeHostLost() {
    if (hostLostHandled) return; // watchConnection() and the heartbeat can
    hostLostHandled = true;      // both observe the same loss
    if (!t7machine) { showScreen('S1'); return; }
    t7machine.noticeDisconnection();
    // Always S10, never routed through findWinner()/maybeEnterWinnerScreen():
    // losing my own connection to the host is not a legitimate win or loss
    // result, even though winnerMulti() (t7/model.js) may happen to resolve
    // a winner once connectedView[myIndex] flips false (e.g. it always does
    // in a 2-player match, since the sole remaining connected/playing player
    // trivially satisfies WinnerMulti) — that's an artifact of connectedView
    // bookkeeping shared with other players' own views, not a signal about
    // what actually happened to *my* game.
    stopGravity();
    stopStateTimer();
    stopHeartbeat();
    sfx.hostLost();
    showScreen('S10');
  }

  // ── STATE broadcast (§15.3): min 3 Hz, leading-edge reset, immediate on Fix ──
  function startStateTimer() {
    stopStateTimer();
    stateTimer = setInterval(broadcastState, STATE_PERIOD_MS);
  }
  function stopStateTimer() {
    if (stateTimer) clearInterval(stateTimer);
    stateTimer = null;
  }
  function rearmStateTimer() {
    if (stateTimer) { clearInterval(stateTimer); stateTimer = setInterval(broadcastState, STATE_PERIOD_MS); }
  }
  function broadcastState() {
    if (!t7machine) return;
    // Reads t7machine's own live getters directly rather than t7eng.snapshot()
    // (t1/model.js's Machine.p/py/px/pr/mg): snapshot() would spread through
    // the whole T1-T6 chain and copy gameoverView/connectedView, none of which
    // this message uses, then mg would need unwrapping right back out of its
    // read-only accessor for JSON — safe here specifically because
    // JSON.stringify (via rawSend, synchronously, before anything else in this
    // single-threaded turn can run) never mutates what it's given, unlike
    // view.js, which is why snapshot() wraps mg read-only in the first place.
    const msg = { type: 'STATE', from: myIndex, to: null,
      mg: t7machine.mg, p: t7machine.p, py: t7machine.py, px: t7machine.px, pr: t7machine.pr,
      gameover: t7machine.gameover };
    if (isHost) broadcastFromHost(tag(msg), 0);
    else sendToHost(msg);
  }

  // ── fix-family aftermath: garbage send + unconditional STATE + gameover check ──
  function handleFixResult(preTarget) {
    if (t7machine.remGenGarbage > 0) {
      const to = preTarget;
      const msg = { type: 'GARBAGE', from: myIndex, to, amount: t7machine.remGenGarbage };
      if (isHost) { if (to === 0) applyIncoming(msg); else sendToPlayer(to, msg); }
      else sendToHost(msg);
    }
    broadcastState();
    rearmStateTimer();
    if (t7machine.gameover) {
      const msg = { type: 'GAMEOVER', from: myIndex, to: null };
      if (isHost) broadcastFromHost(tag(msg), 0);
      else sendToHost(msg);
      enterMidMatchFiller();
      // Must be checked here too, not just on receiving a GAMEOVER from
      // someone else: the player whose own board just topped out needs to
      // see the win/loss screen the same as everyone else. With 3+ players
      // this correctly no-ops (findWinner() is still null) and the filler
      // stands.
      maybeEnterWinnerScreen();
    }
  }

  // ── heartbeat ──
  function startHeartbeat() {
    stopHeartbeat();
    heartbeatTimer = setInterval(() => {
      const now = performance.now();
      if (isHost) {
        for (let i = 1; i < playerData.length; i++) {
          const p = playerData[i];
          if (!p || p.declaredDisconnected) continue;
          if (now - p.lastHeard > HEARTBEAT_TIMEOUT_MS) declarePlayerDisconnected(i);
        }
      } else if (t7machine && now - lastHostMessageAt > HEARTBEAT_TIMEOUT_MS) {
        stopHeartbeat();
        noticeHostLost();
      }
    }, HEARTBEAT_CHECK_MS);
  }
  function stopHeartbeat() { if (heartbeatTimer) clearInterval(heartbeatTimer); heartbeatTimer = null; }

  // spec: ValidHoles — realized as a fresh, per-call memoizing function, not
  // persistent across calls (unlike bagsFn): GarbageGrid always indexes rows
  // from 0 per materialization event (§4-T7h). Each result is asserted in
  // [0, w) at the point of use — throws, uncaught, mirroring assertPieceSet's
  // role for bagNew.
  function makeHolesFn(w) {
    const holes = [];
    return (y) => {
      while (holes.length <= y) holes.push(Math.floor(Math.random() * w));
      const x = holes[y];
      if (!(0 <= x && x < w)) throw new Error(`makeHolesFn: hole out of range: ${x}`);
      return x;
    };
  }

  // ── input: DAS/ARR, shared between t6 (filler) and t7 (real match) ──
  function actionsFor(machine, isT7) {
    // t6 (filler) has no holesFn — only t7's fixPiece/dropPiece take one,
    // constructed fresh at each call site below via makeHolesFn.
    function getS1() { return isT7 ? machine.s6.s1 : machine.s1; }

    // Computes the union/full-row preview for a piece about to lock at
    // (py, px) — current (py,px) for a soft-drop lock, machine.gy for a hard
    // drop. Bounded to the piece's own vertical footprint, not the whole
    // board (HM is unbounded) — only rows the piece touches can newly become
    // full, since NoFullLine already guarantees every other row wasn't.
    function precomputeLock(py, px) {
      const s1 = getS1();
      const preClearGrid = T6Eng.T1Eng.union(s1.mg, 0, 0, T6Eng.T1Eng.rotGrid(s1.p, s1.pr), py, px);
      const rows = [];
      const yStart = Math.max(py, 0);
      const yEnd = Math.min(py + constants.PW, constants.HM);
      for (let y = yStart; y < yEnd; y++) if (T6Eng.T1Eng.isFullLineb(preClearGrid, y)) rows.push(y);
      return { preClearGrid, rows };
    }

    // Plays the lock sound and arms the clear-flash if any of the player's
    // own lines cleared. Combo/perfectClear/level/clear sounds live in
    // fixFamily() below instead, off totalClearedLines/level diffs — those
    // work identically regardless of how the lock happened.
    function onLocked(preClearGrid, rows, isHardDrop) {
      sfx[isHardDrop ? 'drop' : 'fix']();
      if (rows.length > 0) {
        clearAnim = {
          grid: preClearGrid,
          rows,
          lines: rows.length,
          start: performance.now(),
          duration: rows.length === 4 ? TETRIS_ANIM_MS : CLEAR_ANIM_MS,
        };
      }
    }

    // Garbage materialization is genuinely new content, not a reuse of the
    // clear-flash technique: it's "rows pushed in from the bottom", not
    // "rows fade out". Detected precisely (not just "garbage was pending")
    // via the model's own genRemGarbage, so this can never drift from what
    // fixPiece actually materialized — clearing lines can partly or fully
    // cancel pending garbage (req-multi-garbage-cancel), so "garbage was
    // pending before" alone isn't sufficient to conclude rows landed.
    function maybeAnimateGarbage(garbageBefore) {
      if (!isT7 || garbageBefore <= 0) return;
      const s1 = t7machine.s6.s1;
      const [, remGarbage] = t7eng.genRemGarbage(garbageBefore, s1.clearedLines, t7machine.s6.perfectClear);
      const effRem = Math.min(remGarbage, constants.HM);
      if (effRem > 0) {
        sfx.garbageSlam(effRem);
        garbageAnim = { rowCount: effRem, start: performance.now(), duration: GARBAGE_ANIM_MS };
      }
    }

    function fixFamily(fired, wasFix, preTarget) {
      if (!fired) return;
      if (machine.level !== prevLevel) { sfx.levelUp(); retargetGravity(); }
      if (machine.totalClearedLines > prevTotalClearedLines) {
        sfx.clear(machine.totalClearedLines - prevTotalClearedLines);
        if (machine.perfectClear) sfx.perfectClear();
        if (machine.combo > 1) sfx.combo(machine.combo);
        banner = { combo: machine.combo, perfectClear: machine.perfectClear, t: performance.now() };
      }
      prevTotalClearedLines = machine.totalClearedLines;
      if (isT7 && wasFix) handleFixResult(preTarget);
      if (machine.gameover) { if (!isT7) { stopGravity(); gameoverAt = performance.now(); } sfx.gameover(); }
    }
    function doFall() {
      const s1 = getS1();
      const aboutToLock = !T6Eng.T1Eng.canMovePiece(-1, 0, s1);
      const pre = aboutToLock ? precomputeLock(s1.py, s1.px) : null;
      const garbageBefore = isT7 ? machine.garbage : 0;

      if (machine.movePiece(-1, 0)) { sfx.move(); fixFamily(true, false); return; }
      const preTarget = isT7 ? machine.target : undefined;
      const fixed = isT7 ? machine.fixPiece(shuffleBag(), makeHolesFn(constants.WM))
                         : machine.fixPiece(shuffleBag());
      if (fixed) {
        onLocked(pre.preClearGrid, pre.rows, false);
        maybeAnimateGarbage(garbageBefore);
      }
      fixFamily(fixed, true, preTarget);
    }
    function doDrop() {
      const s1 = getS1();
      const pre = precomputeLock(machine.gy, s1.px); // dropPiece relocates to gy first
      const garbageBefore = isT7 ? machine.garbage : 0;
      const preTarget = isT7 ? machine.target : undefined;
      const fixed = isT7 ? machine.dropPiece(shuffleBag(), makeHolesFn(constants.WM))
                         : machine.dropPiece(shuffleBag());
      if (fixed) {
        onLocked(pre.preClearGrid, pre.rows, true);
        maybeAnimateGarbage(garbageBefore);
      }
      fixFamily(fixed, true, preTarget);
    }
    function doRotate(cw) {
      const fired = machine.rotatePiece(cw) || machine.rotateKickPiece(cw);
      if (fired) sfx.rotate();
      fixFamily(fired, false);
    }
    return {
      LEFT:  { repeat: true,  effect: () => { const f = machine.movePiece(0, -1); if (f) sfx.move(); fixFamily(f, false); } },
      RIGHT: { repeat: true,  effect: () => { const f = machine.movePiece(0, 1); if (f) sfx.move(); fixFamily(f, false); } },
      DOWN:  { repeat: true,  effect: () => doFall() },
      CCW:   { repeat: false, effect: () => doRotate(false) },
      CW:    { repeat: false, effect: () => doRotate(true) },
      HOLD:  { repeat: false, effect: () => { const f = machine.holdPiece(shuffleBag()); if (f) sfx.hold(); fixFamily(f, false); } },
      DROP:  { repeat: false, effect: () => doDrop() },
    };
  }

  function resetInput() {
    keyHeld = new Set();
    prevHeld = {};
    repeatTimers = {};
  }

  // Recomputes gravity's period for whichever machine is active right now and
  // restarts the accumulator fresh, discarding whatever had already accumulated
  // toward the previous period — used both when the active machine itself
  // changes (waiting room <-> match) and when its level changes.
  function retargetGravity(now = performance.now()) {
    const m = activeMachine();
    currentGravityPeriod = fallPeriod(m ? m.level : 1);
    prevLevel = m ? m.level : 1;
    lastGravityAt = now;
    gravityRunning = true;
  }

  function stopGravity() {
    gravityRunning = false;
  }

  function onTick() {
    const m = activeMachine();
    if (!m) return;
    const isT7 = (m === t7machine);
    const actions = actionsFor(m, isT7);
    actions.DOWN.effect();
  }

  function computeHeld() {
    const held = {};
    for (const name of keyHeld) held[name] = true;
    const gp = navigator.getGamepads?.()?.[0];
    if (gp) for (const [idx, name] of GAMEPAD_MAP) if (gp.buttons[idx]?.pressed) held[name] = true;
    return held;
  }

  function processGameInput(now) {
    const m = activeMachine();
    if (!m) return;
    const isT7 = (m === t7machine);
    const held = computeHeld();
    // Filler (SP) game has no host/match to wait on — any keypress after its
    // own gameover just starts a fresh one, same as ordinary SP restart —
    // but only once the lockout window has passed.
    if (!isT7 && m.gameover) {
      const canRestart = gameoverAt !== null && now - gameoverAt >= RESTART_LOCKOUT_MS;
      const anyPressed = Object.keys(held).some((name) => held[name] && !prevHeld[name]);
      if (canRestart && anyPressed) enterWaitingRoom();
      prevHeld = held;
      return;
    }
    const actions = actionsFor(m, isT7);
    for (const name of Object.keys(actions)) {
      const act = actions[name];
      if (act.repeat) {
        if (held[name]) {
          const t = repeatTimers[name];
          if (!t) { act.effect(); repeatTimers[name] = { pressedAt: now, lastFire: now }; }
          else if (now - t.pressedAt >= DAS_DELAY && now - t.lastFire >= ARR) { act.effect(); t.lastFire = now; }
        } else repeatTimers[name] = null;
      } else if (held[name] && !prevHeld[name]) act.effect();
    }
    prevHeld = held;
  }

  // ── menu navigation (S1/S2/S3/S4/S9/S10) — gamepad drives focus, button 0 clicks ──
  function processMenuInput() {
    const active = document.activeElement;
    if (active && (active.tagName === 'INPUT' || active.tagName === 'TEXTAREA')) return;
    const buttons = menuButtons();
    if (buttons.length === 0) return;
    const gp = navigator.getGamepads?.()?.[0];
    const held = {};
    if (gp) { held.up = gp.buttons[12]?.pressed; held.down = gp.buttons[13]?.pressed; held.a = gp.buttons[0]?.pressed; }
    if (held.down && !prevMenuHeld.down) { focusIndex = (focusIndex + 1) % buttons.length; buttons[focusIndex]?.focus(); }
    if (held.up && !prevMenuHeld.up) { focusIndex = (focusIndex - 1 + buttons.length) % buttons.length; buttons[focusIndex]?.focus(); }
    if (held.a && !prevMenuHeld.a) buttons[focusIndex]?.click();
    prevMenuHeld = held;
  }

  // ── render loop ──
  function frame(now) {
    if (screen === 'S6' || screen === 'S7') processGameInput(now);
    else processMenuInput();

    const m = activeMachine();
    if (gravityRunning && m && !m.gameover && now - lastGravityAt >= currentGravityPeriod) {
      lastGravityAt = now;
      onTick();
    }

    if (banner && now - banner.t > BANNER_MS) banner = null;

    if (m) {
      const isT7 = (m === t7machine);
      const snap = isT7 ? t7eng.snapshot(m) : T6Eng.snapshot(m);
      const opps = t7machine ? opponents.filter((o) => o) : [];
      const target = t7machine ? t7machine.target : null;

      if (clearAnim) {
        const t = (now - clearAnim.start) / clearAnim.duration;
        if (t >= 1) {
          clearAnim = null;
          canvas.style.transform = '';
        } else {
          const isTetris = clearAnim.lines === 4;
          const progress = isTetris ? tetrisCurve(t) : normalCurve(t);
          renderClearFlash(canvas, constants, snap, clearAnim.grid, clearAnim.rows, progress, PieceColor);
          if (isTetris) {
            const amp = SHAKE_AMPLITUDE * (1 - t);
            const dx = (Math.random() * 2 - 1) * amp;
            const dy = (Math.random() * 2 - 1) * amp;
            canvas.style.transform = `translate(${dx.toFixed(1)}px, ${dy.toFixed(1)}px)`;
          }
          window.requestAnimationFrame(frame);
          return;
        }
      } else if (garbageAnim) {
        // Never starts until clearAnim (above) has finished — matches the
        // model's own sequencing (a fix's own clear resolves before
        // materialization), not just a rendering convenience.
        const t = (now - garbageAnim.start) / garbageAnim.duration;
        if (t >= 1) {
          garbageAnim = null;
          canvas.style.transform = '';
        } else {
          render(canvas, constants, snap, PieceColor, banner, opps, target);
          drawGarbageFlash(canvas, constants, garbageAnim.rowCount, t);
          const amp = GARBAGE_SHAKE_BASE * Math.min(2, garbageAnim.rowCount / 2) * (1 - t);
          const dx = (Math.random() * 2 - 1) * amp;
          const dy = (Math.random() * 2 - 1) * amp;
          canvas.style.transform = `translate(${dx.toFixed(1)}px, ${dy.toFixed(1)}px)`;
          window.requestAnimationFrame(frame);
          return;
        }
      }

      const inLockout = !isT7 && m.gameover && gameoverAt !== null && (now - gameoverAt < RESTART_LOCKOUT_MS);
      if (inLockout) {
        const gridAreaWidth = constants.gridAreaWidth ?? canvas.width;
        const cellSize = Math.min((gridAreaWidth - 2 * constants.PANEL_PX) / constants.WM, canvas.height / constants.HM);
        render(canvas, constants, { ...snap, gameover: false }, PieceColor, banner, opps, target);
        drawGameOverPartial(canvas, constants, cellSize);
      } else if (screen === 'S9') {
        // S9's own HTML overlay already carries the win/lose text and
        // Rematch/Leave buttons — the shared render()'s built-in "GAME OVER
        // / press any button to restart" is t6/model.js's single-player
        // restart flow (there's no "any button" action here) and would be
        // wrong to show behind it, so gameover is suppressed for this
        // render only. The frozen board itself is unaffected — cell
        // contents don't depend on the gameover flag.
        render(canvas, constants, { ...snap, gameover: false }, PieceColor, banner, opps, target);
      } else {
        render(canvas, constants, snap, PieceColor, banner, opps, target);
      }
    }
    window.requestAnimationFrame(frame);
  }

  function sizeCanvas() {
    const PANEL_FRAC = 0.22, PANEL_MIN = 120, PANEL_MAX = 360;
    const MINI_STRIP_FRAC = 0.25; // fixed relative to viewport — §14.2
    const vw = window.innerWidth, vh = window.innerHeight;
    const totalPanel = Math.min(PANEL_MAX, Math.max(PANEL_MIN, Math.round(PANEL_FRAC * vw)));
    const panel = totalPanel / 2;
    const gridMaxW = vw * (1 - MINI_STRIP_FRAC) - 2 * panel;
    const gridMaxH = vh * 0.95;
    const cell = Math.max(1, Math.floor(Math.min(gridMaxW / constants.WM, gridMaxH / constants.HM)));
    constants.PANEL_PX = panel;
    const gridAreaWidth = 2 * panel + constants.WM * cell;
    constants.gridAreaWidth = gridAreaWidth;
    canvas.width = gridAreaWidth + Math.round(vw * MINI_STRIP_FRAC);
    canvas.height = constants.HM * cell;
  }

  // ── DOM wiring ──
  function renderS3Joiners() {
    const el = document.getElementById('s3-joiners');
    el.innerHTML = '';
    const joined = playerData.slice(1).filter((p) => p.joined);
    for (const p of joined) {
      const div = document.createElement('div');
      div.textContent = p.name;
      el.appendChild(div);
    }
    document.getElementById('s3-start-btn').disabled = joined.length < 1;
  }
  function renderS6Joiners() {
    const el = document.getElementById('s6-joiners');
    el.innerHTML = '';
    roster.forEach((n, i) => {
      const div = document.createElement('div');
      div.textContent = i === myIndex ? `${n} (you)` : n;
      el.appendChild(div);
    });
  }

  document.addEventListener('click', async (e) => {
    const action = e.target?.dataset?.action;
    if (!action) return;
    switch (action) {
      case 'sp': {
        const { main: spMain } = await import('./sp_controller.js');
        root.querySelectorAll('.overlay').forEach((el) => el.remove());
        spMain(canvas, root);
        break;
      }
      case 'mp': showScreen('S2'); break;
      case 'host': {
        isHost = true;
        myIndex = 0;
        myName = document.getElementById('s3-name').value || 'Host';
        playerData = [{ name: myName, conn: null, lastHeard: performance.now(), declaredDisconnected: false }];
        renderS3Joiners();
        showScreen('S3');
        break;
      }
      case 'join': showScreen('S4'); break;

      case 's3-add-connection': {
        const block = document.createElement('div');
        block.className = 'pending-block';
        block.innerHTML = `
          <div class="small">Paste joiner's offer:</div>
          <textarea class="s3-offer-input"></textarea>
          <div><button class="s3-offer-paste">Paste</button>
          <button class="s3-offer-add">Add</button>
          <button class="s3-offer-cancel">Cancel</button></div>
        `;
        document.getElementById('s3-pending').appendChild(block);
        const offerInput = block.querySelector('.s3-offer-input');
        offerInput.focus();
        const offerText = await new Promise((resolve) => {
          block.querySelector('.s3-offer-paste').addEventListener('click', async () => {
            try {
              offerInput.value = await navigator.clipboard.readText();
            } catch (err) {
              console.warn('[T7] Clipboard paste failed — paste manually instead.', err);
            }
          });
          block.querySelector('.s3-offer-add').addEventListener('click', () => resolve(offerInput.value));
          block.querySelector('.s3-offer-cancel').addEventListener('click', () => resolve(null));
        });
        if (!offerText) { block.remove(); return; }
        const { pc, dcPromise, sdpText } = await createAnswerConnection(offerText);
        const idx = playerData.length;
        playerData.push({ name: `player${idx}`, conn: null, lastHeard: performance.now(), declaredDisconnected: false, joined: false });
        block.innerHTML = `
          <div class="small">Answer — copy to joiner:</div>
          <textarea readonly></textarea>
          <button class="s3-answer-copy">Copy</button>
        `;
        block.querySelector('textarea').value = sdpText;
        block.querySelector('.s3-answer-copy').addEventListener('click', async () => {
          try {
            await navigator.clipboard.writeText(sdpText);
          } catch (err) {
            console.warn('[T7] Clipboard copy failed — copy manually instead.', err);
          }
        });
        const dc = await dcPromise;
        playerData[idx].conn = dc;
        playerData[idx].pc = pc;
        dc.onmessage = (ev) => hostHandleFromJoiner(idx, JSON.parse(ev.data));
        watchConnection(pc, () => declarePlayerDisconnected(idx));
        block.remove();
        break;
      }
      case 's3-start': {
        // A slot can exist (via "Add connection") without ever having sent
        // JOIN — startMatch()'s Player roster is every index in playerData,
        // joined or not, so a stray not-yet-joined slot would otherwise be
        // dealt into the match as a phantom player. Same for a slot that did
        // join but was later declared disconnected (mid-previous-match, or
        // while waiting here): its connection is actually gone, so dealing
        // it into a fresh Init — which always sets connected := true — would
        // start the match in a state that doesn't correspond to any real
        // T7.v Init. Evict from the end backwards so removing one doesn't
        // shift the index of another one still pending eviction in this
        // same pass.
        for (let i = playerData.length - 1; i >= 1; i--) {
          if (!playerData[i] || !playerData[i].joined || playerData[i].declaredDisconnected) evictSlot(i);
        }
        renderS3Joiners();
        // Eviction can shift a still-joined survivor's index (e.g. an
        // earlier-added, still-unjoined slot evicted while a later-added one
        // has already joined) — resend PLAYERS so every survivor's local
        // roster/myIndex match this new indexing before START (below) tells
        // them to build Player/t7machine from it. Synchronous with no await
        // in this branch, and the data channels are ordered, so PLAYERS is
        // guaranteed to be processed before START on every survivor.
        broadcastPlayers();
        matchGen++;
        // "joined" tracks readiness for the *current* open lobby round; a
        // match starting consumes that readiness, so it's reset here — not
        // on the host's rematch click, which can happen either before or
        // after a given joiner's own rematch/JOIN and must not clobber one
        // that already arrived (see 's9-rematch' below).
        for (let i = 1; i < playerData.length; i++) {
          if (!playerData[i]) continue;
          playerData[i].joined = false;
          playerData[i].declaredDisconnected = false;
          playerData[i].lastHeard = performance.now();
        }
        for (let i = 1; i < playerData.length; i++) sendToPlayer(i, { type: 'START', gen: matchGen });
        showScreen('S7');
        startMatch();
        startHeartbeat();
        break;
      }

      case 's4-copy-offer': {
        try {
          await navigator.clipboard.writeText(document.getElementById('s4-offer').value);
        } catch (err) {
          console.warn('[T7] Clipboard copy failed — copy manually instead.', err);
        }
        break;
      }
      case 's4-paste-answer': {
        try {
          document.getElementById('s4-answer').value = await navigator.clipboard.readText();
        } catch (err) {
          console.warn('[T7] Clipboard paste failed — paste manually instead.', err);
        }
        break;
      }

      case 's4-connect': {
        myName = document.getElementById('s4-name').value || 'Player';
        const answerText = document.getElementById('s4-answer').value;
        if (!hostPc || hostPc.signalingState !== 'have-local-offer') {
          // Already negotiated (e.g. a stray repeat click) or not ready yet —
          // setRemoteDescription would throw InvalidStateError ("wrong state:
          // stable") instead of doing anything useful here.
          console.warn('[T7] Ignoring Connect click — connection not awaiting an answer.');
          return;
        }
        await applyAnswer(hostPc, answerText);
        hostLostHandled = false;
        watchConnection(hostPc, () => noticeHostLost());
        hostConn.onmessage = (ev) => joinerHandleFromHost(JSON.parse(ev.data));
        // The data channel isn't usable the instant the answer is applied —
        // ICE/DTLS still has to finish connecting. Waiting for 'open' here,
        // rather than relying on sendToHost's own fail-fast path, avoids
        // treating this ordinary startup delay as a lost connection (there is
        // no t7.Machine yet at this point for noticeHostLost to act on
        // anyway — it would just bounce to S1).
        if (hostConn.readyState !== 'open') {
          await new Promise((resolve) => { hostConn.onopen = resolve; });
        }
        lastHostMessageAt = performance.now();
        sendToHost({ type: 'JOIN', name: myName });
        showScreen('S6');
        enterWaitingRoom();
        startHeartbeat();
        break;
      }

      case 's9-rematch': {
        if (isHost) {
          // Reused connections keep their slot/fromIdx from the first match —
          // that index is baked into each dc.onmessage closure set up back in
          // 's3-add-connection', and a rematching joiner resends JOIN over
          // that very same channel (no fresh offer/answer). playerData must
          // not be truncated here: doing so would discard those live
          // connections and could make hostHandleJoin's own
          // `playerData[fromIdx].name = ...` write land out of range.
          // `joined`/`name`/etc. are intentionally left untouched here:
          // a joiner's own rematch click (and JOIN) can race ahead of this
          // one, and 's3-start' is what actually resets readiness for the
          // round — clobbering it here would drop a JOIN that already
          // arrived, with no way for that joiner to resend it.
          renderS3Joiners();
          document.getElementById('s3-pending').innerHTML = '';
          showScreen('S3');
        } else {
          hostLostHandled = false;
          sendToHost({ type: 'JOIN', name: myName });
          // t7machine stays alive after a match ends (used by findWinner()/
          // opponents while on the winner screen); the pre-match filler that
          // follows is plain SP and must not keep showing the finished
          // match's mini-grids, which frame()'s `opps` computation gates on
          // t7machine being truthy.
          t7machine = null;
          opponents = [];
          showScreen('S6');
          enterWaitingRoom();
          startHeartbeat();
        }
        break;
      }
      case 's9-leave':
        if (!isHost && hostConn) sendToHost({ type: 'LEAVE', from: myIndex });
        stopHeartbeat();
        stopStateTimer();
        stopGravity();
        t7machine = null; t6machine = null; hostConn = null; hostPc = null;
        showScreen('S1');
        break;
      case 's10-menu':
        stopHeartbeat();
        stopStateTimer();
        stopGravity();
        t7machine = null; t6machine = null; hostConn = null; hostPc = null;
        showScreen('S1');
        break;
    }
  });

  // Join screen: generate our own offer as soon as we arrive there.
  const originalShowScreen = showScreen;
  let generatingOffer = false;
  document.getElementById('S2').querySelector('[data-action="join"]')
    .addEventListener('click', async () => {
      if (generatingOffer) return; // ICE gathering can take a few seconds on
      // a real network (unlike same-machine loopback); without this guard, an
      // impatient repeat click could kick off a second, overlapping connection
      // that races the first one for hostPc/hostConn — whichever finishes last
      // would win, regardless of which offer the user actually copied and sent.
      generatingOffer = true;
      const btn = document.getElementById('S2').querySelector('[data-action="join"]');
      btn.disabled = true;
      try {
        document.getElementById('s4-name').value = myName || '';
        document.getElementById('s4-answer').value = '';
        const { pc, dc, sdpText } = await createOfferConnection();
        hostPc = pc; hostConn = dc;
        document.getElementById('s4-offer').value = sdpText;
      } finally {
        generatingOffer = false;
        btn.disabled = false;
      }
    });

  document.addEventListener('keydown', (e) => {
    const name = KEYMAP.get(e.key);
    if (name && (screen === 'S6' || screen === 'S7')) { e.preventDefault(); keyHeld.add(name); }
  });
  document.addEventListener('keyup', (e) => {
    const name = KEYMAP.get(e.key);
    if (name) keyHeld.delete(name);
  });

  sizeCanvas();
  window.addEventListener('resize', sizeCanvas);
  showScreen('S1');
  window.requestAnimationFrame(frame);
}
