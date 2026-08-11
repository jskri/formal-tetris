// oracle.js — an independent, literal interpreter of T7.v. Reuses oracle6 for
// each player's own T6-level (piece/grid/hold/kick) semantics directly — T7
// changes nothing about a single player's own piece physics — and hand-rolls
// everything genuinely new to T7 independently of model.js: garbage
// generation/cancellation/materialization, target round-robin, and the
// message-queue/view/disconnect machinery. A bug shared between the
// translation and a helper it reuses would still surface as a mismatch here.
//
// State shape (plain object, the *whole* multiplayer system — matches
// proofs.md's Σ, not any single Machine):
//   { s6: [oracle6-state, ...]        indexed by Player
//   , garbage: [n, ...]
//   , target: [pl, ...]
//   , remGenGarbage: [n, ...]         mirrors model.js's own sticky field
//   , gameoverView: [[bool,...], ...] [obs][obsd]
//   , connectedView: [[bool,...], ...]
//   , connected: [bool, ...]          ground truth — oracle-only, no model.js
//                                     field holds this (§6.9)
//   , messages: [[[msg,...],...],...] [from][to] FIFO queues, oracle-only
//   }
// msg: { type: 'garbage', n } | { type: 'gameover' } | { type: 'disconnect' }

import { oracle as oracle1 } from '../../t1/tests/oracle.js';
import { oracle6 } from '../../t6/tests/oracle.js';

function makeEmptyQueues(n) {
  return Array.from({ length: n }, () => Array.from({ length: n }, () => []));
}
function cloneMessages(messages) {
  return messages.map((row) => row.map((q) => q.slice()));
}

// spec: PlayingView s pl pl2
function playingView7(gameoverViewRow, connectedViewRow, pl2) {
  return !gameoverViewRow[pl2] && connectedViewRow[pl2];
}

// spec: WinnerMulti s pl
function winnerMulti7(s, pl, params) {
  if (params.PlayerCount <= 1) return false;
  for (let pl2 = 0; pl2 < params.PlayerCount; pl2++) {
    if (playingView7(s.gameoverView[pl], s.connectedView[pl], pl2) !== (pl2 === pl)) return false;
  }
  return true;
}

// spec: NextTargetAux / NextTarget
function nextTarget7(playing, self, pl, params) {
  let cur = pl;
  for (let i = 0; i < params.PlayerCount; i++) {
    cur = params.PlayerNext(cur);
    if (playing(cur) && cur !== self) return cur;
  }
  return self;
}

// spec: GeneratedGarbage
function generatedGarbage7(clearedLines, perfectClear) {
  const normal = clearedLines < 4 ? Math.max(0, clearedLines - 1) : clearedLines;
  return normal + (perfectClear ? 10 : 0);
}

// spec: GenRemGarbage
function genRemGarbage7(garbage, clearedLines, perfectClear) {
  const gen = generatedGarbage7(clearedLines, perfectClear);
  return [gen, Math.max(0, garbage - gen)];
}

// spec: GarbageGrid garbage holes w — YX = (0,0), lazy: holesFn(y) is only
// ever actually invoked for rows a later subseteq/materialize call samples,
// so this naturally matches model.js's "only query effRem rows" without
// needing an explicit clamp (§4-T7c's clamp is an array-representation
// necessity that the functional representation doesn't share).
function garbageGrid7(garbage, holesFn, w) {
  return oracle1.mkGrid((y, x) => (0 <= y && y < garbage && 0 <= x && x < w && x !== holesFn(y)), garbage, w, 0, 0);
}

// Replaces the innermost s1 inside an oracle6-shaped state, mirroring
// oracle6.js's own (non-exported) withS1 — independent hand-roll, same reason
// oracle6 hand-rolls its own canRotatePiece rather than importing one.
function withS1_6(s6, newS1) {
  return {
    ...s6,
    s4: { ...s6.s4, s3: { ...s6.s4.s3, s2: { ...s6.s4.s3.s2, s1: newS1 } } },
  };
}

function makeParams7(TI) {
  const base = oracle6.makeParams6(TI);
  return {
    ...base,
    WM: TI.InitialMainGrid[0].length,
    PlayerCount: TI.Player.length,
    PlayerNext: (i) => (i + 1) % TI.Player.length,
    HostIndex: TI.HostIndex,
  };
}

function initState7(bagsFnPerPlayer, params) {
  const n = params.PlayerCount;
  const s6 = [];
  for (let pl = 0; pl < n; pl++) s6.push(oracle6.initState6(bagsFnPerPlayer[pl], params));
  const gameoverView = Array.from({ length: n }, (_, obs) =>
    Array.from({ length: n }, (_, obsd) => (obsd === obs ? oracle6.snapshotOf6(s6[obs]).gameover : false)));
  return {
    s6,
    garbage: Array(n).fill(0),
    target: Array.from({ length: n }, (_, pl) => params.PlayerNext(pl)),
    remGenGarbage: Array(n).fill(0),
    gameoverView,
    connectedView: Array.from({ length: n }, () => Array(n).fill(true)),
    connected: Array(n).fill(true),
    messages: makeEmptyQueues(n),
  };
}

// spec: MovePiece pl dyx s
function movePiece7(pl, dy, dx, s, params) {
  if (winnerMulti7(s, pl, params)) return null;
  const s6New = oracle6.movePiece6(dy, dx, s.s6[pl], params);
  if (!s6New) return null;
  const s6 = s.s6.slice(); s6[pl] = s6New;
  return { ...s, s6 };
}

// spec: RotatePiece pl cw s
function rotatePiece7(pl, cw, s, params) {
  if (winnerMulti7(s, pl, params)) return null;
  const s6New = oracle6.rotatePiece6(cw, s.s6[pl], params);
  if (!s6New) return null;
  const s6 = s.s6.slice(); s6[pl] = s6New;
  return { ...s, s6 };
}

// spec: HoldPiece pl bagNew H s
function holdPiece7(pl, bagNew, s, params) {
  if (winnerMulti7(s, pl, params)) return null;
  const s6New = oracle6.holdPiece6(bagNew, s.s6[pl], params);
  if (!s6New) return null;
  const s6 = s.s6.slice(); s6[pl] = s6New;
  return { ...s, s6 };
}

// spec: RotateKickPiece pl cw s
function rotateKickPiece7(pl, cw, s, params) {
  if (winnerMulti7(s, pl, params)) return null;
  const s6New = oracle6.rotateKickPiece6(cw, s.s6[pl], params);
  if (!s6New) return null;
  const s6 = s.s6.slice(); s6[pl] = s6New;
  return { ...s, s6 };
}

// spec: FixPiece pl holes H1 bagNew H2 s (materializing branch — always taken,
// PlayerCount > 1 in every test fixture)
function fixPiece7(pl, holesFn, bagNew, s, params) {
  if (winnerMulti7(s, pl, params)) return null;
  const s6New = oracle6.fixPiece6(bagNew, s.s6[pl], params);
  if (!s6New) return null;

  // s6New is {s4, gy} (mirrors t5_tests_oracle.js's own state shape — oracle6
  // is exactly oracle5) — never flat. mg/gameover are read/written through the
  // nested s1, same path withS1_6 already uses; clearedLines/perfectClear read
  // through the flat snapshot (safe: read-only, snapshotOf6 already handles
  // the mg conversion correctly for it).
  const s1New = s6New.s4.s3.s2.s1;
  const snapNew = oracle6.snapshotOf6(s6New);
  const [genGarbage, remGarbage] = genRemGarbage7(s.garbage[pl], snapNew.clearedLines, snapNew.perfectClear);
  const remGenGarbage = Math.max(0, genGarbage - s.garbage[pl]);

  // spec: let garbageGrid := GarbageGrid remGarbage holes (W InitialMainGrid)
  //       let mg' := garbageGrid ∪ (mg ⊕ (remGarbage, 0))
  //       let croppedMg' := mg' ∩ Full mg
  //       gameover' := T6.gameover s6' || (mg' ⊈ croppedMg') || (ForbiddenGrid ∩ croppedMg' ⊈ ∅)
  // Literal translation, no effRem clamp: gridIntersect crops to oldMg's own
  // box regardless of how large remGarbage is (the whole reason the array
  // representation in model.js needs an explicit clamp and this doesn't).
  const oldMg = s1New.mg;
  const garbageGrid = garbageGrid7(remGarbage, holesFn, params.WM);
  const newMg = oracle1.gridUnion(
                  garbageGrid,
                  oracle1.gridTranslate(oldMg, remGarbage, 0));
  const croppedMg = oracle1.gridIntersect(newMg, oracle1.Full(oldMg));

  const overflow = !oracle1.subseteq(newMg, croppedMg);
  const forbiddenHit = !oracle1.subseteq(oracle1.gridIntersect(params.ForbiddenGrid, croppedMg), oracle1.EmptyGrid);
  const newGameover = s1New.gameover || overflow || forbiddenHit;

  const s6Final = withS1_6(s6New, { ...s1New, mg: croppedMg, gameover: newGameover });
  const s6 = s.s6.slice(); s6[pl] = s6Final;

  const garbage = s.garbage.slice(); garbage[pl] = 0;
  const remGenGarbageArr = s.remGenGarbage.slice(); remGenGarbageArr[pl] = remGenGarbage;

  const gameoverView = s.gameoverView.map((row) => row.slice());
  gameoverView[pl][pl] = newGameover;

  let target = s.target;
  if (remGenGarbage > 0 && !newGameover) {
    target = s.target.slice();
    const playingView = (pl2) => playingView7(gameoverView[pl], s.connectedView[pl], pl2);
    target[pl] = nextTarget7(playingView, pl, s.target[pl], params);
  }

  let messages = s.messages;
  if (s.connected[pl]) {
    messages = cloneMessages(s.messages);
    for (let to = 0; to < params.PlayerCount; to++) {
      if (to === pl) continue;
      if (to === target[pl] && remGenGarbage > 0) messages[pl][to].push({ type: 'garbage', n: remGenGarbage });
      if (newGameover) messages[pl][to].push({ type: 'gameover' });
    }
  }

  return { ...s, s6, garbage, target, remGenGarbage: remGenGarbageArr, gameoverView, messages };
}

// spec: FallStep pl holes H1 bagNew H2 s
function fallStep7(pl, holesFn, bagNew, s, params) {
  if (winnerMulti7(s, pl, params)) return null;
  const moved = movePiece7(pl, -1, 0, s, params);
  if (moved) return moved;
  return fixPiece7(pl, holesFn, bagNew, s, params);
}

// spec: DropPiece pl holes H1 bagNew H2 s := FixPiece ... (NewPieceYXState (gy, px) ...)
function dropPiece7(pl, holesFn, bagNew, s, params) {
  if (winnerMulti7(s, pl, params)) return null;
  const s6 = s.s6[pl];
  const s1 = s6.s4.s3.s2.s1;
  if (s1.gameover) return null;
  const relocated = withS1_6(s6, { ...s1, py: s6.gy });
  const relocatedAll = s.s6.slice(); relocatedAll[pl] = relocated;
  return fixPiece7(pl, holesFn, bagNew, { ...s, s6: relocatedAll }, params);
}

// spec: ReceiveMessage pl from s
function receiveMessage7(pl, from, s, params) {
  if (!s.connected[pl]) return null;
  const q = s.messages[from][pl];
  if (q.length === 0) return null;
  const [msg, ...rest] = q;
  const messages = cloneMessages(s.messages);
  messages[from][pl] = rest;

  if (msg.type === 'garbage') {
    const garbage = s.garbage.slice(); garbage[pl] += msg.n;
    return { ...s, garbage, messages };
  }
  if (msg.type === 'gameover') {
    const gameoverView = s.gameoverView.map((r) => r.slice());
    gameoverView[pl][from] = true;
    let target = s.target;
    if (s.target[pl] === from) {
      target = s.target.slice();
      const view = (pl2) => playingView7(gameoverView[pl], s.connectedView[pl], pl2);
      target[pl] = nextTarget7(view, pl, from, params);
    }
    return { ...s, gameoverView, target, messages };
  }
  // 'disconnect'
  const connectedView = s.connectedView.map((r) => r.slice());
  connectedView[pl][from] = false;
  let target = s.target;
  if (s.target[pl] === from) {
    target = s.target.slice();
    const view = (pl2) => playingView7(s.gameoverView[pl], connectedView[pl], pl2);
    target[pl] = nextTarget7(view, pl, from, params);
  }
  return { ...s, connectedView, target, messages };
}

// spec: DisconnectPlayer pl s — no Machine method exists for this (§4-T7f);
// present in the oracle only, to build disconnect scenarios and to check
// receiveMessage7's 'disconnect' branch and noticeDisconnection7 against it.
function disconnectPlayer7(pl, s, params) {
  if (!s.connected[pl]) return null;
  const connected = s.connected.slice();
  let messages = s.messages;
  if (pl === params.HostIndex) {
    for (let i = 0; i < connected.length; i++) connected[i] = false;
    // no messages sent at all — the host-branch is a pure fact, not a broadcast
  } else {
    connected[pl] = false;
    messages = cloneMessages(s.messages);
    for (let to = 0; to < params.PlayerCount; to++) {
      if (to !== pl) messages[pl][to].push({ type: 'disconnect' });
    }
  }
  return { ...s, connected, messages };
}

// spec: NoticeDisconnection pl s
function noticeDisconnection7(pl, s) {
  const connectedView = s.connectedView.map((r) => r.slice());
  connectedView[pl][pl] = false;
  return { ...s, connectedView };
}

// Matches model.js's snapshot(machine) exactly, field for field, for player `pl`.
function snapshotOf7(s, pl) {
  return {
    ...oracle6.snapshotOf6(s.s6[pl]),
    garbage: s.garbage[pl],
    target: s.target[pl],
    gameoverView: s.gameoverView[pl].slice(),
    connectedView: s.connectedView[pl].slice(),
    remGenGarbage: s.remGenGarbage[pl],
    myIndex: pl,
  };
}

export const oracle7 = {
  makeParams7,
  initState7,
  movePiece7,
  rotatePiece7,
  holdPiece7,
  rotateKickPiece7,
  fixPiece7,
  fallStep7,
  dropPiece7,
  receiveMessage7,
  disconnectPlayer7,
  noticeDisconnection7,
  winnerMulti7,
  playingView7,
  nextTarget7,
  generatedGarbage7,
  genRemGarbage7,
  snapshotOf7,
};
