// oracle.js — an independent, literal interpreter of T3.v. Reuses T2's oracle
// (`t2/tests/oracle.js`) for the embedded s2 state (exactly as T3.v embeds
// T2.State), and hand-rolls HoldPiece's NewPieceState-equivalent independently
// of `t1/model.js`/`model.js` — a bug shared between the translation and the
// helper it reuses (T2Eng.T1Eng.newPieceState) would still surface as a
// mismatch here.

import { oracle2 } from '../../t2/tests/oracle.js';

// spec: NewPieceState p_new s — independent hand-roll (see file header)
function newPieceState(pNew, s1, params) {
  return {
    mg: s1.mg,
    p: pNew,
    py: params.InitialY(pNew),
    px: params.InitialX(pNew),
    pr: 0,
    gameover: s1.gameover,
    clearedLines: s1.clearedLines,
  };
}

function initState3(p, params) {
  return { s2: oracle2.initState(p, params), hold: null, swapped: false };
}

function movePiece3(dy, dx, s, params) {
  const s2p = oracle2.movePiece(dy, dx, s.s2, params);
  return s2p ? { ...s, s2: s2p } : null;
}

function rotatePiece3(cw, s, params) {
  const s2p = oracle2.rotatePiece(cw, s.s2, params);
  return s2p ? { ...s, s2: s2p } : null;
}

function fixPiece3(pNew, s, params) {
  const s2p = oracle2.fixPiece(pNew, s.s2, params);
  if (!s2p) return null;
  return { s2: s2p, hold: s.hold, swapped: false }; // req-hold-limit
}

function fallStep3(pNew, s, params) {
  return movePiece3(-1, 0, s, params) ?? fixPiece3(pNew, s, params);
}

function holdPiece3(pNew, s, params) {
  const gameover = s.s2.s1.gameover;
  if (!(!gameover && !s.swapped)) return null; // real guard (req-hold-limit)
  const p2 = (s.hold !== null) ? s.hold : pNew; // req-hold-swap / req-hold-empty
  const oldP = s.s2.s1.p;                        // read BEFORE overwritten
  const newS1 = newPieceState(p2, s.s2.s1, params);
  return {
    s2: { ...s.s2, s1: newS1 }, // score/level/combo/perfectClear/totalClearedLines untouched
    hold: oldP,                  // req-hold
    swapped: true,                // req-hold-limit
  };
}

function snapshotOf3(s) {
  return {
    ...oracle2.snapshotOf(s.s2),
    hold: s.hold,
    swapped: s.swapped,
  };
}

function states3Equal(a, b) {
  return JSON.stringify(snapshotOf3(a)) === JSON.stringify(snapshotOf3(b));
}

export const oracle3 = {
  makeParams: oracle2.makeParams,
  initState3,
  movePiece3,
  rotatePiece3,
  fixPiece3,
  fallStep3,
  holdPiece3,
  snapshotOf3,
  states3Equal,
};
