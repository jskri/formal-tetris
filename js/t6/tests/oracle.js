// oracle.js — an independent, literal interpreter of T6.v. T6.State is T5.State
// itself (no new record), so this oracle reuses T5's oracle state shape directly
// rather than wrapping it, and hand-rolls canRotatePiece/mod independently of
// `model.js`/`t1/model.js` — a bug shared between the translation and a helper
// it reuses would still surface as a mismatch here.

import { oracle5 } from '../../t5/tests/oracle.js';

function mod(a, n) { return ((a % n) + n) % n; }

// spec: (the guard inside T6.RotateKickPiece that computes plainRotFires) —
// independent hand-roll, not imported from t1/model.js's canRotatePiece.
function canRotatePiece(cw, s1, params) {
  const pr2 = mod(s1.pr + (cw ? -1 : 1), 4);
  return !s1.gameover && params.valid(s1.mg, s1.p, s1.py, s1.px, pr2);
}

// Replaces the innermost s1 inside a T5-oracle-shaped state, leaving every
// other field (gy, bag_, next_, hold, swapped, score, level, combo,
// perfectClear, totalClearedLines) untouched.
function withS1(s, newS1) {
  return {
    ...s,
    s4: {
      ...s.s4,
      s3: {
        ...s.s4.s3,
        s2: { ...s.s4.s3.s2, s1: newS1 },
      },
    },
  };
}

// spec: RotateKickPiece cw s (T6.v, exclusive form) — independent hand-roll.
function rotateKickPiece6(cw, s, params) {
  const s1 = s.s4.s3.s2.s1;
  if (canRotatePiece(cw, s1, params)) return null; // plain would fire — exclusive
  const origPx = s1.px;
  const left = oracle5.rotatePiece5(cw, withS1(s, { ...s1, px: origPx - 1 }), params);
  if (left) return left;
  const right = oracle5.rotatePiece5(cw, withS1(s, { ...s1, px: origPx + 1 }), params);
  if (right) return right;
  return null;
}

function snapshotOf6(s) {
  return oracle5.snapshotOf5(s); // T6.State = T5.State: identical shape, identical snapshot
}

export const oracle6 = {
  makeParams6: oracle5.makeParams5,
  initState6: oracle5.initState5,
  movePiece6: oracle5.movePiece5,
  rotatePiece6: oracle5.rotatePiece5,
  fixPiece6: oracle5.fixPiece5,
  fallStep6: oracle5.fallStep5,
  holdPiece6: oracle5.holdPiece5,
  dropPiece6: oracle5.dropPiece5,
  rotateKickPiece6,
  snapshotOf6,
};
