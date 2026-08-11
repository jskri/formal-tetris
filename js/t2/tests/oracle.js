// oracle.js — an independent, literal interpreter of T2.v. Reuses T1's oracle
// (`t1/tests/oracle.js`) for the embedded s1 state (exactly as T2.v embeds
// T1.State), and hand-rolls the five new scalar fields independently of
// `lib/utils.js` / `model.js`, so a bug shared between the translation and its
// helper module would still surface as a mismatch here.

import { oracle as t1oracle } from '../../t1/tests/oracle.js';

function natSub(a, b) { return a > b ? a - b : 0; }
function natDiv(a, b) { return Math.floor(a / b); }
function capAdd(a, b, max) { return b > max - a ? max : a + b; }

function lineClearPoints(clearedLines, level) {
  if (clearedLines === 0) return 0;
  if (clearedLines === 1) return 100 * level;
  if (clearedLines === 2) return 300 * level;
  if (clearedLines === 3) return 500 * level;
  return 800 * level;
}

function comboPoints(level, combo) {
  return combo > 0 ? 50 * combo * level : 0;
}

function perfectClearPoints(perfectClear, clearedLines, level) {
  if (!perfectClear) return 0;
  if (clearedLines === 0) return 0;
  if (clearedLines === 1) return 800 * level;
  if (clearedLines === 2) return 1200 * level;
  if (clearedLines === 3) return 1800 * level;
  return 2000 * level;
}

function points(clearedLines, level, combo, perfectClear) {
  return lineClearPoints(clearedLines, level)
       + comboPoints(level, combo)
       + perfectClearPoints(perfectClear, clearedLines, level);
}

function emptyGridb(g) {
  for (const row of g) for (const c of row) if (c) return false;
  return true;
}

const MAX = Number.MAX_SAFE_INTEGER;

function initState(p, params) {
  return {
    s1: t1oracle.initState(p, params),
    score: 0,
    level: 1,
    combo: 0,
    perfectClear: false,
    totalClearedLines: 0,
  };
}

function movePiece(dy, dx, s, params) {
  const s1p = t1oracle.movePiece(dy, dx, s.s1, params);
  return s1p ? { ...s, s1: s1p } : null;
}

function rotatePiece(cw, s, params) {
  const s1p = t1oracle.rotatePiece(cw, s.s1, params);
  return s1p ? { ...s, s1: s1p } : null;
}

function fixPiece(pNew, s, params) {
  const s1p = t1oracle.fixPiece(pNew, s.s1, params);
  if (!s1p) return null;
  const clearedLines = s1p.clearedLines;
  const combo2 = (clearedLines === 0) ? 0 : capAdd(s.combo, 1, MAX);
  const perfectClear2 = emptyGridb(t1oracle.snapshotOf(s1p).mg);
  const pts = points(clearedLines, s.level, natSub(combo2, 1), perfectClear2);
  const total2 = capAdd(s.totalClearedLines, clearedLines, MAX);
  return {
    s1: s1p,
    combo: combo2,
    perfectClear: perfectClear2,
    score: capAdd(s.score, pts, MAX),
    totalClearedLines: total2,
    level: 1 + natDiv(total2, 10),
  };
}

function fallStep(pNew, s, params) {
  return movePiece(-1, 0, s, params) ?? fixPiece(pNew, s, params);
}

function snapshotOf(s) {
  return {
    ...t1oracle.snapshotOf(s.s1),
    score: s.score,
    level: s.level,
    combo: s.combo,
    perfectClear: s.perfectClear,
    totalClearedLines: s.totalClearedLines,
  };
}

function states2Equal(a, b) {
  return JSON.stringify(snapshotOf(a)) === JSON.stringify(snapshotOf(b));
}

export const oracle2 = {
  makeParams: t1oracle.makeParams,
  initState,
  movePiece,
  rotatePiece,
  fixPiece,
  fallStep,
  snapshotOf,
  states2Equal,
};
