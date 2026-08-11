// oracle.js — an independent, literal interpreter of T4.v. Reuses T3's oracle
// (`t3/tests/oracle.js`) for the embedded s3 state (exactly as T4.v embeds
// T3.State), and hand-rolls isPieceSet/drawOnce/initPieceAndDraw independently
// of `model.js` — a bug shared between the translation and the helper it
// reuses would still surface as a mismatch here. Deliberately written in a
// different style (manual pairwise duplicate check instead of `Set`) for the
// same reason.

import { oracle3 } from '../../t3/tests/oracle.js';

// spec: Bijective / PieceSet — independent hand-roll (see file header)
function isPieceSet(arr, numPieces) {
  if (arr.length !== numPieces) return false;
  for (let i = 0; i < arr.length; i++)
    for (let j = i + 1; j < arr.length; j++)
      if (arr[i] === arr[j]) return false;
  return true;
}

// spec: DrawNextPiece d bagNew — independent hand-roll (see file header)
function drawOnce(bag_, next_, bagNew) {
  const resetting = bag_.length === 1;
  const p = next_.shift();
  next_.push(bag_.pop());
  if (resetting) for (const x of bagNew) bag_.push(x);
  return { p, resetting };
}

// spec: BuildInitNext + InitPieceAndDraw — independent hand-roll
function initPieceAndDraw(bagsFn, nextLen) {
  const bag_ = bagsFn(0).slice();
  const next_ = new Array(nextLen).fill(bagsFn(0)[0]);
  let bagIdx = 1;
  for (let k = 0; k < nextLen; k++) {
    const { resetting } = drawOnce(bag_, next_, bagsFn(bagIdx));
    if (resetting) bagIdx += 1;
  }
  const { p } = drawOnce(bag_, next_, bagsFn(bagIdx));
  return { p, bag_, next_ };
}

function makeParams4(TI) {
  return { ...oracle3.makeParams(TI), NextLen: TI.NextLen };
}

function initState4(bagsFn, params) {
  const { p, bag_, next_ } = initPieceAndDraw(bagsFn, params.NextLen);
  return { s3: oracle3.initState3(p, params), bag_, next_ };
}

function movePiece4(dy, dx, s, params) {
  const s3p = oracle3.movePiece3(dy, dx, s.s3, params);
  return s3p ? { ...s, s3: s3p } : null;
}

function rotatePiece4(cw, s, params) {
  const s3p = oracle3.rotatePiece3(cw, s.s3, params);
  return s3p ? { ...s, s3: s3p } : null;
}

// spec: FixPiece bagNew H — peek next_[0], only commit the draw once T3 confirms.
function fixPiece4(bagNew, s, params) {
  const p = s.next_[0];
  const s3p = oracle3.fixPiece3(p, s.s3, params);
  if (!s3p) return null; // guard-fail: bag_/next_ untouched
  const bag_ = s.bag_.slice(), next_ = s.next_.slice();
  drawOnce(bag_, next_, bagNew); // commit now that T3 is confirmed to fire
  return { s3: s3p, bag_, next_ };
}

function fallStep4(bagNew, s, params) {
  return movePiece4(-1, 0, s, params) ?? fixPiece4(bagNew, s, params);
}

// spec: HoldPiece bagNew H — draw only in the hold===null branch (skip-vs-discard).
function holdPiece4(bagNew, s, params) {
  const snap = oracle3.snapshotOf3(s.s3);
  if (snap.gameover) return null;
  const bag_ = s.bag_.slice(), next_ = s.next_.slice();
  let p2;
  if (snap.hold !== null) {
    p2 = snap.hold; // skip: bag_/next_ (the copies above) stay untouched
  } else {
    const drawn = drawOnce(bag_, next_, bagNew); // commit: T3 guaranteed to fire here
    p2 = drawn.p;
  }
  const s3p = oracle3.holdPiece3(p2, s.s3, params);
  if (!s3p) return null;
  return { s3: s3p, bag_, next_ };
}

function snapshotOf4(s) {
  return {
    ...oracle3.snapshotOf3(s.s3),
    next: s.next_.slice(),
  };
}

function states4Equal(a, b) {
  return JSON.stringify(snapshotOf4(a)) === JSON.stringify(snapshotOf4(b));
}

export const oracle4 = {
  makeParams4,
  isPieceSet,
  drawOnce,
  initPieceAndDraw,
  initState4,
  movePiece4,
  rotatePiece4,
  fixPiece4,
  fallStep4,
  holdPiece4,
  snapshotOf4,
  states4Equal,
};
