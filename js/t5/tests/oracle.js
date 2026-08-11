// oracle.js — an independent, literal interpreter of T5.v. Reuses T4's oracle
// (`t4/tests/oracle.js`) for the embedded s4 state, and hand-rolls shadowY and
// newPieceYXState independently of `model.js`/`t1/model.js` — a bug shared
// between the translation and a helper it reuses would still surface as a
// mismatch here.

import { oracle4 } from '../../t4/tests/oracle.js';

// spec: ShadowYImpl + ShadowY — independent hand-roll (see file header).
// Fuel-bounded: py can go as low as -(PW-1) for a piece whose occupied cells
// sit near the top of its own PW×PW bounding box.
function shadowY(s1, PW, valid) {
  let py = s1.py;
  let fuel = py + PW - 1;
  while (fuel > 0) {
    if (!valid(s1.mg, s1.p, py - 1, s1.px, s1.pr)) break;
    py -= 1;
    fuel -= 1;
  }
  return py;
}

// spec: NewPieceYXState pyNew pxNew s — independent hand-roll. Both coordinates
// are overridden unconditionally; dropPiece5 (below) passes s1.px explicitly to
// keep the column unchanged, mirroring T1.v's NewPieceYXState — which merged the
// narrower, since-removed NewPieceYState (py-only) into this one.
function newPieceYXState(pyNew, pxNew, s1) {
  return {
    mg: s1.mg,
    p: s1.p,
    py: pyNew,
    px: pxNew,
    pr: s1.pr,
    gameover: s1.gameover,
    clearedLines: s1.clearedLines,
  };
}

function initState5(bagsFn, params) {
  const s4 = oracle4.initState4(bagsFn, params);
  const gy = shadowY(s4.s3.s2.s1, params.PW, params.valid);
  return { s4, gy };
}

function movePiece5(dy, dx, s, params) {
  const s4p = oracle4.movePiece4(dy, dx, s.s4, params);
  if (!s4p) return null;
  return { s4: s4p, gy: shadowY(s4p.s3.s2.s1, params.PW, params.valid) };
}

function rotatePiece5(cw, s, params) {
  const s4p = oracle4.rotatePiece4(cw, s.s4, params);
  if (!s4p) return null;
  return { s4: s4p, gy: shadowY(s4p.s3.s2.s1, params.PW, params.valid) };
}

function fixPiece5(bagNew, s, params) {
  const s4p = oracle4.fixPiece4(bagNew, s.s4, params);
  if (!s4p) return null;
  return { s4: s4p, gy: shadowY(s4p.s3.s2.s1, params.PW, params.valid) };
}

function fallStep5(bagNew, s, params) {
  return movePiece5(-1, 0, s, params) ?? fixPiece5(bagNew, s, params);
}

function holdPiece5(bagNew, s, params) {
  const s4p = oracle4.holdPiece4(bagNew, s.s4, params);
  if (!s4p) return null;
  return { s4: s4p, gy: shadowY(s4p.s3.s2.s1, params.PW, params.valid) };
}

// spec: DropPiece bagNew H — relocate to gy, then fix. A single upfront gameover
// check suffices, given LowestShadowY guarantees the relocated state's FixPiece
// guard is satisfiable whenever ¬gameover held before the drop.
function dropPiece5(bagNew, s, params) {
  const snap4 = oracle4.snapshotOf4(s.s4);
  if (snap4.gameover) return null;
  const s1 = s.s4.s3.s2.s1;
  const relocated = newPieceYXState(s.gy, s1.px, s1);
  const s4Relocated = { ...s.s4, s3: { ...s.s4.s3, s2: { ...s.s4.s3.s2, s1: relocated } } };
  return fixPiece5(bagNew, { s4: s4Relocated, gy: s.gy }, params);
}

function snapshotOf5(s) {
  return {
    ...oracle4.snapshotOf4(s.s4),
    gy: s.gy,
  };
}

function states5Equal(a, b) {
  return JSON.stringify(snapshotOf5(a)) === JSON.stringify(snapshotOf5(b));
}

// makeParams5: extends T4's oracle params with PW and a valid function, both
// needed by shadowY here (T4's own oracle params don't carry either).
function makeParams5(TI) {
  return { ...oracle4.makeParams4(TI), PW: TI.PW, valid: makeValid(TI) };
}

// Independent hand-roll of Valid = OccupiedInside ∧ ¬Intersect, operating on the
// grid-object {L,H,W} representation t1oracle uses internally for mg, and on
// plain arrays for rotGrid's output — matching t1/tests/oracle.js's own style.
function makeValid(TI) {
  return function valid(mg, p, py, px, pr) {
    const rg = TI.RotGrid(p, pr);
    const rgH = rg.length, rgW = rg[0].length;
    for (let y = 0; y < rgH; y++) {
      for (let x = 0; x < rgW; x++) {
        if (!rg[y][x]) continue;
        const oy = y + py, ox = x + px;
        if (!(oy >= 0 && oy < mg.H && ox >= 0 && ox < mg.W)) return false;
        if (mg.L(oy, ox)) return false;
      }
    }
    return true;
  };
}

export const oracle5 = {
  makeParams5,
  shadowY,
  newPieceYXState,
  initState5,
  movePiece5,
  rotatePiece5,
  fixPiece5,
  fallStep5,
  holdPiece5,
  dropPiece5,
  snapshotOf5,
  states5Equal,
};
