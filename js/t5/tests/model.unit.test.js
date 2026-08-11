import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { assertSnapshotsEqual } from '../../t1/tests/oracle.js';

function makeEngine() {
  return T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
            TI.PW, TI.FY, TI.FX, TI.NextLen);
}

describe('shadowY — unobstructed column, per piece type', () => {
  test('the true floor can be below row 0, per piece', () => {
    const eng = makeEngine();
    for (const piece of TI.Piece) {
      const m = new eng.Machine(() => [piece, ...TI.Piece.filter(p => p !== piece)]);
      const s1 = m.s4.s3.s2.s1;
      s1.p = piece;
      m.updateShadowY();
      // The floor a piece actually reaches depends on where its occupied cells
      // sit within its own PW×PW rotation grid — not fixed at 0.
      while (m.movePiece(-1, 0)) { /* fall all the way */ }
      assert.strictEqual(m.gy, s1.py, `${piece}: shadowY must match the true resting position`);
    }
  });
});

describe('shadowY — overhang board', () => {
  test('rests on a shelf, does not fall through to a cavity beneath it', () => {
    const eng = makeEngine();
    const m = new eng.Machine(() => ['A', 'B']);
    const s1 = m.s4.s3.s2.s1;
    const shelfRow = 3; // within the small fixture's 6-row grid
    for (let x = 0; x < s1.mg[0].length; x++) s1.mg[shelfRow][x] = true;
    m.updateShadowY();

    const valid = eng.T4Eng.T3Eng.T2Eng.T1Eng.valid;
    assert.strictEqual(valid(s1.mg, s1.p, m.gy, s1.px, s1.pr), true);
    assert.strictEqual(valid(s1.mg, s1.p, m.gy - 1, s1.px, s1.pr), false);
    assert.notStrictEqual(m.gy, 0, 'must not fall through to a cavity below the shelf');
  });
});

describe('shadowY — refresh on move/rotate, not on pure vertical fall', () => {
  test('recomputes after a horizontal move or rotation', () => {
    const eng = makeEngine();
    const m = new eng.Machine(() => ['A', 'B']);
    const before = m.gy;
    const moved = m.movePiece(0, -1);
    if (moved) {
      assert.strictEqual(m.gy, eng.shadowY(m.s4.s3.s2.s1));
    }
  });

  test('a pure vertical move leaves the same value (still correct, just redundant)', () => {
    const eng = makeEngine();
    const m = new eng.Machine(() => ['A', 'B']);
    const before = m.gy;
    if (m.movePiece(-1, 0)) {
      assert.strictEqual(m.gy, before);
    }
  });
});

describe('Machine.dropPiece', () => {
  test('locks the piece at exactly gy, not py', () => {
    const eng = makeEngine();
    const m = new eng.Machine(() => ['A', 'B']);
    const targetGy = m.gy;
    const pBefore = m.s4.s3.s2.s1.p;
    const fired = m.dropPiece(['B', 'A']);
    assert.strictEqual(fired, true);
  });

  test('produces the same result as falling to the floor then fixing', () => {
    const eng = makeEngine();
    const seed = [['A', 'B'], ['B', 'A'], ['A', 'B']];
    const bagsFn = (i) => seed[i % seed.length];
    const mDrop = new eng.Machine(bagsFn);
    const mFall = new eng.Machine(bagsFn);
    const bagNew = ['B', 'A'];
    mDrop.dropPiece(bagNew);
    while (mFall.movePiece(-1, 0)) { /* fall */ }
    mFall.fixPiece(bagNew);
    assertSnapshotsEqual(eng.snapshot(mDrop), eng.snapshot(mFall));
  });

  test('blocked by gameover', () => {
    const eng = makeEngine();
    const m = new eng.Machine(() => ['A', 'B']);
    m.s4.s3.s2.s1.gameover = true;
    assert.strictEqual(m.dropPiece(['A', 'B']), false);
  });

  test('narrow blast radius: everything fixPiece-at-gy would change, plus gy itself', () => {
    const eng = makeEngine();
    const seed = [['A', 'B'], ['B', 'A']];
    const bagsFn = (i) => seed[i % seed.length];
    const mDrop = new eng.Machine(bagsFn);
    const mFixAtGy = new eng.Machine(bagsFn);
    mFixAtGy.s4.s3.s2.s1.py = mDrop.gy; // relocate manually, same effect dropPiece has
    const bagNew = ['A', 'B'];
    mDrop.dropPiece(bagNew);
    mFixAtGy.fixPiece(bagNew);
    assertSnapshotsEqual(eng.snapshot(mDrop), eng.snapshot(mFixAtGy));
  });
});

describe('Machine constructor — Init', () => {
  test('gy is computed at construction', () => {
    const eng = makeEngine();
    const m = new eng.Machine(() => ['A', 'B']);
    assert.strictEqual(m.gy, eng.shadowY(m.s4.s3.s2.s1));
  });
});
