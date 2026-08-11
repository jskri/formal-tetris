import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import { T } from '../model.js';
import * as TI from './testInstance.js';

function makeEngine() {
  return T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
            TI.PW, TI.FY, TI.FX, TI.NextLen);
}

// Deterministic bagsFn table for hand-verified golden vectors on the 2-piece
// fixture (Piece = ['A','B'], MaxBagLen = 2, NextLen = 3). See
// implementation.md §9 for the worked derivation this reproduces.
function tableBagsFn(table) {
  return (i) => table[i];
}

describe('isPieceSet / assertPieceSet', () => {
  test('rejects wrong length', () => {
    const eng = makeEngine();
    assert.strictEqual(eng.isPieceSet(['A']), false);
    assert.throws(() => eng.assertPieceSet(['A']));
  });

  test('rejects a duplicate', () => {
    const eng = makeEngine();
    assert.strictEqual(eng.isPieceSet(['A', 'A']), false);
    assert.throws(() => eng.assertPieceSet(['A', 'A']));
  });

  test('accepts a valid permutation, in either order', () => {
    const eng = makeEngine();
    assert.strictEqual(eng.isPieceSet(['A', 'B']), true);
    assert.strictEqual(eng.isPieceSet(['B', 'A']), true);
    assert.doesNotThrow(() => eng.assertPieceSet(['A', 'B']));
  });
});

describe('Machine constructor — Init, hand-verified golden vector', () => {
  test('initPieceAndDraw matches the hand-computed trace', () => {
    const eng = makeEngine();
    const bagsFn = tableBagsFn([['A', 'B'], ['B', 'A'], ['A', 'B'], ['B', 'A']]);
    const m = new eng.Machine(bagsFn);
    assert.strictEqual(m.s3.s2.s1.p, 'B');
    assert.deepStrictEqual(m.bag_, ['A', 'B']);
    assert.deepStrictEqual(m.next_, ['A', 'A', 'B']);
  });

  test('continuing the trace one more draw crosses into the reset branch two steps later', () => {
    const eng = makeEngine();
    const bagsFn = tableBagsFn([['A', 'B'], ['B', 'A'], ['A', 'B'], ['B', 'A']]);
    const m = new eng.Machine(bagsFn);
    // draw 1: non-reset (bag_ was length 2, becomes length 1)
    const p1 = m.drawNextPiece(['A', 'B']);
    assert.strictEqual(p1, 'A');
    assert.deepStrictEqual(m.bag_, ['A']);
    assert.deepStrictEqual(m.next_, ['A', 'B', 'B']);
    // draw 2: resetting (bag_ was length 1, refills from the supplied bagNew)
    const p2 = m.drawNextPiece(['A', 'B']);
    assert.strictEqual(p2, 'A');
    assert.deepStrictEqual(m.bag_, ['A', 'B']);
    assert.deepStrictEqual(m.next_, ['B', 'B', 'A']);
  });
});

describe('Machine.fixPiece — peek-then-commit ordering', () => {
  test('guard-fail leaves bag_/next_ byte-identical to before the call', () => {
    const eng = makeEngine();
    const m = new eng.Machine(() => ['A', 'B']);
    const bagBefore = m.bag_.slice(), nextBefore = m.next_.slice();
    const fired = m.fixPiece(['A', 'B']); // spawn has clear space below -> guard fails
    assert.strictEqual(fired, false);
    assert.deepStrictEqual(m.bag_, bagBefore);
    assert.deepStrictEqual(m.next_, nextBefore);
  });

  test('a successful fix consumes exactly next_[0] (read before the draw)', () => {
    const eng = makeEngine();
    const m = new eng.Machine(() => ['A', 'B']);
    while (m.movePiece(-1, 0)) { /* fall to the floor */ }
    const expectedP = m.next_[0];
    const nextLenBefore = m.next_.length;
    const fired = m.fixPiece(['B', 'A']);
    assert.strictEqual(fired, true);
    assert.strictEqual(m.s3.s2.s1.p, expectedP);
    assert.strictEqual(m.next_.length, nextLenBefore);
  });
});

describe('Machine.holdPiece — skip-vs-discard', () => {
  test('firing a hold when hold !== null leaves bag_/next_ byte-identical', () => {
    const eng = makeEngine();
    const m = new eng.Machine(() => ['A', 'B']);
    m.holdPiece(['A', 'B']); // first hold: hold was null, draws
    while (m.movePiece(-1, 0)) { /* fall */ }
    m.fixPiece(['B', 'A']); // resets swapped
    const bagBefore = m.bag_.slice(), nextBefore = m.next_.slice();
    m.holdPiece(['B', 'A']); // second hold: hold !== null, must skip the draw
    assert.deepStrictEqual(m.bag_, bagBefore);
    assert.deepStrictEqual(m.next_, nextBefore);
  });

  test('gameover blocks hold', () => {
    const eng = makeEngine();
    const m = new eng.Machine(() => ['A', 'B']);
    m.s3.s2.s1.gameover = true; // force for this unit test
    assert.strictEqual(m.holdPiece(['A', 'B']), false);
  });
});

describe('checkInvariants — bag_ prefix validity', () => {
  test('bag_ stays a valid prefix (distinct, in-bounds, subset of Piece) across a full cycle', () => {
    const eng = makeEngine();
    const m = new eng.Machine(() => ['A', 'B']);
    for (let i = 0; i < 6; i++) {
      assert.ok(m.bag_.length > 0 && m.bag_.length <= TI.Piece.length);
      assert.strictEqual(new Set(m.bag_).size, m.bag_.length);
      assert.ok(m.bag_.every(p => TI.Piece.includes(p)));
      m.drawNextPiece(['A', 'B']);
    }
  });
});
