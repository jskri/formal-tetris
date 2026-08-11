import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { assertSnapshotsEqual, gridsEqual } from '../../t1/tests/oracle.js';

function makeEngine() {
  return T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
            TI.PW, TI.FY, TI.FX);
}

describe('Machine constructor — Init', () => {
  test('hold/swapped defaults', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    assert.strictEqual(m.hold, null);
    assert.strictEqual(m.swapped, false);
  });
});

describe('Machine.holdPiece — req-hold-empty', () => {
  test('first hold uses pNew; hold slot receives the old current piece; swapped becomes true', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    const oldPiece = m.s2.s1.p;
    const fired = m.holdPiece('B');
    assert.strictEqual(fired, true);
    assert.strictEqual(m.s2.s1.p, 'B');
    assert.strictEqual(m.hold, oldPiece);
    assert.strictEqual(m.swapped, true);
    assert.strictEqual(m.s2.s1.py, TI.InitialY('B'));
    assert.strictEqual(m.s2.s1.px, TI.InitialX('B'));
    assert.strictEqual(m.s2.s1.pr, 0);
  });
});

describe('Machine.holdPiece — req-hold-swap', () => {
  test('holding again after a fix swaps with the held piece; pNew is ignored', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    m.holdPiece('B'); // hold = old current ('A'), current = 'B'
    while (m.movePiece(-1, 0)) { /* fall */ }
    m.fixPiece('S');  // resets swapped
    const currentBeforeSwap = m.s2.s1.p;
    const heldBeforeSwap = m.hold;
    const fired = m.holdPiece('Z'); // irrelevant: hold slot is occupied
    assert.strictEqual(fired, true);
    assert.strictEqual(m.s2.s1.p, heldBeforeSwap);
    assert.strictEqual(m.hold, currentBeforeSwap);
  });
});

describe('Machine.holdPiece — req-hold-limit', () => {
  test('a second hold before an intervening fix fails (stutter)', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    assert.strictEqual(m.holdPiece('B'), true);
    const snapBefore = eng.snapshot(m);
    assert.strictEqual(m.holdPiece('S'), false);
    assertSnapshotsEqual(eng.snapshot(m), snapBefore);
  });

  test('a fix resets swapped, re-enabling hold', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    m.holdPiece('B');
    assert.strictEqual(m.swapped, true);
    while (m.movePiece(-1, 0)) { /* fall */ }
    m.fixPiece('S');
    assert.strictEqual(m.swapped, false);
    assert.strictEqual(m.holdPiece('Z'), true);
  });
});

describe('Machine.holdPiece — gameover blocks hold', () => {
  test('cannot hold once gameover', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    m.s2.s1.gameover = true; // force for this unit test
    assert.strictEqual(m.holdPiece('B'), false);
  });
});

describe('Machine.holdPiece — narrow blast radius', () => {
  test('only p/py/px/pr (of s1) and hold/swapped change; everything else is untouched', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    m.s2.s1.mg[0][0] = true; // marker cell, so mg comparison is non-trivial
    const before = eng.snapshot(m);
    m.holdPiece('B');
    const after = eng.snapshot(m);

    for (const f of ['mg', 'gameover', 'clearedLines', 'score', 'level', 'combo',
                      'perfectClear', 'totalClearedLines']) {
      if (f === 'mg') assert.ok(gridsEqual(after.mg, before.mg), 'mg should be untouched by holdPiece');
      else assert.deepStrictEqual(after[f], before[f], `field ${f} should be untouched by holdPiece`);
    }
    assert.notStrictEqual(after.p, before.p);
    assert.notStrictEqual(after.hold, before.hold);
    assert.notStrictEqual(after.swapped, before.swapped);
  });
});

describe('Machine.movePiece / rotatePiece / fixPiece — hold/swapped pass-through', () => {
  test('movePiece leaves hold/swapped untouched', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    m.holdPiece('B');
    const before = { hold: m.hold, swapped: m.swapped };
    m.movePiece(0, -1);
    assert.deepStrictEqual({ hold: m.hold, swapped: m.swapped }, before);
  });

  test('rotatePiece leaves hold/swapped untouched', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    m.holdPiece('B');
    const before = { hold: m.hold, swapped: m.swapped };
    m.rotatePiece(true);
    assert.deepStrictEqual({ hold: m.hold, swapped: m.swapped }, before);
  });

  test('fixPiece leaves hold untouched but resets swapped to false', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    m.holdPiece('B');
    const heldBefore = m.hold;
    while (m.movePiece(-1, 0)) { /* fall */ }
    m.fixPiece('S');
    assert.strictEqual(m.hold, heldBefore);
    assert.strictEqual(m.swapped, false);
  });
});

describe('Machine.fallStep', () => {
  test('falls when space below (hold/swapped untouched)', () => {
    const eng = makeEngine();
    const m = new eng.Machine('B');
    m.holdPiece('A');
    const before = { hold: m.hold, swapped: m.swapped };
    assert.strictEqual(m.fallStep('A'), true);
    assert.deepStrictEqual({ hold: m.hold, swapped: m.swapped }, before);
  });

  test('triggers fixPiece when blocked below, which resets swapped', () => {
    const eng = makeEngine();
    const m = new eng.Machine('B');
    m.holdPiece('A');
    while (m.movePiece(-1, 0)) { /* fall */ }
    assert.strictEqual(m.fallStep('A'), true);
    assert.strictEqual(m.swapped, false);
  });
});

describe('Read-through getters', () => {
  test('gameover/level/totalClearedLines/combo/perfectClear track the inner s2', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    assert.strictEqual(m.gameover, m.s2.gameover);
    assert.strictEqual(m.level, m.s2.level);
    assert.strictEqual(m.totalClearedLines, m.s2.totalClearedLines);
    assert.strictEqual(m.combo, m.s2.combo);
    assert.strictEqual(m.perfectClear, m.s2.perfectClear);

    m.s2.s1.gameover = true;
    assert.strictEqual(m.gameover, true);
  });
});
