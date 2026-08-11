import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import { T } from '../model.js';
import * as TI from './testInstance.js';

function makeEngine() {
  return T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
            TI.PW, TI.FY, TI.FX);
}

describe('lineClearPoints', () => {
  for (const level of [1, 2, 5]) {
    for (const [clearedLines, expected] of [[0, 0], [1, 100], [2, 300], [3, 500], [4, 800], [5, 800]]) {
      test(`lineClearPoints(${clearedLines}, level=${level})`, () => {
        const eng = makeEngine();
        assert.strictEqual(eng.lineClearPoints(clearedLines, level), expected * level);
      });
    }
  }
});

describe('comboPoints', () => {
  for (const level of [1, 2]) {
    for (const combo of [0, 1, 2]) {
      test(`comboPoints(level=${level}, combo=${combo})`, () => {
        const eng = makeEngine();
        const expected = combo > 0 ? 50 * combo * level : 0;
        assert.strictEqual(eng.comboPoints(level, combo), expected);
      });
    }
  }
});

describe('perfectClearPoints', () => {
  const table = { 0: 0, 1: 800, 2: 1200, 3: 1800, 4: 2000, 5: 2000 };
  for (const level of [1, 2]) {
    for (const clearedLines of [0, 1, 2, 3, 4, 5]) {
      test(`perfectClearPoints(false, ${clearedLines}, ${level}) === 0`, () => {
        const eng = makeEngine();
        assert.strictEqual(eng.perfectClearPoints(false, clearedLines, level), 0);
      });
      test(`perfectClearPoints(true, ${clearedLines}, ${level})`, () => {
        const eng = makeEngine();
        assert.strictEqual(eng.perfectClearPoints(true, clearedLines, level), table[clearedLines] * level);
      });
    }
  }
});

describe('points', () => {
  test('sums all three components', () => {
    const eng = makeEngine();
    // clearedLines=2, level=1, combo=1, perfectClear=true
    // lineClear=300, combo=50*1*1=50, perfectClear=1200 => 1550
    assert.strictEqual(eng.points(2, 1, 1, true), 1550);
  });

  test('no clear, no combo, no perfect clear -> 0', () => {
    const eng = makeEngine();
    assert.strictEqual(eng.points(0, 3, 0, false), 0);
  });
});

describe('emptyGridb', () => {
  test('all-false grid is empty', () => {
    const eng = makeEngine();
    assert.strictEqual(eng.emptyGridb([[false, false], [false, false]]), true);
  });

  test('any true cell makes it non-empty', () => {
    const eng = makeEngine();
    assert.strictEqual(eng.emptyGridb([[false, true], [false, false]]), false);
  });
});

describe('fullLineCount (re-exported from T1)', () => {
  test('counts full rows', () => {
    const eng = makeEngine();
    const g = [[true, true], [false, true], [true, true]];
    assert.strictEqual(eng.fullLineCount(g), 2);
  });
});

// Helper: drop the current piece to the floor and fill the landing rows' outer
// columns (0 and 3) so a full-block piece ('A', occupying both landing rows'
// middle columns 1,2) completes both lines.
function dropAndFillFullClear(m, pNew) {
  while (m.s1.movePiece(-1, 0)) { /* fall */ }
  const y = m.s1.py;
  m.s1.mg[y][0] = true; m.s1.mg[y][3] = true;
  m.s1.mg[y + 1][0] = true; m.s1.mg[y + 1][3] = true;
  return m.fixPiece(pNew);
}

describe('Machine.fixPiece — score/level bookkeeping', () => {
  test('a clearing fix raises score and totalClearedLines; single clear yields no perfect-clear here', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    const fired = dropAndFillFullClear(m, 'A');
    assert.strictEqual(fired, true);
    assert.strictEqual(m.s1.clearedLines, 2);
    // grid is 6x4 with only these two rows ever touched: clearing both empties the whole grid.
    assert.strictEqual(m.perfectClear, true);
    assert.strictEqual(m.totalClearedLines, 2);
    assert.strictEqual(m.level, 1);
    // lineClear(2,1)=300, combo(1,0)=0 [combo'=1, visible=0], perfectClear(true,2,1)=1200
    assert.strictEqual(m.score, 300 + 0 + 1200);
    assert.strictEqual(m.combo, 1); // stored = visible(0) + 1
  });

  test('combo increments across consecutive clearing fixes', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    dropAndFillFullClear(m, 'A');
    const scoreAfterFirst = m.score;
    dropAndFillFullClear(m, 'A');
    assert.strictEqual(m.combo, 2); // visible combo = 1
    // lineClear(2,1)=300, combo(1, visible=1)=50, perfectClear(true,2,1)=1200 => 1550
    assert.strictEqual(m.score, scoreAfterFirst + 1550);
    assert.strictEqual(m.totalClearedLines, 4);
  });

  test('a non-clearing fix resets combo to 0 and leaves score unchanged', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    while (m.movePiece(-1, 0)) { /* fall to the floor without filling any line */ }
    const before = { score: m.score, total: m.totalClearedLines };
    const fired = m.fixPiece('A');
    assert.strictEqual(fired, true);
    assert.strictEqual(m.s1.clearedLines, 0);
    assert.strictEqual(m.combo, 0);
    assert.strictEqual(m.score, before.score);
    assert.strictEqual(m.totalClearedLines, before.total);
  });

  test('level rises by one every ten cleared lines', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    for (let i = 0; i < 5; i++) dropAndFillFullClear(m, 'A'); // 5 * 2 = 10 lines
    assert.strictEqual(m.totalClearedLines, 10);
    assert.strictEqual(m.level, 2);
  });

  test('guard fails (piece can still fall) -> stutter, no T2 field changes', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A'); // spawns with clear space below
    const before = { score: m.score, level: m.level, combo: m.combo,
                      perfectClear: m.perfectClear, totalClearedLines: m.totalClearedLines };
    assert.strictEqual(m.fixPiece('B'), false);
    assert.deepStrictEqual(
      { score: m.score, level: m.level, combo: m.combo,
        perfectClear: m.perfectClear, totalClearedLines: m.totalClearedLines },
      before);
  });
});

describe('Machine.movePiece / rotatePiece — scalars unchanged', () => {
  test('movePiece leaves score/level/combo/perfectClear/totalClearedLines untouched', () => {
    const eng = makeEngine();
    const m = new eng.Machine('B');
    const before = { score: m.score, level: m.level, combo: m.combo,
                      perfectClear: m.perfectClear, totalClearedLines: m.totalClearedLines };
    m.movePiece(0, -1);
    assert.deepStrictEqual(
      { score: m.score, level: m.level, combo: m.combo,
        perfectClear: m.perfectClear, totalClearedLines: m.totalClearedLines },
      before);
  });

  test('rotatePiece leaves score/level/combo/perfectClear/totalClearedLines untouched', () => {
    const eng = makeEngine();
    const m = new eng.Machine('B');
    const before = { score: m.score, level: m.level, combo: m.combo,
                      perfectClear: m.perfectClear, totalClearedLines: m.totalClearedLines };
    m.rotatePiece(true);
    assert.deepStrictEqual(
      { score: m.score, level: m.level, combo: m.combo,
        perfectClear: m.perfectClear, totalClearedLines: m.totalClearedLines },
      before);
  });
});

describe('Machine.fallStep', () => {
  test('falls when space below (no T2 field change)', () => {
    const eng = makeEngine();
    const m = new eng.Machine('B');
    const before = m.score;
    assert.strictEqual(m.fallStep('A'), true);
    assert.strictEqual(m.score, before);
  });

  test('triggers fixPiece when blocked below', () => {
    const eng = makeEngine();
    const m = new eng.Machine('B');
    while (m.movePiece(-1, 0)) { /* fall */ }
    const pBefore = m.s1.p;
    assert.strictEqual(m.fallStep('A'), true);
    assert.notStrictEqual(m.s1.p, pBefore); // fixPiece fired
  });
});

describe('Machine constructor — Init', () => {
  test('req-score-init / req-level-init defaults', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    assert.strictEqual(m.score, 0);
    assert.strictEqual(m.level, 1);
    assert.strictEqual(m.combo, 0);
    assert.strictEqual(m.perfectClear, false);
    assert.strictEqual(m.totalClearedLines, 0);
  });
});
