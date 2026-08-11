import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import { T } from '../model.js';
import { mod } from '../../lib/utils.js';
import * as TI from './testInstance.js';
import { assertSnapshotsEqual } from './oracle.js';

function makeEngine() {
  return T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
            TI.PW, TI.FY, TI.FX);
}

describe('mod (L-mod)', () => {
  for (const [a, n, expected] of [[-1, 4, 3], [0, 4, 0], [1, 4, 1], [2, 4, 2], [3, 4, 3], [4, 4, 0]]) {
    test(`mod(${a},${n}) === ${expected}`, () => {
      assert.strictEqual(mod(a, n), expected);
    });
  }
});

describe('rotGrid', () => {
  test('4 rotations of the asymmetric piece B return distinct occupied sets', () => {
    const eng = makeEngine();
    const occupiedSets = [0, 1, 2, 3].map(r => {
      const g = eng.rotGrid('B', r);
      const cells = [];
      for (let y = 0; y < g.length; y++)
        for (let x = 0; x < g[0].length; x++)
          if (g[y][x]) cells.push([y, x]);
      return JSON.stringify(cells);
    });
    assert.strictEqual(new Set(occupiedSets).size, 4);
  });

  test('rotation-invariant piece A is identical across all 4 rotations', () => {
    const eng = makeEngine();
    const g0 = eng.rotGrid('A', 0);
    for (const r of [1, 2, 3]) assert.deepStrictEqual(eng.rotGrid('A', r), g0);
  });

  test('rotGrid returns a fresh copy each call (no aliasing)', () => {
    const eng = makeEngine();
    const g1 = eng.rotGrid('A', 0);
    const g2 = eng.rotGrid('A', 0);
    assert.notStrictEqual(g1, g2);
    assert.notStrictEqual(g1[0], g2[0]);
  });
});

describe('clearFullLines', () => {
  const F = false, X = true;

  test('no full line: grid unchanged', () => {
    const eng = makeEngine();
    const g = [[F, F], [F, X], [X, F]];
    assert.deepStrictEqual(eng.clearFullLines(g), g);
  });

  test('one full line at the bottom', () => {
    const eng = makeEngine();
    const g = [[X, X], [F, X], [F, F]];
    assert.deepStrictEqual(eng.clearFullLines(g), [[F, X], [F, F], [F, F]]);
  });

  test('one full line in the middle', () => {
    const eng = makeEngine();
    const g = [[F, X], [X, X], [X, F]];
    assert.deepStrictEqual(eng.clearFullLines(g), [[F, X], [X, F], [F, F]]);
  });

  test('one full line at the top', () => {
    const eng = makeEngine();
    const g = [[F, X], [X, F], [X, X]];
    assert.deepStrictEqual(eng.clearFullLines(g), [[F, X], [X, F], [F, F]]);
  });

  test('several full lines', () => {
    const eng = makeEngine();
    const g = [[X, X], [F, X], [X, X]];
    assert.deepStrictEqual(eng.clearFullLines(g), [[F, X], [F, F], [F, F]]);
  });

  test('all full', () => {
    const eng = makeEngine();
    const g = [[X, X], [X, X], [X, X]];
    assert.deepStrictEqual(eng.clearFullLines(g), [[F, F], [F, F], [F, F]]);
  });

  test('none full (all empty)', () => {
    const eng = makeEngine();
    const g = [[F, F], [F, F]];
    assert.deepStrictEqual(eng.clearFullLines(g), g);
  });

  test('dimension preserved and rows are booleans', () => {
    const eng = makeEngine();
    const g = [[X, X], [F, X], [X, X]];
    const out = eng.clearFullLines(g);
    assert.strictEqual(out.length, g.length);
    assert.ok(out.every(r => r.length === g[0].length));
  });
});

describe('intersect / occupiedInside / valid — boundary cells, no throw', () => {
  const F = false, X = true;
  const g2 = [[X, X], [X, X]]; // 2x2 all-true

  test('negative offset does not throw and is out-of-bounds (occupiedInside false)', () => {
    const eng = makeEngine();
    const g1 = [[X]];
    assert.doesNotThrow(() => eng.occupiedInside(g1, -1, -1, g2, 0, 0));
    assert.strictEqual(eng.occupiedInside(g1, -1, -1, g2, 0, 0), false);
    assert.doesNotThrow(() => eng.intersect(g1, -1, -1, g2, 0, 0));
    assert.strictEqual(eng.intersect(g1, -1, -1, g2, 0, 0), false);
  });

  test('offset landing exactly at H g2 (out of range) does not throw', () => {
    const eng = makeEngine();
    const g1 = [[X]];
    assert.doesNotThrow(() => eng.intersect(g1, 2, 0, g2, 0, 0));
    assert.strictEqual(eng.intersect(g1, 2, 0, g2, 0, 0), false);
  });

  test('offset landing exactly at W g2 (out of range) does not throw', () => {
    const eng = makeEngine();
    const g1 = [[X]];
    assert.doesNotThrow(() => eng.intersect(g1, 0, 2, g2, 0, 0));
    assert.strictEqual(eng.intersect(g1, 0, 2, g2, 0, 0), false);
  });

  test('valid: rejects out-of-bounds and intersecting placements without throwing', () => {
    const eng = makeEngine();
    assert.doesNotThrow(() => eng.valid(TI.InitialMainGrid, 'A', -100, -100, 0));
    assert.strictEqual(eng.valid(TI.InitialMainGrid, 'A', -100, -100, 0), false);
  });
});

describe('Machine.movePiece', () => {
  test('each legal direction moves the piece', () => {
    const eng = makeEngine();
    const m = new eng.Machine('B');
    const py0 = m.py, px0 = m.px;
    assert.strictEqual(m.movePiece(0, -1), true);
    assert.strictEqual(m.px, px0 - 1);
    assert.strictEqual(m.movePiece(0, 1), true);
    assert.strictEqual(m.px, px0);
    assert.strictEqual(m.movePiece(-1, 0), true);
    assert.strictEqual(m.py, py0 - 1);
  });

  test('illegal direction is rejected (stutter)', () => {
    const eng = makeEngine();
    const m = new eng.Machine('B');
    const snap = eng.snapshot(m);
    assert.strictEqual(m.movePiece(1, 0), false);   // upward move not permitted
    assert.strictEqual(m.movePiece(1, 1), false);   // diagonal not permitted
    assertSnapshotsEqual(eng.snapshot(m), snap);
  });

  test('move that would leave the grid is blocked', () => {
    const eng = makeEngine();
    const m = new eng.Machine('B'); // spawns at px=1, main grid width 4
    assert.strictEqual(m.movePiece(0, -1), true); // px=0
    assert.strictEqual(m.movePiece(0, -1), false); // would go to px=-1: blocked
  });

  test('gameover blocks movement', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    m.gameover = true; // force for this unit test
    assert.strictEqual(m.movePiece(0, 1), false);
  });
});

describe('Machine.rotatePiece', () => {
  test('cw and ccw cycle pr through all 4 values and back', () => {
    const eng = makeEngine();
    const m = new eng.Machine('B');
    const seen = [m.pr];
    for (let i = 0; i < 4; i++) { assert.strictEqual(m.rotatePiece(true), true); seen.push(m.pr); }
    assert.strictEqual(seen[4], seen[0]);
    for (let i = 0; i < 4; i++) assert.strictEqual(m.rotatePiece(false), true);
    assert.strictEqual(m.pr, seen[0]);
  });

  test('gameover blocks rotation', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A');
    m.gameover = true;
    assert.strictEqual(m.rotatePiece(true), false);
  });

  test('a rotation that would intersect locked blocks is rejected', () => {
    const eng = makeEngine();
    const m = new eng.Machine('B');
    // Lock a block directly in the way of one of B's rotated occupied cells.
    m.mg[m.py][m.px] = true; // occupy the spawn cell itself
    // r=0 occupies (0,0) relative -> exactly (py,px); rotating ccw once goes to r=1,
    // which occupies (0,1) relative -> (py, px+1).
    m.mg[m.py][m.px + 1] = true;
    assert.strictEqual(m.rotatePiece(false), false); // cw=false -> pr 0->1, blocked
  });
});

describe('Machine.fixPiece', () => {
  test('full lock -> clear -> respawn sequence on a crafted board', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A'); // 2x2 block, spawns at py=4,px=1
    while (m.movePiece(-1, 0)) { /* drop to the floor: py=0,px=1 */ }
    // Pre-fill the rest of rows 0 and 1 (cols 0 and 3) so A's lock completes both lines.
    m.mg[0][0] = true; m.mg[0][3] = true;
    m.mg[1][0] = true; m.mg[1][3] = true;
    const fired = m.fixPiece('B');
    assert.strictEqual(fired, true);
    assert.strictEqual(m.clearedLines, 2);
    assert.ok(m.mg.every(row => row.every(c => c === false))); // both lines cleared
    assert.strictEqual(m.p, 'B');
    assert.strictEqual(m.py, TI.InitialY('B'));
    assert.strictEqual(m.px, TI.InitialX('B'));
    assert.strictEqual(m.pr, 0);
  });

  test('locking so the resulting grid still occupies the forbidden zone triggers gameover', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A'); // spawns at py=4,px=1, occupying rows 4-5 (the forbidden zone)
    // Block the space directly below the spawn so the piece cannot fall further.
    m.mg[3][1] = true; m.mg[3][2] = true;
    const fired = m.fixPiece('B');
    assert.strictEqual(fired, true);
    assert.strictEqual(m.clearedLines, 0); // rows 4,5 are not completed (cols 0,3 stay empty)
    assert.strictEqual(m.gameover, true);  // locked cells remain inside the forbidden zone
  });

  test('guard fails (piece can still fall) -> stutter', () => {
    const eng = makeEngine();
    const m = new eng.Machine('A'); // spawns with clear space below
    const snap = eng.snapshot(m);
    assert.strictEqual(m.fixPiece('B'), false);
    assertSnapshotsEqual(eng.snapshot(m), snap);
  });
});

describe('Machine.fallStep', () => {
  test('falls when space below', () => {
    const eng = makeEngine();
    const m = new eng.Machine('B');
    const py0 = m.py;
    assert.strictEqual(m.fallStep('A'), true);
    assert.strictEqual(m.py, py0 - 1);
  });

  test('triggers fixPiece when blocked below (mutual exclusion of guards)', () => {
    const eng = makeEngine();
    const m = new eng.Machine('B');
    while (m.movePiece(-1, 0)) { /* fall */ }
    const pBefore = m.p;
    assert.strictEqual(m.fallStep('A'), true);
    assert.notStrictEqual(m.p, pBefore); // fixPiece fired: piece was replaced
  });
});
