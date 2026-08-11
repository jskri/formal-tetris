import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import fc from 'fast-check';
import { T } from '../model.js';
import * as TI from './testInstance.js';

const eng = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
              TI.PW, TI.FY, TI.FX);

// Event generator: random sequence of {kind, args} over the four non-trivial events.
const pieceArb = fc.constantFrom(...TI.Piece);
const eventArb = fc.oneof(
  fc.record({ kind: fc.constant('move'), dy: fc.constantFrom(-1, 0), dx: fc.constantFrom(-1, 0, 1) }),
  fc.record({ kind: fc.constant('rotate'), cw: fc.boolean() }),
  fc.record({ kind: fc.constant('fix'), pNew: pieceArb }),
  fc.record({ kind: fc.constant('fall'), pNew: pieceArb }),
);

function applyEvent(m, e) {
  switch (e.kind) {
    case 'move': return m.movePiece(e.dy, e.dx);
    case 'rotate': return m.rotatePiece(e.cw);
    case 'fix': return m.fixPiece(e.pNew);
    case 'fall': return m.fallStep(e.pNew);
  }
}

describe('T1 model.js properties', () => {
  test('invariants hold after every step of every random trace', () => {
    fc.assert(fc.property(pieceArb, fc.array(eventArb, { maxLength: 200 }), (p0, events) => {
      const m = new eng.Machine(p0);
      let sawGameover = false;
      for (const e of events) {
        assert.doesNotThrow(() => applyEvent(m, e));               // D9 guard-before-index
        assert.strictEqual(eng.typeOK(m), true);                    // typeOK(snapshot)
        assert.strictEqual(m.mg.length, TI.InitialMainGrid.length); // mg stays HM x WM
        assert.strictEqual(m.mg[0].length, TI.InitialMainGrid[0].length);
        assert.doesNotThrow(() => eng.checkInvariants(m, 'property'));

        // integer fields within MAX_SAFE_INTEGER (D10)
        for (const f of [m.py, m.px, m.pr, m.clearedLines])
          assert.ok(Math.abs(f) <= Number.MAX_SAFE_INTEGER);

        // gameover monotonicity
        if (sawGameover) assert.strictEqual(m.gameover, true);
        if (m.gameover) sawGameover = true;
      }
    }), { numRuns: 200 });
  });

  test('clearFullLines is idempotent and dimension-preserving', () => {
    fc.assert(fc.property(
      fc.array(fc.array(fc.boolean(), { minLength: 3, maxLength: 3 }), { minLength: 1, maxLength: 8 }),
      (grid) => {
        const once = eng.clearFullLines(grid);
        const twice = eng.clearFullLines(once);
        assert.deepStrictEqual(once, twice);
        assert.strictEqual(once.length, grid.length);
        assert.strictEqual(once[0].length, grid[0].length);
      }));
  });

  test('union dimensions match g1 dimensions', () => {
    fc.assert(fc.property(
      fc.array(fc.array(fc.boolean(), { minLength: 2, maxLength: 2 }), { minLength: 2, maxLength: 2 }),
      fc.array(fc.array(fc.boolean(), { minLength: 2, maxLength: 2 }), { minLength: 2, maxLength: 2 }),
      fc.integer({ min: -2, max: 2 }), fc.integer({ min: -2, max: 2 }),
      (g1, g2, y1, x1) => {
        const u = eng.union(g1, y1, x1, g2, 0, 0);
        assert.strictEqual(u.length, g1.length);
        assert.strictEqual(u[0].length, g1[0].length);
      }));
  });
});
