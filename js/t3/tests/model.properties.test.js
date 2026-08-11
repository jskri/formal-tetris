import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import fc from 'fast-check';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { oracle3 } from './oracle.js';
import { assertSnapshotsEqual, gridsEqual } from '../../t1/tests/oracle.js';

const eng = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
              TI.PW, TI.FY, TI.FX);

// model.js's snapshot() wraps mg as a read-only { height, width, cell(y,x) }
// accessor (D1, t1/model.js). gridsEqual compares two grids in either
// representation; assertSnapshotsEqual compares two full snapshots the same way.

const pieceArb = fc.constantFrom(...TI.Piece);
const eventArb = fc.oneof(
  fc.record({ kind: fc.constant('move'), dy: fc.constantFrom(-1, 0), dx: fc.constantFrom(-1, 0, 1) }),
  fc.record({ kind: fc.constant('rotate'), cw: fc.boolean() }),
  fc.record({ kind: fc.constant('fix'), pNew: pieceArb }),
  fc.record({ kind: fc.constant('fall'), pNew: pieceArb }),
  fc.record({ kind: fc.constant('hold'), pNew: pieceArb }),
);

function applyEvent(m, e) {
  switch (e.kind) {
    case 'move': return m.movePiece(e.dy, e.dx);
    case 'rotate': return m.rotatePiece(e.cw);
    case 'fix': return m.fixPiece(e.pNew);
    case 'fall': return m.fallStep(e.pNew);
    case 'hold': return m.holdPiece(e.pNew);
  }
}

function applyEvent3(rs, e, params) {
  switch (e.kind) {
    case 'move': return oracle3.movePiece3(e.dy, e.dx, rs, params);
    case 'rotate': return oracle3.rotatePiece3(e.cw, rs, params);
    case 'fix': return oracle3.fixPiece3(e.pNew, rs, params);
    case 'fall': return oracle3.fallStep3(e.pNew, rs, params);
    case 'hold': return oracle3.holdPiece3(e.pNew, rs, params);
  }
}

describe('T3 model.js properties', () => {
  test('SwappedImplyHoldSome, GameoverImplyNotSwapped, HoldMonotone, T2 typeOK hold after every step', () => {
    fc.assert(fc.property(pieceArb, fc.array(eventArb, { maxLength: 200 }), (p0, events) => {
      const m = new eng.Machine(p0);
      let holdEverSet = false;
      for (const e of events) {
        assert.doesNotThrow(() => applyEvent(m, e));
        assert.strictEqual(eng.T2Eng.T1Eng.typeOK(m.s2.s1), true);
        assert.ok(!m.swapped || m.hold !== null);
        assert.ok(!m.gameover || !m.swapped);
        assert.ok(m.hold === null || TI.Piece.includes(m.hold));
        if (holdEverSet) assert.notStrictEqual(m.hold, null);
        if (m.hold !== null) holdEverSet = true;
      }
    }), { numRuns: 200 });
  });

  test('holdPiece narrow blast radius: only p/py/px/pr/hold/swapped ever change on a firing hold', () => {
    fc.assert(fc.property(pieceArb, pieceArb, (p0, pNew) => {
      const m = new eng.Machine(p0);
      const before = eng.snapshot(m);
      const fired = m.holdPiece(pNew);
      if (!fired) return; // guard failed, nothing to check
      const after = eng.snapshot(m);
      for (const f of ['mg', 'gameover', 'clearedLines', 'score', 'level', 'combo',
                        'perfectClear', 'totalClearedLines']) {
        if (f === 'mg') assert.ok(gridsEqual(after.mg, before.mg), 'mg mismatch');
        else assert.deepStrictEqual(after[f], before[f]);
      }
    }), { numRuns: 200 });
  });

  test('differential oracle: every snapshot field agrees at every step', () => {
    const params = oracle3.makeParams(TI);
    fc.assert(fc.property(pieceArb, fc.array(eventArb, { maxLength: 150 }), (p0, events) => {
      const m = new eng.Machine(p0);
      let rs = oracle3.initState3(p0, params);
      assertSnapshotsEqual(eng.snapshot(m), oracle3.snapshotOf3(rs));
      for (const e of events) {
        applyEvent(m, e);
        const r = applyEvent3(rs, e, params);
        if (r) rs = r;
        assertSnapshotsEqual(eng.snapshot(m), oracle3.snapshotOf3(rs));
      }
    }), { numRuns: 200 });
  });
});
