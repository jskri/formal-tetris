import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import fc from 'fast-check';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { oracle2 } from './oracle.js';
import { assertSnapshotsEqual } from '../../t1/tests/oracle.js';

const eng = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
              TI.PW, TI.FY, TI.FX);

// model.js's snapshot() wraps mg as a read-only { height, width, cell(y,x) }
// accessor (D1, t1/model.js); assertSnapshotsEqual (t1/tests/oracle.js) compares
// it correctly against the oracle's own plain-array mg.

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

function applyEvent2(rs, e, params) {
  switch (e.kind) {
    case 'move': return oracle2.movePiece(e.dy, e.dx, rs, params);
    case 'rotate': return oracle2.rotatePiece(e.cw, rs, params);
    case 'fix': return oracle2.fixPiece(e.pNew, rs, params);
    case 'fall': return oracle2.fallStep(e.pNew, rs, params);
  }
}

describe('T2 model.js properties', () => {
  test('invariants hold after every step: T1 typeOK on s1, level>=1, monotonicity, safe integers', () => {
    fc.assert(fc.property(pieceArb, fc.array(eventArb, { maxLength: 200 }), (p0, events) => {
      const m = new eng.Machine(p0);
      let prevScore = 0, prevLevel = 1, prevTotal = 0;
      for (const e of events) {
        assert.doesNotThrow(() => applyEvent(m, e));
        assert.strictEqual(eng.T1Eng.typeOK(m.s1), true);
        assert.ok(m.level >= 1);
        assert.strictEqual(m.level, 1 + Math.floor(m.totalClearedLines / 10));
        for (const f of [m.score, m.level, m.combo, m.totalClearedLines])
          assert.ok(Number.isSafeInteger(f));
        assert.ok(m.score >= prevScore);
        assert.ok(m.level >= prevLevel);
        assert.ok(m.totalClearedLines >= prevTotal);
        if (m.totalClearedLines > prevTotal && prevScore < Number.MAX_SAFE_INTEGER)
          assert.ok(m.score > prevScore);
        prevScore = m.score; prevLevel = m.level; prevTotal = m.totalClearedLines;
      }
    }), { numRuns: 200 });
  });

  test('differential oracle: all six state components agree at every step', () => {
    const params = oracle2.makeParams(TI);
    fc.assert(fc.property(pieceArb, fc.array(eventArb, { maxLength: 150 }), (p0, events) => {
      const m = new eng.Machine(p0);
      let rs = oracle2.initState(p0, params);
      assertSnapshotsEqual(eng.snapshot(m), oracle2.snapshotOf(rs));
      for (const e of events) {
        applyEvent(m, e);
        const r = applyEvent2(rs, e, params);
        if (r) rs = r;
        assertSnapshotsEqual(eng.snapshot(m), oracle2.snapshotOf(rs));
      }
    }), { numRuns: 200 });
  });

  test('points formula matches the T2.v case tables (independent of model.js)', () => {
    fc.assert(fc.property(
      fc.integer({ min: 0, max: 6 }), fc.integer({ min: 1, max: 20 }),
      fc.integer({ min: 0, max: 5 }), fc.boolean(),
      (clearedLines, level, combo, perfectClear) => {
        const lc = [0, 100, 300, 500][clearedLines] ?? 800;
        const expectedLine = lc * level;
        const expectedCombo = combo > 0 ? 50 * combo * level : 0;
        const pcTable = [0, 800, 1200, 1800];
        const expectedPc = perfectClear ? (pcTable[clearedLines] ?? 2000) * level : 0;
        assert.strictEqual(eng.points(clearedLines, level, combo, perfectClear),
          expectedLine + expectedCombo + expectedPc);
      }));
  });
});
