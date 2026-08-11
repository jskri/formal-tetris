import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import fc from 'fast-check';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { oracle5 } from './oracle.js';
import { assertSnapshotsEqual } from '../../t1/tests/oracle.js';

const eng = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
              TI.PW, TI.FY, TI.FX, TI.NextLen);

// model.js's snapshot() wraps mg as a read-only { height, width, cell(y,x) }
// accessor (D1, t1/model.js); assertSnapshotsEqual (t1/tests/oracle.js) compares
// it correctly against the oracle's own plain-array mg, or against another
// model.js snapshot.

const bagArb = fc.constantFrom(['A', 'B'], ['B', 'A']);
const eventArb = fc.oneof(
  fc.record({ kind: fc.constant('move'), dy: fc.constantFrom(-1, 0), dx: fc.constantFrom(-1, 0, 1) }),
  fc.record({ kind: fc.constant('rotate'), cw: fc.boolean() }),
  fc.record({ kind: fc.constant('fix'), bagNew: bagArb }),
  fc.record({ kind: fc.constant('fall'), bagNew: bagArb }),
  fc.record({ kind: fc.constant('hold'), bagNew: bagArb }),
  fc.record({ kind: fc.constant('drop'), bagNew: bagArb }),
);

function applyEvent(m, e) {
  switch (e.kind) {
    case 'move': return m.movePiece(e.dy, e.dx);
    case 'rotate': return m.rotatePiece(e.cw);
    case 'fix': return m.fixPiece(e.bagNew);
    case 'fall': return m.fallStep(e.bagNew);
    case 'hold': return m.holdPiece(e.bagNew);
    case 'drop': return m.dropPiece(e.bagNew);
  }
}

function applyEvent5(rs, e, params) {
  switch (e.kind) {
    case 'move': return oracle5.movePiece5(e.dy, e.dx, rs, params);
    case 'rotate': return oracle5.rotatePiece5(e.cw, rs, params);
    case 'fix': return oracle5.fixPiece5(e.bagNew, rs, params);
    case 'fall': return oracle5.fallStep5(e.bagNew, rs, params);
    case 'hold': return oracle5.holdPiece5(e.bagNew, rs, params);
    case 'drop': return oracle5.dropPiece5(e.bagNew, rs, params);
  }
}

function makeBagsFnFromSeed(bags) {
  return (i) => bags[i % bags.length];
}

describe('T5 model.js properties', () => {
  test('gy always equals a fresh shadowY computation (when ¬gameover); gy <= py; gy >= -(PW-1)', () => {
    fc.assert(fc.property(bagArb, fc.array(eventArb, { maxLength: 150 }), (initBag, events) => {
      const m = new eng.Machine(makeBagsFnFromSeed([initBag]));
      for (const e of events) {
        assert.doesNotThrow(() => applyEvent(m, e));
        if (!m.gameover) {
          assert.strictEqual(m.gy, eng.shadowY(m.s4.s3.s2.s1));
          assert.ok(m.gy <= m.s4.s3.s2.s1.py);
          assert.ok(m.gy >= -(TI.PW - 1));
        }
      }
    }), { numRuns: 200 });
  });

  test('differential oracle: every snapshot field agrees at every step', () => {
    const params = oracle5.makeParams5(TI);
    fc.assert(fc.property(bagArb, fc.array(eventArb, { maxLength: 120 }), (initBag, events) => {
      const bagsFn = makeBagsFnFromSeed([initBag]);
      const m = new eng.Machine(bagsFn);
      let rs = oracle5.initState5(bagsFn, params);
      assertSnapshotsEqual(eng.snapshot(m), oracle5.snapshotOf5(rs));
      for (const e of events) {
        applyEvent(m, e);
        const r = applyEvent5(rs, e, params);
        if (r) rs = r;
        assertSnapshotsEqual(eng.snapshot(m), oracle5.snapshotOf5(rs));
      }
    }), { numRuns: 200 });
  });

  test('dropPiece: guard-fail leaves the state untouched', () => {
    fc.assert(fc.property(bagArb, bagArb, (initBag, bagNew) => {
      const m = new eng.Machine(makeBagsFnFromSeed([initBag]));
      m.s4.s3.s2.s1.gameover = true;
      const before = eng.snapshot(m);
      const fired = m.dropPiece(bagNew);
      assert.strictEqual(fired, false);
      assertSnapshotsEqual(eng.snapshot(m), before);
    }), { numRuns: 50 });
  });
});
