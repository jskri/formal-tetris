import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import fc from 'fast-check';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { oracle4 } from './oracle.js';
import { assertSnapshotsEqual } from '../../t1/tests/oracle.js';

const eng = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
              TI.PW, TI.FY, TI.FX, TI.NextLen);

// model.js's snapshot() wraps mg as a read-only { height, width, cell(y,x) }
// accessor (D1, t1/model.js); assertSnapshotsEqual (t1/tests/oracle.js) compares
// it correctly against the oracle's own plain-array mg.

const bagArb = fc.shuffledSubarray(TI.Piece, { minLength: TI.Piece.length, maxLength: TI.Piece.length });
const eventArb = fc.oneof(
  fc.record({ kind: fc.constant('move'), dy: fc.constantFrom(-1, 0), dx: fc.constantFrom(-1, 0, 1) }),
  fc.record({ kind: fc.constant('rotate'), cw: fc.boolean() }),
  fc.record({ kind: fc.constant('fix'), bagNew: bagArb }),
  fc.record({ kind: fc.constant('fall'), bagNew: bagArb }),
  fc.record({ kind: fc.constant('hold'), bagNew: bagArb }),
);

function applyEvent(m, e) {
  switch (e.kind) {
    case 'move': return m.movePiece(e.dy, e.dx);
    case 'rotate': return m.rotatePiece(e.cw);
    case 'fix': return m.fixPiece(e.bagNew);
    case 'fall': return m.fallStep(e.bagNew);
    case 'hold': return m.holdPiece(e.bagNew);
  }
}

function applyEvent4(rs, e, params) {
  switch (e.kind) {
    case 'move': return oracle4.movePiece4(e.dy, e.dx, rs, params);
    case 'rotate': return oracle4.rotatePiece4(e.cw, rs, params);
    case 'fix': return oracle4.fixPiece4(e.bagNew, rs, params);
    case 'fall': return oracle4.fallStep4(e.bagNew, rs, params);
    case 'hold': return oracle4.holdPiece4(e.bagNew, rs, params);
  }
}

function makeBagsFnFromSeed(bags) {
  return (i) => bags[i % bags.length];
}

describe('T4 model.js properties', () => {
  test('bag_ prefix validity, next_ well-formedness, T3 invariants hold after every step', () => {
    fc.assert(fc.property(bagArb, fc.array(eventArb, { maxLength: 150 }), (initBag, events) => {
      const m = new eng.Machine(makeBagsFnFromSeed([initBag]));
      let holdEverSet = false;
      for (const e of events) {
        assert.doesNotThrow(() => applyEvent(m, e));
        assert.strictEqual(eng.T3Eng.T2Eng.T1Eng.typeOK(m.s3.s2.s1), true);
        assert.ok(m.bag_.length > 0 && m.bag_.length <= TI.Piece.length);
        assert.strictEqual(new Set(m.bag_).size, m.bag_.length);
        assert.ok(m.bag_.every(p => TI.Piece.includes(p)));
        assert.strictEqual(m.next_.length, TI.NextLen);
        assert.ok(!m.s3.swapped || m.s3.hold !== null);
        assert.ok(!m.gameover || !m.s3.swapped);
        if (holdEverSet) assert.notStrictEqual(m.s3.hold, null);
        if (m.s3.hold !== null) holdEverSet = true;
      }
    }), { numRuns: 200 });
  });

  test('fixPiece guard-fail leaves bag_/next_ untouched (peek-then-commit)', () => {
    fc.assert(fc.property(bagArb, bagArb, (initBag, bagNew) => {
      const m = new eng.Machine(makeBagsFnFromSeed([initBag]));
      const bagBefore = m.bag_.slice(), nextBefore = m.next_.slice();
      const fired = m.fixPiece(bagNew);
      if (fired) return; // only checking the guard-fail path here
      assert.deepStrictEqual(m.bag_, bagBefore);
      assert.deepStrictEqual(m.next_, nextBefore);
    }), { numRuns: 200 });
  });

  test('differential oracle: every snapshot field agrees at every step', () => {
    fc.assert(fc.property(bagArb, fc.array(eventArb, { maxLength: 120 }), (initBag, events) => {
      const bagsFn = makeBagsFnFromSeed([initBag]); // referentially consistent, per index
      const params = oracle4.makeParams4(TI);
      const m = new eng.Machine(bagsFn);
      let rs = oracle4.initState4(bagsFn, params);
      assertSnapshotsEqual(eng.snapshot(m), oracle4.snapshotOf4(rs));
      for (const e of events) {
        applyEvent(m, e);
        const r = applyEvent4(rs, e, params);
        if (r) rs = r;
        assertSnapshotsEqual(eng.snapshot(m), oracle4.snapshotOf4(rs));
      }
    }), { numRuns: 200 });
  });
});
