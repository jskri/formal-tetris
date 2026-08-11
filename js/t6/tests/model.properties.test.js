import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import fc from 'fast-check';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { oracle6 } from './oracle.js';
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
  fc.record({ kind: fc.constant('kick'), cw: fc.boolean() }),
);

function applyEvent(m, e) {
  switch (e.kind) {
    case 'move': return m.movePiece(e.dy, e.dx);
    case 'rotate': return m.rotatePiece(e.cw);
    case 'fix': return m.fixPiece(e.bagNew);
    case 'fall': return m.fallStep(e.bagNew);
    case 'hold': return m.holdPiece(e.bagNew);
    case 'drop': return m.dropPiece(e.bagNew);
    case 'kick': return m.rotateKickPiece(e.cw);
  }
}

function applyEvent6(rs, e, params) {
  switch (e.kind) {
    case 'move': return oracle6.movePiece6(e.dy, e.dx, rs, params);
    case 'rotate': return oracle6.rotatePiece6(e.cw, rs, params);
    case 'fix': return oracle6.fixPiece6(e.bagNew, rs, params);
    case 'fall': return oracle6.fallStep6(e.bagNew, rs, params);
    case 'hold': return oracle6.holdPiece6(e.bagNew, rs, params);
    case 'drop': return oracle6.dropPiece6(e.bagNew, rs, params);
    case 'kick': return oracle6.rotateKickPiece6(e.cw, rs, params);
  }
}

function makeBagsFnFromSeed(bags) {
  return (i) => bags[i % bags.length];
}

describe('T6 model.js properties', () => {
  test('rotateKickPiece and rotatePiece are exclusive: never both fire for the same input', () => {
    fc.assert(fc.property(bagArb, fc.boolean(), (initBag, cw) => {
      const m = new eng.Machine(makeBagsFnFromSeed([initBag]));
      const canPlain = eng.T1Eng.canRotatePiece(cw, m.s1);
      const snapBefore = eng.snapshot(m);
      const kickFired = m.rotateKickPiece(cw);
      if (canPlain) {
        assert.strictEqual(kickFired, false);
        assertSnapshotsEqual(eng.snapshot(m), snapBefore);
      }
    }), { numRuns: 200 });
  });

  test('differential oracle: every snapshot field agrees at every step, all seven event kinds', () => {
    const params = oracle6.makeParams6(TI);
    fc.assert(fc.property(bagArb, fc.array(eventArb, { maxLength: 120 }), (initBag, events) => {
      const bagsFn = makeBagsFnFromSeed([initBag]);
      const m = new eng.Machine(bagsFn);
      let rs = oracle6.initState6(bagsFn, params);
      assertSnapshotsEqual(eng.snapshot(m), oracle6.snapshotOf6(rs));
      for (const e of events) {
        applyEvent(m, e);
        const r = applyEvent6(rs, e, params);
        if (r) rs = r;
        assertSnapshotsEqual(eng.snapshot(m), oracle6.snapshotOf6(rs));
      }
    }), { numRuns: 200 });
  });
});
