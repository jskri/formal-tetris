import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { oracle5 } from './oracle.js';
import { assertSnapshotsEqual } from '../../t1/tests/oracle.js';

const eng = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
              TI.PW, TI.FY, TI.FX, TI.NextLen);

// model.js's snapshot() wraps mg as a read-only { height, width, cell(y,x) }
// accessor (D1, t1/model.js); assertSnapshotsEqual (t1/tests/oracle.js) compares
// it correctly against the oracle's own plain-array mg.

function randOf(arr) { return arr[Math.floor(Math.random() * arr.length)]; }
function shuffleBag() {
  const a = TI.Piece.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}
function makeBagsFn() {
  const bags = [];
  return (i) => { while (bags.length <= i) bags.push(shuffleBag()); return bags[i]; };
}

function randomTrace(steps) {
  const m = new eng.Machine(makeBagsFn());
  for (let i = 0; i < steps; i++) {
    const kind = Math.floor(Math.random() * 6);
    assert.doesNotThrow(() => {
      if (kind === 0) m.movePiece(randOf([-1, 0]), randOf([-1, 0, 1]));
      else if (kind === 1) m.rotatePiece(Math.random() < 0.5);
      else if (kind === 2) m.fixPiece(shuffleBag());
      else if (kind === 3) m.fallStep(shuffleBag());
      else if (kind === 4) m.holdPiece(shuffleBag());
      else m.dropPiece(shuffleBag());
    });

    assert.strictEqual(eng.T4Eng.T3Eng.T2Eng.T1Eng.typeOK(m.s4.s3.s2.s1), true);

    if (!m.gameover) {
      const expected = eng.shadowY(m.s4.s3.s2.s1);
      assert.strictEqual(m.gy, expected);
      assert.ok(m.gy <= m.s4.s3.s2.s1.py);
      assert.ok(m.gy >= -(TI.PW - 1));
    }
  }
}

describe('T5 model.js fuzz', () => {
  test('long random traces: no throw + gy invariants (incl. dropPiece)', () => {
    for (let trial = 0; trial < 20; trial++) randomTrace(1500);
  });

  test('differential oracle agreement over random traces, all six event kinds', () => {
    const params = oracle5.makeParams5(TI);
    for (let trial = 0; trial < 20; trial++) {
      const bagsFn = makeBagsFn();
      const m = new eng.Machine(bagsFn);
      let rs = oracle5.initState5(bagsFn, params);
      assertSnapshotsEqual(eng.snapshot(m), oracle5.snapshotOf5(rs));

      for (let step = 0; step < 150; step++) {
        const kind = Math.floor(Math.random() * 6);
        let r = null;
        if (kind === 0) {
          const dy = randOf([-1, 0]), dx = randOf([-1, 0, 1]);
          m.movePiece(dy, dx);
          r = oracle5.movePiece5(dy, dx, rs, params);
        } else if (kind === 1) {
          const cw = Math.random() < 0.5;
          m.rotatePiece(cw);
          r = oracle5.rotatePiece5(cw, rs, params);
        } else if (kind === 2) {
          const bagNew = shuffleBag();
          m.fixPiece(bagNew);
          r = oracle5.fixPiece5(bagNew, rs, params);
        } else if (kind === 3) {
          const bagNew = shuffleBag();
          m.fallStep(bagNew);
          r = oracle5.fallStep5(bagNew, rs, params);
        } else if (kind === 4) {
          const bagNew = shuffleBag();
          m.holdPiece(bagNew);
          r = oracle5.holdPiece5(bagNew, rs, params);
        } else {
          const bagNew = shuffleBag();
          m.dropPiece(bagNew);
          r = oracle5.dropPiece5(bagNew, rs, params);
        }
        if (r) rs = r;
        assertSnapshotsEqual(eng.snapshot(m), oracle5.snapshotOf5(rs));
      }
    }
  });

  test('checkInvariants never fires spuriously across many steps', () => {
    const originalAssert = console.assert;
    let fired = 0;
    console.assert = (cond) => { if (!cond) fired++; };
    try {
      for (let trial = 0; trial < 10; trial++) {
        const m = new eng.Machine(makeBagsFn());
        eng.checkInvariants(m, 'init');
        for (let step = 0; step < 300; step++) {
          const kind = Math.floor(Math.random() * 6);
          if (kind === 0) m.movePiece(randOf([-1, 0]), randOf([-1, 0, 1]));
          else if (kind === 1) m.rotatePiece(Math.random() < 0.5);
          else if (kind === 2) m.fixPiece(shuffleBag());
          else if (kind === 3) m.fallStep(shuffleBag());
          else if (kind === 4) m.holdPiece(shuffleBag());
          else m.dropPiece(shuffleBag());
          eng.checkInvariants(m, `trial${trial}/step${step}`);
        }
      }
    } finally {
      console.assert = originalAssert;
    }
    assert.strictEqual(fired, 0);
  });
});
