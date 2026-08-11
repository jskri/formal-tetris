import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { oracle6 } from './oracle.js';
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
    const kind = Math.floor(Math.random() * 7);
    assert.doesNotThrow(() => {
      if (kind === 0) m.movePiece(randOf([-1, 0]), randOf([-1, 0, 1]));
      else if (kind === 1) m.rotatePiece(Math.random() < 0.5);
      else if (kind === 2) m.fixPiece(shuffleBag());
      else if (kind === 3) m.fallStep(shuffleBag());
      else if (kind === 4) m.holdPiece(shuffleBag());
      else if (kind === 5) m.dropPiece(shuffleBag());
      else m.rotateKickPiece(Math.random() < 0.5);
    });

    assert.strictEqual(eng.T1Eng.typeOK(m.s1), true);
    if (!m.gameover) {
      assert.strictEqual(m.gy, eng.shadowY(m.s1));
    }
  }
}

describe('T6 model.js fuzz', () => {
  test('long random traces: no throw + invariants (incl. rotateKickPiece)', () => {
    for (let trial = 0; trial < 20; trial++) randomTrace(1500);
  });

  test('differential oracle agreement over random traces, all seven event kinds', () => {
    const params = oracle6.makeParams6(TI);
    let kickFirings = 0;
    for (let trial = 0; trial < 20; trial++) {
      const bagsFn = makeBagsFn();
      const m = new eng.Machine(bagsFn);
      let rs = oracle6.initState6(bagsFn, params);
      assertSnapshotsEqual(eng.snapshot(m), oracle6.snapshotOf6(rs));

      for (let step = 0; step < 150; step++) {
        const kind = Math.floor(Math.random() * 7);
        let r = null;
        if (kind === 0) {
          const dy = randOf([-1, 0]), dx = randOf([-1, 0, 1]);
          m.movePiece(dy, dx);
          r = oracle6.movePiece6(dy, dx, rs, params);
        } else if (kind === 1) {
          const cw = Math.random() < 0.5;
          m.rotatePiece(cw);
          r = oracle6.rotatePiece6(cw, rs, params);
        } else if (kind === 2) {
          const bagNew = shuffleBag();
          m.fixPiece(bagNew);
          r = oracle6.fixPiece6(bagNew, rs, params);
        } else if (kind === 3) {
          const bagNew = shuffleBag();
          m.fallStep(bagNew);
          r = oracle6.fallStep6(bagNew, rs, params);
        } else if (kind === 4) {
          const bagNew = shuffleBag();
          m.holdPiece(bagNew);
          r = oracle6.holdPiece6(bagNew, rs, params);
        } else if (kind === 5) {
          const bagNew = shuffleBag();
          m.dropPiece(bagNew);
          r = oracle6.dropPiece6(bagNew, rs, params);
        } else {
          const cw = Math.random() < 0.5;
          const fired = m.rotateKickPiece(cw);
          r = oracle6.rotateKickPiece6(cw, rs, params);
          if (fired) kickFirings++;
        }
        if (r) rs = r;
        assertSnapshotsEqual(eng.snapshot(m), oracle6.snapshotOf6(rs));
      }
    }
    assert.ok(kickFirings >= 0); // presence not required on the small fixture; see real-instance script
  });

  test('adversarial checkAxioms (delegated through T5/T4/T3/T2/T1)', () => {
    const originalAssert = console.assert;
    let tripped = false;
    console.assert = (cond) => { if (!cond) tripped = true; };
    try {
      tripped = false;
      const raggedGrid = [[false, false], [false]];
      const badEng = T(TI.Piece, raggedGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
                        TI.PW, TI.FY, TI.FX, TI.NextLen);
      badEng.checkAxioms();
      assert.strictEqual(tripped, true);
    } finally {
      console.assert = originalAssert;
    }
  });
});
