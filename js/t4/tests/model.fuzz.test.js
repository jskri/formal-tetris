import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { oracle4 } from './oracle.js';
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
  let holdEverSet = false;

  for (let i = 0; i < steps; i++) {
    const kind = Math.floor(Math.random() * 5);
    assert.doesNotThrow(() => {
      if (kind === 0) m.movePiece(randOf([-1, 0]), randOf([-1, 0, 1]));
      else if (kind === 1) m.rotatePiece(Math.random() < 0.5);
      else if (kind === 2) m.fixPiece(shuffleBag());
      else if (kind === 3) m.fallStep(shuffleBag());
      else m.holdPiece(shuffleBag());
    });

    assert.strictEqual(eng.T3Eng.T2Eng.T1Eng.typeOK(m.s3.s2.s1), true);

    // bag_ prefix validity (see checkInvariants' own comment for why this,
    // not isPieceSet(bag_), is the checkable representational invariant)
    assert.ok(m.bag_.length > 0 && m.bag_.length <= TI.Piece.length);
    assert.strictEqual(new Set(m.bag_).size, m.bag_.length);
    assert.ok(m.bag_.every(p => TI.Piece.includes(p)));
    assert.strictEqual(m.next_.length, TI.NextLen);
    assert.ok(m.next_.every(p => TI.Piece.includes(p)));

    // T3-level invariants transfer to the embedded s3
    assert.ok(!m.s3.swapped || m.s3.hold !== null);
    assert.ok(!m.gameover || !m.s3.swapped);
    if (holdEverSet) assert.notStrictEqual(m.s3.hold, null);
    if (m.s3.hold !== null) holdEverSet = true;
  }
}

describe('T4 model.js fuzz', () => {
  test('long random traces: no throw + invariants + bag-prefix validity', () => {
    for (let trial = 0; trial < 20; trial++) randomTrace(1500);
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
          const kind = Math.floor(Math.random() * 5);
          if (kind === 0) m.movePiece(randOf([-1, 0]), randOf([-1, 0, 1]));
          else if (kind === 1) m.rotatePiece(Math.random() < 0.5);
          else if (kind === 2) m.fixPiece(shuffleBag());
          else if (kind === 3) m.fallStep(shuffleBag());
          else m.holdPiece(shuffleBag());
          eng.checkInvariants(m, `trial${trial}/step${step}`);
        }
      }
    } finally {
      console.assert = originalAssert;
    }
    assert.strictEqual(fired, 0);
  });

  test('differential oracle agreement over random traces', () => {
    const params = oracle4.makeParams4(TI);
    for (let trial = 0; trial < 20; trial++) {
      const bagsTable = [];
      const bagsFn = (i) => { while (bagsTable.length <= i) bagsTable.push(shuffleBag()); return bagsTable[i]; };

      const m = new eng.Machine(bagsFn);
      let rs = oracle4.initState4(bagsFn, params);
      assertSnapshotsEqual(eng.snapshot(m), oracle4.snapshotOf4(rs));

      for (let step = 0; step < 150; step++) {
        const kind = Math.floor(Math.random() * 5);
        if (kind === 0) {
          const dy = randOf([-1, 0]), dx = randOf([-1, 0, 1]);
          m.movePiece(dy, dx);
          const r = oracle4.movePiece4(dy, dx, rs, params);
          if (r) rs = r;
        } else if (kind === 1) {
          const cw = Math.random() < 0.5;
          m.rotatePiece(cw);
          const r = oracle4.rotatePiece4(cw, rs, params);
          if (r) rs = r;
        } else if (kind === 2) {
          const bagNew = shuffleBag();
          m.fixPiece(bagNew);
          const r = oracle4.fixPiece4(bagNew, rs, params);
          if (r) rs = r;
        } else if (kind === 3) {
          const bagNew = shuffleBag();
          m.fallStep(bagNew);
          const r = oracle4.fallStep4(bagNew, rs, params);
          if (r) rs = r;
        } else {
          const bagNew = shuffleBag();
          m.holdPiece(bagNew);
          const r = oracle4.holdPiece4(bagNew, rs, params);
          if (r) rs = r;
        }
        assertSnapshotsEqual(eng.snapshot(m), oracle4.snapshotOf4(rs));
      }
    }
  });

  test('adversarial checkAxioms (delegated through T3/T2/T1) and own NextLen axiom', () => {
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

      tripped = false;
      const badEng2 = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
                         TI.PW, TI.FY, TI.FX, 0 /* NextLen must be > 0 */);
      badEng2.checkAxioms();
      assert.strictEqual(tripped, true);
    } finally {
      console.assert = originalAssert;
    }
  });
});
