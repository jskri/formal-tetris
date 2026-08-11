import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { oracle3 } from './oracle.js';
import { assertSnapshotsEqual } from '../../t1/tests/oracle.js';

const eng = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
              TI.PW, TI.FY, TI.FX);

// model.js's snapshot() wraps mg as a read-only { height, width, cell(y,x) }
// accessor (D1, t1/model.js); assertSnapshotsEqual (t1/tests/oracle.js) compares
// it correctly against the oracle's own plain-array mg.

function randOf(arr) { return arr[Math.floor(Math.random() * arr.length)]; }

function randomTrace(steps) {
  const m = new eng.Machine(randOf(TI.Piece));
  let holdEverSet = false;

  for (let i = 0; i < steps; i++) {
    const kind = Math.floor(Math.random() * 5);
    assert.doesNotThrow(() => {
      if (kind === 0) m.movePiece(randOf([-1, 0]), randOf([-1, 0, 1]));
      else if (kind === 1) m.rotatePiece(Math.random() < 0.5);
      else if (kind === 2) m.fixPiece(randOf(TI.Piece));
      else if (kind === 3) m.fallStep(randOf(TI.Piece));
      else m.holdPiece(randOf(TI.Piece));
    });

    // T2 invariants transfer to the embedded s2 (delegated typeOK/checkInvariants)
    assert.strictEqual(eng.T2Eng.T1Eng.typeOK(m.s2.s1), true);

    // SwappedImplyHoldSome
    assert.ok(!m.swapped || m.hold !== null);
    // GameoverImplyNotSwapped
    assert.ok(!m.gameover || !m.swapped);
    // hold typeOK: Piece | null
    assert.ok(m.hold === null || TI.Piece.includes(m.hold));

    // HoldMonotone: once hold is set, it never reverts to null
    if (holdEverSet) assert.notStrictEqual(m.hold, null);
    if (m.hold !== null) holdEverSet = true;
  }
}

describe('T3 model.js fuzz', () => {
  test('long random traces: no throw + invariants (SwappedImplyHoldSome, GameoverImplyNotSwapped, HoldMonotone)', () => {
    for (let trial = 0; trial < 20; trial++) randomTrace(1500);
  });

  test('differential oracle agreement over random traces', () => {
    const params = oracle3.makeParams(TI);
    for (let trial = 0; trial < 20; trial++) {
      const p0 = randOf(TI.Piece);
      const m = new eng.Machine(p0);
      let rs = oracle3.initState3(p0, params);
      assertSnapshotsEqual(eng.snapshot(m), oracle3.snapshotOf3(rs));

      for (let step = 0; step < 150; step++) {
        const kind = Math.floor(Math.random() * 5);
        if (kind === 0) {
          const dy = randOf([-1, 0]), dx = randOf([-1, 0, 1]);
          m.movePiece(dy, dx);
          const r = oracle3.movePiece3(dy, dx, rs, params);
          if (r) rs = r;
        } else if (kind === 1) {
          const cw = Math.random() < 0.5;
          m.rotatePiece(cw);
          const r = oracle3.rotatePiece3(cw, rs, params);
          if (r) rs = r;
        } else if (kind === 2) {
          const pNew = randOf(TI.Piece);
          m.fixPiece(pNew);
          const r = oracle3.fixPiece3(pNew, rs, params);
          if (r) rs = r;
        } else if (kind === 3) {
          const pNew = randOf(TI.Piece);
          m.fallStep(pNew);
          const r = oracle3.fallStep3(pNew, rs, params);
          if (r) rs = r;
        } else {
          const pNew = randOf(TI.Piece);
          m.holdPiece(pNew);
          const r = oracle3.holdPiece3(pNew, rs, params);
          if (r) rs = r;
        }
        assertSnapshotsEqual(eng.snapshot(m), oracle3.snapshotOf3(rs));
      }
    }
  });

  test('adversarial checkAxioms (delegated through T2/T1): malformed params trip an assertion', () => {
    const originalAssert = console.assert;
    let tripped = false;
    console.assert = (cond) => { if (!cond) tripped = true; };
    try {
      tripped = false;
      const raggedGrid = [[false, false], [false]];
      const badEng = T(TI.Piece, raggedGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
                        TI.PW, TI.FY, TI.FX);
      badEng.checkAxioms();
      assert.strictEqual(tripped, true);
    } finally {
      console.assert = originalAssert;
    }
  });
});
