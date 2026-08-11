import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { oracle2 } from './oracle.js';
import { assertSnapshotsEqual } from '../../t1/tests/oracle.js';

const eng = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
              TI.PW, TI.FY, TI.FX);

// model.js's snapshot() wraps mg as a read-only { height, width, cell(y,x) }
// accessor (D1, t1/model.js); the oracle's own mg stays a plain nested array
// (it faithfully models T1.v's genuinely bool-valued Grid.L, untouched).
// assertSnapshotsEqual (t1/tests/oracle.js) compares the two representations
// correctly regardless of which shape either side is in.

function randOf(arr) { return arr[Math.floor(Math.random() * arr.length)]; }

function randomTrace(steps) {
  const p0 = randOf(TI.Piece);
  const m = new eng.Machine(p0);
  let prevTotal = 0;
  let prevLevel = 1;
  let prevScore = 0;

  for (let i = 0; i < steps; i++) {
    const kind = Math.floor(Math.random() * 4);
    assert.doesNotThrow(() => {
      if (kind === 0) m.movePiece(randOf([-1, 0]), randOf([-1, 0, 1]));
      else if (kind === 1) m.rotatePiece(Math.random() < 0.5);
      else if (kind === 2) m.fixPiece(randOf(TI.Piece));
      else m.fallStep(randOf(TI.Piece));
    });

    // T1 invariants transfer to the embedded s1 (§2 of proofs.md)
    assert.strictEqual(eng.T1Eng.typeOK(m.s1), true);

    // safe-integer + LevelCorrect + non-negativity
    for (const f of [m.score, m.level, m.combo, m.totalClearedLines])
      assert.ok(Number.isSafeInteger(f));
    assert.strictEqual(m.level, 1 + Math.floor(m.totalClearedLines / 10));
    assert.ok(m.combo >= 0);
    assert.ok(m.score >= 0);
    assert.ok(m.totalClearedLines >= 0);

    // monotonicity
    assert.ok(m.score >= prevScore);
    assert.ok(m.level >= prevLevel);
    assert.ok(m.totalClearedLines >= prevTotal);

    // a clear this step (detected via totalClearedLines delta, not s1.clearedLines,
    // which rides through move/rotate unchanged) strictly raises score, unless
    // score is already saturated at MAX_SAFE_INTEGER.
    if (m.totalClearedLines > prevTotal && prevScore < Number.MAX_SAFE_INTEGER)
      assert.ok(m.score > prevScore);

    prevTotal = m.totalClearedLines;
    prevLevel = m.level;
    prevScore = m.score;
  }
}

describe('T2 model.js fuzz', () => {
  test('long random traces over the test instance: no throw + invariants + monotonicity', () => {
    for (let trial = 0; trial < 20; trial++) randomTrace(1500);
  });

  test('differential oracle agreement over random traces', () => {
    const params = oracle2.makeParams(TI);
    for (let trial = 0; trial < 20; trial++) {
      const p0 = randOf(TI.Piece);
      const m = new eng.Machine(p0);
      let rs = oracle2.initState(p0, params);
      assertSnapshotsEqual(eng.snapshot(m), oracle2.snapshotOf(rs));

      for (let step = 0; step < 150; step++) {
        const kind = Math.floor(Math.random() * 4);
        if (kind === 0) {
          const dy = randOf([-1, 0]), dx = randOf([-1, 0, 1]);
          m.movePiece(dy, dx);
          const r = oracle2.movePiece(dy, dx, rs, params);
          if (r) rs = r;
        } else if (kind === 1) {
          const cw = Math.random() < 0.5;
          m.rotatePiece(cw);
          const r = oracle2.rotatePiece(cw, rs, params);
          if (r) rs = r;
        } else if (kind === 2) {
          const pNew = randOf(TI.Piece);
          m.fixPiece(pNew);
          const r = oracle2.fixPiece(pNew, rs, params);
          if (r) rs = r;
        } else {
          const pNew = randOf(TI.Piece);
          m.fallStep(pNew);
          const r = oracle2.fallStep(pNew, rs, params);
          if (r) rs = r;
        }
        assertSnapshotsEqual(eng.snapshot(m), oracle2.snapshotOf(rs));
      }
    }
  });

  test('adversarial checkAxioms (delegated to T1): malformed params trip an assertion', () => {
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
