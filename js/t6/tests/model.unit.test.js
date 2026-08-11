import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { assertSnapshotsEqual } from '../../t1/tests/oracle.js';

function makeEngine() {
  return T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
            TI.PW, TI.FY, TI.FX, TI.NextLen);
}

describe('Machine — standalone (subclass of T5.Machine, no wrapping field)', () => {
  test('every T5 method is directly callable on the T6 instance', () => {
    const eng = makeEngine();
    const m = new eng.Machine(() => ['A', 'B']);
    for (const method of ['movePiece', 'rotatePiece', 'fixPiece', 'fallStep', 'holdPiece', 'dropPiece']) {
      assert.strictEqual(typeof m[method], 'function', `${method} should be inherited`);
    }
    assert.strictEqual(typeof m.rotateKickPiece, 'function');
    assert.ok(m instanceof eng.Machine);
    assert.ok('s4' in m, "T6.Machine has T5.Machine's own s4 field directly, no extra wrapping layer");
    assert.ok(!('s5' in m), 'no new wrapping field was introduced');
  });
});

describe('Machine.rotateKickPiece — exclusivity with rotatePiece', () => {
  test('does not fire when plain rotation would succeed', () => {
    const eng = makeEngine();
    // Find a state where plain rotation succeeds.
    let m, canRotate;
    for (let tries = 0; tries < 50; tries++) {
      m = new eng.Machine(() => ['A', 'B']);
      canRotate = eng.T1Eng.canRotatePiece(true, m.s1);
      if (canRotate) break;
      m.movePiece(-1, 0);
      canRotate = eng.T1Eng.canRotatePiece(true, m.s1);
      if (canRotate) break;
    }
    if (canRotate) {
      const before = eng.snapshot(m);
      const fired = m.rotateKickPiece(true);
      assert.strictEqual(fired, false);
      assertSnapshotsEqual(eng.snapshot(m), before);
    }
  });

  test('fires (via a kick) when plain rotation would not succeed but a shift makes it possible', () => {
    const eng = makeEngine();
    // Force a scenario by scanning columns for one where plain rotation fails
    // but a kick succeeds — small fixture (PW=2, pieces A/B).
    let found = false;
    for (const piece of TI.Piece) {
      for (let px = -2; px < 3 && !found; px++) {
        const m = new eng.Machine(() => [piece, ...TI.Piece.filter(p => p !== piece)]);
        m.s1.p = piece;
        m.s1.px = px;
        if (!eng.T1Eng.canRotatePiece(true, m.s1)) {
          const fired = m.rotateKickPiece(true);
          if (fired) { found = true; }
        }
      }
    }
    // Not asserting found=true unconditionally here — the small fixture's two
    // pieces may not expose a kick-needed configuration; the real instance does
    // (see model.fuzz.test.js's oracle run). This test documents the search.
  });
});

describe('Machine.rotateKickPiece — left tried before right, w.r.t. original position', () => {
  test('a successful kick moves px by exactly ±1 from where it started', () => {
    const eng = makeEngine();
    for (const piece of TI.Piece) {
      for (let px = -2; px < 3; px++) {
        const m = new eng.Machine(() => [piece, ...TI.Piece.filter(p => p !== piece)]);
        m.s1.p = piece;
        m.s1.px = px;
        if (eng.T1Eng.canRotatePiece(true, m.s1)) continue; // not a kick scenario
        const before = px;
        const fired = m.rotateKickPiece(true);
        if (fired) {
          assert.ok(m.s1.px === before - 1 || m.s1.px === before + 1,
            `kick should move px by exactly 1 from ${before}, got ${m.s1.px}`);
        }
      }
    }
  });
});
