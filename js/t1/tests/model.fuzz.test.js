import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import { T } from '../model.js';
import * as TI from './testInstance.js';

const eng = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
              TI.PW, TI.FY, TI.FX);

function randOf(arr) { return arr[Math.floor(Math.random() * arr.length)]; }

function randomTrace(steps) {
  const m = new eng.Machine(randOf(TI.Piece));
  let sawGameover = false;
  for (let i = 0; i < steps; i++) {
    const kind = Math.floor(Math.random() * 4);
    assert.doesNotThrow(() => {
      if (kind === 0) m.movePiece(randOf([-1, 0]), randOf([-1, 0, 1]));
      else if (kind === 1) m.rotatePiece(Math.random() < 0.5);
      else if (kind === 2) m.fixPiece(randOf(TI.Piece));
      else m.fallStep(randOf(TI.Piece));
    });

    assert.strictEqual(eng.typeOK(m), true);
    for (const f of [m.py, m.px, m.pr, m.clearedLines])
      assert.ok(Math.abs(f) <= Number.MAX_SAFE_INTEGER);
    if (sawGameover) assert.strictEqual(m.gameover, true);
    if (m.gameover) sawGameover = true;
  }
}

describe('T1 model.js fuzz', () => {
  test('long random traces over the test instance: no throw + typeOK + bounds + gameover-monotone', () => {
    for (let trial = 0; trial < 20; trial++) randomTrace(2000);
  });

  test('adversarial checkAxioms: malformed params trip an assertion', () => {
    const originalAssert = console.assert;
    let tripped = false;
    console.assert = (cond) => { if (!cond) tripped = true; };
    try {
      // ragged grid
      tripped = false;
      const raggedGrid = [[false, false], [false]];
      const badEng = T(TI.Piece, raggedGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
                        TI.PW, TI.FY, TI.FX);
      badEng.checkAxioms();
      assert.strictEqual(tripped, true);

      // non-primitive piece
      tripped = false;
      const badEng2 = T([{}], TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, () => 4, () => 1,
                         TI.PW, TI.FY, TI.FX);
      badEng2.checkAxioms();
      assert.strictEqual(tripped, true);

      // B > MAX_SAFE_INTEGER (force via a tiny MAX_SAFE_INTEGER override)
      tripped = false;
      const badEng3 = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
                         TI.PW, TI.FY, TI.FX, 1 /* MAX_SAFE_INTEGER */);
      badEng3.checkAxioms();
      assert.strictEqual(tripped, true);

      // negative FY
      tripped = false;
      const badEng4 = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
                         TI.PW, -1, TI.FX);
      badEng4.checkAxioms();
      assert.strictEqual(tripped, true);
    } finally {
      console.assert = originalAssert;
    }
  });
});
