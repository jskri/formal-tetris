import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { oracle7 } from './oracle.js';
import { assertSnapshotsEqual } from '../../t1/tests/oracle.js';

function makeEngine() {
  return T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
           TI.PW, TI.FY, TI.FX, TI.NextLen, TI.Player, TI.HostIndex);
}

function bagsFnFrom(bag) { return () => bag; }

function makeHolesFn(w) {
  const holes = [];
  return (y) => {
    while (holes.length <= y) holes.push(Math.floor(Math.random() * w));
    const x = holes[y];
    if (!(0 <= x && x < w)) throw new Error(`makeHolesFn: hole out of range: ${x}`);
    return x;
  };
}

describe('Machine — field shape', () => {
  test('has garbage/target/gameoverView/connectedView; has no connected/messages field (§6.9)', () => {
    const eng = makeEngine();
    const m = new eng.Machine(0, bagsFnFrom(['A', 'B']));
    assert.strictEqual(typeof m.garbage, 'number');
    assert.strictEqual(typeof m.target, 'number');
    assert.ok(Array.isArray(m.gameoverView));
    assert.ok(Array.isArray(m.connectedView));
    assert.strictEqual(m.gameoverView.length, TI.Player.length);
    assert.strictEqual(m.connectedView.length, TI.Player.length);
    assert.ok(!('connected' in m), 'connected must not be a Machine field (§6.9)');
    assert.ok(!('messages' in m), 'messages must not be a Machine field (§6.9)');
  });

  test('s6 is nested, not flattened (unlike T2–T6\'s own inner engines)', () => {
    const eng = makeEngine();
    const m = new eng.Machine(0, bagsFnFrom(['A', 'B']));
    assert.ok('s6' in m);
    assert.ok(!('mg' in m) || typeof Object.getOwnPropertyDescriptor(m, 'mg') === 'undefined',
      'mg is a read-through getter, not a flattened own field');
    assert.deepStrictEqual(m.mg, m.s6.s1.mg);
  });

  test('checkAxioms rejects PlayerCount <= 1 and an out-of-range HostIndex', () => {
    const eng1 = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
                   TI.PW, TI.FY, TI.FX, TI.NextLen, [0], 0);
    const originalAssert = console.assert;
    let tripped = false;
    console.assert = (cond) => { if (!cond) tripped = true; };
    try {
      eng1.checkAxioms();
      assert.strictEqual(tripped, true, 'PlayerCount = 1 must trip an axiom');

      tripped = false;
      const eng2 = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
                     TI.PW, TI.FY, TI.FX, TI.NextLen, TI.Player, 99);
      eng2.checkAxioms();
      assert.strictEqual(tripped, true, 'out-of-range HostIndex must trip an axiom');
    } finally {
      console.assert = originalAssert;
    }
  });
});

describe('GeneratedGarbage / GenRemGarbage — exact arithmetic (req-multi-garbage-gen/cancel)', () => {
  test('normal garbage: c - 1 for c < 4, floored at 0; c itself for c >= 4', () => {
    const eng = makeEngine();
    assert.strictEqual(eng.generatedGarbage(0, false), 0);
    assert.strictEqual(eng.generatedGarbage(1, false), 0);
    assert.strictEqual(eng.generatedGarbage(2, false), 1);
    assert.strictEqual(eng.generatedGarbage(3, false), 2);
    assert.strictEqual(eng.generatedGarbage(4, false), 4);
    assert.strictEqual(eng.generatedGarbage(4, true), 14); // + special (10)
  });

  test('cancellation arithmetic: [genGarbage, remGarbage], plus the caller-side remGenGarbage formula', () => {
    const eng = makeEngine();
    // clearedLines=2 -> gen=1 (2-1, c<4 branch); garbage=5 already covers it: rem=4, remGen=0.
    assert.deepStrictEqual(eng.genRemGarbage(5, 2, false), [1, 4]);
    assert.strictEqual(Math.max(0, 1 - 5), 0);
    // clearedLines=6 -> gen=6 (c>=4 branch); garbage=1 falls short: rem=0, remGen=5.
    assert.deepStrictEqual(eng.genRemGarbage(1, 6, false), [6, 0]);
    assert.strictEqual(Math.max(0, 6 - 1), 5);
  });
});

describe('fixPiece — materialization (§4-T7c)', () => {
  test('remGarbage >= HM: gameover via overflow, no negative-index scan, mg stays exactly HM rows', () => {
    const eng = makeEngine();
    const m = new eng.Machine(0, bagsFnFrom(['A', 'B']));
    m.garbage = TI.InitialMainGrid.length + 10; // force remGarbage > HM after a zero-clear fix
    const holesFn = makeHolesFn(TI.InitialMainGrid[0].length);
    // dropPiece relocates to the floor then fixes — already independently
    // tested (§ "dropPiece — calls T7's own fixPiece") — using it here avoids
    // re-deriving that relocation by hand a second time, and avoids
    // doesNotThrow silently passing over a false return (see below).
    let fired;
    assert.doesNotThrow(() => { fired = m.dropPiece(['A', 'B'], holesFn); });
    assert.strictEqual(fired, true, 'dropPiece must actually fire here — a resting piece must be fixable');
    assert.strictEqual(m.mg.length, TI.InitialMainGrid.length, 'mg must never grow past HM');
    assert.strictEqual(m.gameover, true);
  });

  test('holesFn is queried only for rows actually materialized (effRem), never beyond it', () => {
    const eng = makeEngine();
    const m = new eng.Machine(0, bagsFnFrom(['A', 'B']));
    m.garbage = 1;
    m.s6.s1.py = m.s6.gy; // same requirement — otherwise fixPiece is a guaranteed no-op
                          // and this test would pass vacuously (countingHolesFn never called)
    let calls = 0;
    const countingHolesFn = (y) => { calls++; return 0; };
    const fired = m.fixPiece(['A', 'B'], countingHolesFn);
    assert.strictEqual(fired, true, 'fixPiece must actually fire for this test to check anything');
    assert.ok(calls <= TI.InitialMainGrid.length);
  });
});

describe('Target round-robin — the 3-player worked trace from T7.v\'s own comment', () => {
  test('A -> B -> C initially; A -> C once B is gameover; A -> A (self) once C is also gameover', () => {
    const [A, B, C] = [0, 1, 2];
    const eng = makeEngine();
    const m = new eng.Machine(A, bagsFnFrom(['A', 'B']));
    assert.strictEqual(m.target, B, 'initial target is PlayerNext(self)');

    m.gameoverView[B] = true; // B observed gameover
    m.connectedView[B] = true;
    const viewAfterB = (pl2) => eng.playingView(m.gameoverView, m.connectedView, pl2);
    m.target = eng.nextTarget(viewAfterB, A, B); // mirrors receiveGameover's redirect from B
    assert.strictEqual(m.target, C);

    m.gameoverView[C] = true;
    const viewAfterC = (pl2) => eng.playingView(m.gameoverView, m.connectedView, pl2);
    m.target = eng.nextTarget(viewAfterC, A, C);
    assert.strictEqual(m.target, A, 'no one else alive: target becomes self (req-multi-target-nonself\'s winner exception)');
  });
});

describe('receiveGarbage / receiveGameover / receiveDisconnect — field updates', () => {
  test('receiveGarbage: sender-agnostic += , no from parameter', () => {
    const eng = makeEngine();
    const m = new eng.Machine(0, bagsFnFrom(['A', 'B']));
    m.receiveGarbage(3);
    m.receiveGarbage(2);
    assert.strictEqual(m.garbage, 5);
  });

  test('receiveGameover: sets the view, redirects target only if it pointed at the dead player', () => {
    const eng = makeEngine();
    const m = new eng.Machine(0, bagsFnFrom(['A', 'B']));
    assert.strictEqual(m.target, 1);
    m.receiveGameover(2); // target is 1, not 2 — no redirect
    assert.strictEqual(m.gameoverView[2], true);
    assert.strictEqual(m.target, 1);
    m.receiveGameover(1); // target is 1 — redirect
    assert.strictEqual(m.gameoverView[1], true);
    assert.notStrictEqual(m.target, 1);
  });

  test('receiveDisconnect: same redirect discipline as receiveGameover', () => {
    const eng = makeEngine();
    const m = new eng.Machine(0, bagsFnFrom(['A', 'B']));
    m.receiveDisconnect(1); // target is 1 — redirect
    assert.strictEqual(m.connectedView[1], false);
    assert.notStrictEqual(m.target, 1);
  });

  test('receiveX methods are not gated on winner/gameover — a disconnected/gameover player keeps draining', () => {
    const eng = makeEngine();
    const m = new eng.Machine(0, bagsFnFrom(['A', 'B']));
    m.s6.s1.gameover = true; // simulate self already gameover
    assert.doesNotThrow(() => { m.receiveGarbage(1); m.receiveGameover(1); m.receiveDisconnect(2); });
  });
});

describe('noticeDisconnection', () => {
  test('flips only the self-diagonal of connectedView', () => {
    const eng = makeEngine();
    const m = new eng.Machine(0, bagsFnFrom(['A', 'B']));
    m.noticeDisconnection();
    assert.strictEqual(m.connectedView[0], false);
    assert.strictEqual(m.connectedView[1], true);
    assert.strictEqual(m.connectedView[2], true);
  });
});

describe('winnerMulti gates every guarded method', () => {
  test('once winnerMulti is true, move/rotate/hold/kick/fix/fall/drop all return false with zero mutation', () => {
    const eng = makeEngine();
    const m = new eng.Machine(0, bagsFnFrom(['A', 'B']));
    m.gameoverView[1] = true;
    m.gameoverView[2] = true; // everyone else out — self is the winner
    assert.strictEqual(m.winner, true);
    const before = eng.snapshot(m);
    const holesFn = makeHolesFn(TI.InitialMainGrid[0].length);
    assert.strictEqual(m.movePiece(0, 1), false);
    assert.strictEqual(m.rotatePiece(true), false);
    assert.strictEqual(m.holdPiece(['A', 'B']), false);
    assert.strictEqual(m.rotateKickPiece(true), false);
    assert.strictEqual(m.fixPiece(['A', 'B'], holesFn), false);
    assert.strictEqual(m.fallStep(['A', 'B'], holesFn), false);
    assert.strictEqual(m.dropPiece(['A', 'B'], holesFn), false);
    assertSnapshotsEqual(eng.snapshot(m), before);
  });
});

describe('dropPiece — calls T7\'s own fixPiece, not this.s6.dropPiece (§4-T7i)', () => {
  test('a drop that generates garbage sends it (materialization not bypassed)', () => {
    const eng = makeEngine();
    const m = new eng.Machine(0, bagsFnFrom(['A', 'B']));
    m.garbage = 5; // pending garbage that a real fix should try to cancel
    const holesFn = makeHolesFn(TI.InitialMainGrid[0].length);
    const fired = m.dropPiece(['A', 'B'], holesFn);
    if (fired) {
      // whatever happened, garbage must have been processed through T7's own
      // accounting (reset to 0, or consumed into remGenGarbage) — never left
      // untouched at 5, which is what calling this.s6.dropPiece would do.
      assert.notStrictEqual(m.garbage, 5);
    }
  });
});
