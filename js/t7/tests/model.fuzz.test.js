import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { oracle7 } from './oracle.js';
import { assertSnapshotsEqual } from '../../t1/tests/oracle.js';

const eng = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
              TI.PW, TI.FY, TI.FX, TI.NextLen, TI.Player, TI.HostIndex);
const N = TI.Player.length;

// model.js's snapshot() wraps mg as a read-only { height, width, cell(y,x) }
// accessor (D1, t1/model.js) — its garbage materialization also goes through the
// same (∪) ∩ Full formula, so a materialized 'garbage' cell collapses to true on
// the oracle's side too. assertSnapshotsEqual (t1/tests/oracle.js) compares the
// two representations correctly either way.

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
function randHolesFn() { return () => Math.floor(Math.random() * TI.InitialMainGrid[0].length); }

function drainAll(s, machines, params) {
  let changed = true;
  while (changed) {
    changed = false;
    for (let from = 0; from < params.PlayerCount; from++) {
      for (let to = 0; to < params.PlayerCount; to++) {
        while (s.messages[from][to].length > 0) {
          const msg = s.messages[from][to][0];
          const r = oracle7.receiveMessage7(to, from, s, params);
          if (!r) break;
          s = r;
          if (msg.type === 'garbage') machines[to].receiveGarbage(msg.n);
          else if (msg.type === 'gameover') machines[to].receiveGameover(from);
          else machines[to].receiveDisconnect(from);
          changed = true;
        }
      }
    }
  }
  return s;
}

function randomStep(machines) {
  const pl = Math.floor(Math.random() * N);
  const m = machines[pl];
  const kind = Math.floor(Math.random() * 9);
  if (kind === 0) m.movePiece(randOf([-1, 0]), randOf([-1, 0, 1]));
  else if (kind === 1) m.rotatePiece(Math.random() < 0.5);
  else if (kind === 2) m.fixPiece(shuffleBag(), randHolesFn());
  else if (kind === 3) m.fallStep(shuffleBag(), randHolesFn());
  else if (kind === 4) m.holdPiece(shuffleBag());
  else if (kind === 5) m.dropPiece(shuffleBag(), randHolesFn());
  else if (kind === 6) m.rotateKickPiece(Math.random() < 0.5);
  else if (kind === 7) { /* disconnect: no Machine method — oracle-only, driven separately */ }
  else m.noticeDisconnection();
}

describe('T7 model.js fuzz', () => {
  test('long random multi-instance traces: no throw + T6-level invariants + T7-level bounds', () => {
    for (let trial = 0; trial < 15; trial++) {
      const machines = [];
      for (let pl = 0; pl < N; pl++) machines[pl] = new eng.Machine(pl, makeBagsFn());
      for (let step = 0; step < 800; step++) {
        assert.doesNotThrow(() => randomStep(machines));
        for (const m of machines) {
          eng.T6Eng.checkInvariants(m.s6, `trial ${trial} step ${step}`);
          assert.ok(m.garbage >= 0);
          assert.ok(Number.isInteger(m.target) && m.target >= 0 && m.target < N);
          assert.strictEqual(m.gameoverView.length, N);
          assert.strictEqual(m.connectedView.length, N);
        }
      }
    }
  });

  test('differential oracle agreement over random multi-instance traces, all event kinds incl. disconnect', () => {
    const params = oracle7.makeParams7(TI);
    for (let trial = 0; trial < 15; trial++) {
      const bagsFns = TI.Player.map(() => makeBagsFn());
      const machines = [];
      for (let pl = 0; pl < N; pl++) machines[pl] = new eng.Machine(pl, bagsFns[pl]);
      let s = oracle7.initState7(bagsFns, params);
      for (let pl = 0; pl < N; pl++) {
        assertSnapshotsEqual(eng.snapshot(machines[pl]), oracle7.snapshotOf7(s, pl));
      }

      for (let step = 0; step < 200; step++) {
        const pl = Math.floor(Math.random() * N);
        const m = machines[pl];
        const kind = Math.floor(Math.random() * 10);
        let r = null;
        if (kind === 0) {
          // console.log('move');
          const dy = randOf([-1, 0]), dx = randOf([-1, 0, 1]);
          m.movePiece(dy, dx);
          r = oracle7.movePiece7(pl, dy, dx, s, params);
        } else if (kind === 1) {
          // console.log('rotate');
          const cw = Math.random() < 0.5;
          m.rotatePiece(cw);
          r = oracle7.rotatePiece7(pl, cw, s, params);
        } else if (kind === 2) {
          // console.log('fix');
          const bagNew = shuffleBag(); const hole = Math.floor(Math.random() * TI.InitialMainGrid[0].length);
          m.fixPiece(bagNew, () => hole);
          r = oracle7.fixPiece7(pl, () => hole, bagNew, s, params);
        } else if (kind === 3) {
          // console.log('fall');
          const bagNew = shuffleBag(); const hole = Math.floor(Math.random() * TI.InitialMainGrid[0].length);
          m.fallStep(bagNew, () => hole);
          r = oracle7.fallStep7(pl, () => hole, bagNew, s, params);
        } else if (kind === 4) {
          // console.log('hold');
          const bagNew = shuffleBag();
          m.holdPiece(bagNew);
          r = oracle7.holdPiece7(pl, bagNew, s, params);
        } else if (kind === 5) {
          // console.log('drop');
          const bagNew = shuffleBag(); const hole = Math.floor(Math.random() * TI.InitialMainGrid[0].length);
          m.dropPiece(bagNew, () => hole);
          r = oracle7.dropPiece7(pl, () => hole, bagNew, s, params);
        } else if (kind === 6) {
          // console.log('kick');
          const cw = Math.random() < 0.5;
          m.rotateKickPiece(cw);
          r = oracle7.rotateKickPiece7(pl, cw, s, params);
        } else if (kind === 7) {
          // console.log('disconnect');
          r = oracle7.disconnectPlayer7(pl, s, params); // no Machine method — oracle only
        } else if (kind === 8) {
          // console.log('notice');
          m.noticeDisconnection();
          r = oracle7.noticeDisconnection7(pl, s);
        } else if (kind === 9) {
          // console.log('receive');
          const from = Math.floor(Math.random() * N);
          if (s.connected[pl] && s.messages[from][pl].length > 0) {
            const [msg, ...rest] = s.messages[from][pl];
            if (msg.type === 'garbage') {
              m.receiveGarbage(msg.n);
            } else if (msg.type === 'gameover') {
              m.receiveGameover(from);
            } else if (msg.type === 'disconnect') {
              m.receiveDisconnect(from);
            } else {
              assert(false, `unknown message type: ${msg.type}`);
            }
          }
          r = oracle7.receiveMessage7(pl, from, s, params);
        } else {
          assert(false, `unknown kind: ${kind}`);
        }
        if (r) s = r;
        // CHECK: Is draining here correct? Why is there no receiveMessage kind
        // in the "if-else-if" chain above?
        // Missing model.js: receiveGarbage, receiveGameover, receiveDisconnect
        // Oracle: move, rotate, hold, kick, fix, fall, drop, receiveMessage,
        // disconnect, notice
        // s = drainAll(s, machines, params);
        for (let p2 = 0; p2 < N; p2++) {
          assertSnapshotsEqual(eng.snapshot(machines[p2]), oracle7.snapshotOf7(s, p2), `trial ${trial} step ${step} player ${p2}`);
        }
      }
    }
  });

  test('adversarial checkAxioms (PlayerCount and HostIndex, delegated through T6-T1)', () => {
    const originalAssert = console.assert;
    let tripped = false;
    console.assert = (cond) => { if (!cond) tripped = true; };
    try {
      tripped = false;
      const raggedGrid = [[false, false], [false]];
      const badEng = T(TI.Piece, raggedGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
                        TI.PW, TI.FY, TI.FX, TI.NextLen, TI.Player, TI.HostIndex);
      badEng.checkAxioms();
      assert.strictEqual(tripped, true, 'a ragged main grid must still trip a T1-level axiom');

      tripped = false;
      const singlePlayerEng = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
                                 TI.PW, TI.FY, TI.FX, TI.NextLen, [0], 0);
      singlePlayerEng.checkAxioms();
      assert.strictEqual(tripped, true, 'PlayerCount = 1 must trip AxiomsPlayer');
    } finally {
      console.assert = originalAssert;
    }
  });
});
