import { describe, test } from 'node:test';
import assert from 'node:assert/strict';
import fc from 'fast-check';
import { T } from '../model.js';
import * as TI from './testInstance.js';
import { oracle7 } from './oracle.js';
import { assertSnapshotsEqual } from '../../t1/tests/oracle.js';

const eng = T(TI.Piece, TI.InitialMainGrid, TI.ForbiddenGrid, TI.RotGrid, TI.InitialY, TI.InitialX,
              TI.PW, TI.FY, TI.FX, TI.NextLen, TI.Player, TI.HostIndex);
const N = TI.Player.length;

// model.js's snapshot() wraps mg as a read-only { height, width, cell(y,x) }
// accessor (D1, t1/model.js); assertSnapshotsEqual (t1/tests/oracle.js) compares
// it correctly against the oracle's own plain-array mg.

const bagArb = fc.constantFrom(['A', 'B'], ['B', 'A']);
const plArb = fc.integer({ min: 0, max: N - 1 });

// No 'notice' event with no prior disconnect — noticeDisconnection has no
// guard in model.js either, so it's safe to fire unconditionally; whether it
// changes anything is left to deepStrictEqual to catch either way.
const eventArb = fc.oneof(
  fc.record({ kind: fc.constant('move'), pl: plArb, dy: fc.constantFrom(-1, 0), dx: fc.constantFrom(-1, 0, 1) }),
  fc.record({ kind: fc.constant('rotate'), pl: plArb, cw: fc.boolean() }),
  fc.record({ kind: fc.constant('fix'), pl: plArb, bagNew: bagArb, hole: fc.integer({ min: 0, max: 1 }) }),
  fc.record({ kind: fc.constant('fall'), pl: plArb, bagNew: bagArb, hole: fc.integer({ min: 0, max: 1 }) }),
  fc.record({ kind: fc.constant('hold'), pl: plArb, bagNew: bagArb }),
  fc.record({ kind: fc.constant('drop'), pl: plArb, bagNew: bagArb, hole: fc.integer({ min: 0, max: 1 }) }),
  fc.record({ kind: fc.constant('kick'), pl: plArb, cw: fc.boolean() }),
  fc.record({ kind: fc.constant('disconnect'), pl: plArb }),
  fc.record({ kind: fc.constant('notice'), pl: plArb }),
);

function makeBagsFnFromSeed(bag) { return () => bag; }
function constHolesFn(hole) { return () => hole; }

// Drains every pending message in lockstep on both sides — the harness owns
// the "network" (messages/connected live in the oracle only, §6.9), so this
// is where receiveGarbage/receiveGameover/receiveDisconnect actually get
// exercised, immediately after whatever produced them (§9's "no transport"
// multi-instance harness).
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

function applyEvent(machines, e) {
  const m = machines[e.pl];
  switch (e.kind) {
    case 'move': return m.movePiece(e.dy, e.dx);
    case 'rotate': return m.rotatePiece(e.cw);
    case 'fix': return m.fixPiece(e.bagNew, constHolesFn(e.hole));
    case 'fall': return m.fallStep(e.bagNew, constHolesFn(e.hole));
    case 'hold': return m.holdPiece(e.bagNew);
    case 'drop': return m.dropPiece(e.bagNew, constHolesFn(e.hole));
    case 'kick': return m.rotateKickPiece(e.cw);
    case 'disconnect': return null; // no Machine method exists (§4-T7f) — oracle only
    case 'notice': m.noticeDisconnection(); return true;
  }
}

function applyEvent7(s, e, params) {
  switch (e.kind) {
    case 'move': return oracle7.movePiece7(e.pl, e.dy, e.dx, s, params);
    case 'rotate': return oracle7.rotatePiece7(e.pl, e.cw, s, params);
    case 'fix': return oracle7.fixPiece7(e.pl, constHolesFn(e.hole), e.bagNew, s, params);
    case 'fall': return oracle7.fallStep7(e.pl, constHolesFn(e.hole), e.bagNew, s, params);
    case 'hold': return oracle7.holdPiece7(e.pl, e.bagNew, s, params);
    case 'drop': return oracle7.dropPiece7(e.pl, constHolesFn(e.hole), e.bagNew, s, params);
    case 'kick': return oracle7.rotateKickPiece7(e.pl, e.cw, s, params);
    case 'disconnect': return oracle7.disconnectPlayer7(e.pl, s, params);
    case 'notice': return oracle7.noticeDisconnection7(e.pl, s);
  }
}

function assertAllSnapshotsAgree(machines, s) {
  for (let pl = 0; pl < N; pl++) {
    assertSnapshotsEqual(eng.snapshot(machines[pl]), oracle7.snapshotOf7(s, pl), `mismatch for player ${pl}`);
  }
}

describe('T7 model.js properties', () => {
  test('winnerMulti never returns true for more than one player at once', () => {
    fc.assert(fc.property(bagArb, fc.array(eventArb, { maxLength: 60 }), (initBag, events) => {
      const machines = [];
      for (let pl = 0; pl < N; pl++) machines[pl] = new eng.Machine(pl, makeBagsFnFromSeed(initBag));
      for (const e of events) {
        if (['move', 'rotate', 'fix', 'fall', 'hold', 'drop', 'kick'].includes(e.kind)) applyEvent(machines, e);
        const winners = machines.filter((m) => m.winner).length;
        assert.ok(winners <= 1, 'at most one player may believe herself the winner at a time');
      }
    }), { numRuns: 100 });
  });

  test('differential oracle: every player\'s snapshot agrees at every step, all event kinds incl. messages/disconnect', () => {
    const params = oracle7.makeParams7(TI);
    fc.assert(fc.property(bagArb, fc.array(eventArb, { maxLength: 80 }), (initBag, events) => {
      const machines = TI.Player.map((pl) => new eng.Machine(pl, makeBagsFnFromSeed(initBag)));
      let s = oracle7.initState7(TI.Player.map(() => makeBagsFnFromSeed(initBag)), params);
      assertAllSnapshotsAgree(machines, s);

      for (const e of events) {
        applyEvent(machines, e);
        const r = applyEvent7(s, e, params);
        if (r) s = r;
        s = drainAll(s, machines, params);
        assertAllSnapshotsAgree(machines, s);
      }
    }), { numRuns: 100 });
  });
});
