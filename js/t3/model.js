import { T as T2 } from '../t2/model.js';

const CHECK_INVARIANTS = false;

// spec: module T3 (parameter order identical to T1/T2 — T3 adds no abstract parameters)
export function T(
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX,
  MAX_SAFE_INTEGER = Number.MAX_SAFE_INTEGER,
) {
  const T2Eng = T2(Piece, InitialMainGrid, ForbiddenGrid, RotGrid, InitialY, InitialX,
                    PW, FY, FX, MAX_SAFE_INTEGER);

  // T3.v defines no non-state free function of its own (§5: none) —
  // `newPieceState` is reached via T2Eng.T1Eng.newPieceState, not redefined.

  function checkInvariants(s, message, isOccupied = (c => Piece.includes(c))) {
    T2Eng.checkInvariants(s.s2, message, isOccupied);
    console.assert(!s.swapped || s.hold !== null, `SwappedImplyHoldSome failed @ ${message}`);
    console.assert(!s.gameover || !s.swapped, `GameoverImplyNotSwapped failed @ ${message}`);
    console.assert(s.hold === null || Piece.includes(s.hold),
      `hold ∈ Piece ∪ {null} failed @ ${message}`);
  }

  // ── Machine: encapsulates T3.State ─────────────────────────
  class Machine {
    // spec: Init p
    constructor(p) {
      this.s2 = new T2Eng.Machine(p);       // spec: T2.Init p
      this.hold = null;                      // None
      this.swapped = false;
      if (CHECK_INVARIANTS) checkInvariants(this, 'Init');
    }

    // spec: gameover s — T3.v's own `gameover` helper (T1.gameover (s1 (s2 s)))
    get gameover() { return this.s2.gameover; }

    // Flattens access to the innermost T1.Machine — this.s2.s1 already works
    // (T2.Machine's own field is literally named s1), but exposing it one level
    // up too keeps the depth of ".s1" access independent of how many models are
    // stacked, so a wrapping model never needs to know T3's own internal shape.
    get s1() { return this.s2.s1; }

    // read-through getters — every T2-level field controller.js reads directly
    // outside snapshot() (implementation.md §6.7)
    get level() { return this.s2.level; }
    get totalClearedLines() { return this.s2.totalClearedLines; }
    get combo() { return this.s2.combo; }
    get perfectClear() { return this.s2.perfectClear; }
    get score() { return this.s2.score; }

    // spec: MovePiece dy dx — delegate; hold/swapped unchanged (full use)
    movePiece(dy, dx) {
      const fired = this.s2.movePiece(dy, dx);
      if (CHECK_INVARIANTS) checkInvariants(this, 'movePiece');
      return fired;
    }

    // spec: RotatePiece cw — delegate; hold/swapped unchanged (full use)
    rotatePiece(cw) {
      const fired = this.s2.rotatePiece(cw);
      if (CHECK_INVARIANTS) checkInvariants(this, 'rotatePiece');
      return fired;
    }

    // spec: FixPiece p_new — delegate, then req-hold-limit reset (partial use)
    fixPiece(pNew) {
      const fired = this.s2.fixPiece(pNew);
      if (!fired) return false;
      this.swapped = false;                  // req-hold-limit
      if (CHECK_INVARIANTS) checkInvariants(this, 'fixPiece');
      return true;
    }

    // spec: FallStep p_new
    fallStep(pNew) {
      if (this.movePiece(-1, 0)) return true; // req-piece-fall
      return this.fixPiece(pNew);             // req-piece-fix
    }

    // spec: HoldPiece p_new — the only non-trivial T3 logic (no-use action)
    holdPiece(pNew) {
      if (!(!this.gameover && !this.swapped)) return false; // real guard (req-hold-limit)
      const p2 = (this.hold !== null) ? this.hold : pNew;   // req-hold-swap / req-hold-empty
      const oldP = this.s2.s1.p;                              // 1: read BEFORE overwritten
      const newS1 = T2Eng.T1Eng.newPieceState(p2, this.s2.s1); // spec: NewPieceState p2 (s1 s2_)
      this.s2.s1.mg = newS1.mg;                                // 2: written for uniformity (unchanged value)
      this.s2.s1.p = newS1.p;
      this.s2.s1.py = newS1.py;
      this.s2.s1.px = newS1.px;
      this.s2.s1.pr = newS1.pr;
      this.s2.s1.gameover = newS1.gameover;
      this.s2.s1.clearedLines = newS1.clearedLines;
      this.hold = oldP;                                        // 3: req-hold
      this.swapped = true;                                     // 4: req-hold-limit
      if (CHECK_INVARIANTS) checkInvariants(this, 'holdPiece');
      return true;
    }
  } // class Machine

  // spec: snapshot — extends T2's inline, plus hold/swapped
  function snapshot(machine) {
    return {
      ...T2Eng.snapshot(machine.s2),
      hold: machine.hold,
      swapped: machine.swapped,
    };
  }

  return {
    // free functions (§5: none)

    // inner engine
    T2Eng,
    T1Eng: T2Eng.T1Eng, // flattened — one hop regardless of how many models are stacked
    checkAxioms: T2Eng.checkAxioms, // no new axioms in T3

    // helpers / invariant checkers
    checkInvariants,

    // machine
    Machine,
    snapshot,
  };
}
