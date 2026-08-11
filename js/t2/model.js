import { T as T1 } from '../t1/model.js';
import { natSub, natDiv, capAdd } from '../lib/utils.js';

const CHECK_INVARIANTS = false;

// spec: module T2 (parameter order identical to T1's — T2 adds no abstract parameters)
export function T(
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX,
  MAX_SAFE_INTEGER = Number.MAX_SAFE_INTEGER,
) {
  const T1Eng = T1(Piece, InitialMainGrid, ForbiddenGrid, RotGrid, InitialY, InitialX,
                    PW, FY, FX, MAX_SAFE_INTEGER);

  // ── Free functions (non-state Rocq defs), T2.v source order ──────────────

  // spec: LineClearPoints clearedLines level
  function lineClearPoints(clearedLines, level) {
    switch (clearedLines) {
      case 0: return 0;
      case 1: return 100 * level;
      case 2: return 300 * level;
      case 3: return 500 * level;
      default: return 800 * level;
    }
  }

  // spec: ComboPoints level combo
  function comboPoints(level, combo) {
    return combo > 0 ? 50 * combo * level : 0;
  }

  // spec: PerfectClearPoints perfectClear clearedLines level
  function perfectClearPoints(perfectClear, clearedLines, level) {
    if (!perfectClear) return 0;
    switch (clearedLines) {
      case 0: return 0;
      case 1: return 800 * level;
      case 2: return 1200 * level;
      case 3: return 1800 * level;
      default: return 2000 * level;
    }
  }

  // spec: Points clearedLines level combo perfectClear — req-score-formula
  function points(clearedLines, level, combo, perfectClear) {
    return lineClearPoints(clearedLines, level)
         + comboPoints(level, combo)
         + perfectClearPoints(perfectClear, clearedLines, level);
  }

  // spec: EmptyGridb g
  function emptyGridb(g) {
    return g.every(row => row.every(c => !T1Eng.occ(c)));
  }

  function checkInvariants(s, message, isOccupied = (c => Piece.includes(c))) {
    T1Eng.checkInvariants(s.s1, message, isOccupied);
    // LevelCorrect
    console.assert(s.level === 1 + Math.floor(s.totalClearedLines / 10),
      `LevelCorrect failed @ ${message}`);
    console.assert(s.combo >= 0, `combo >= 0 failed @ ${message}`);
    console.assert(s.totalClearedLines >= 0, `totalClearedLines >= 0 failed @ ${message}`);
    console.assert(s.score >= 0, `score >= 0 failed @ ${message}`);
    for (const f of [s.score, s.level, s.combo, s.totalClearedLines])
      console.assert(Number.isSafeInteger(f), `safe-integer field failed @ ${message}`);
  }

  // ── Machine: encapsulates T2.State ─────────────────────────
  class Machine {
    // spec: Init p
    constructor(p) {
      this.s1 = new T1Eng.Machine(p);       // spec: T1.Init p (validates T1's checkAxioms)
      this.score = 0;                        // req-score-init
      this.level = 1;                        // req-level-init
      this.combo = 0;
      this.perfectClear = false;
      this.totalClearedLines = 0;
      if (CHECK_INVARIANTS) checkInvariants(this, 'Init');
    }

    // spec: MovePiece dy dx — delegate; scalars unchanged (§4-T2d)
    movePiece(dy, dx) {
      const fired = this.s1.movePiece(dy, dx);
      if (CHECK_INVARIANTS) checkInvariants(this, 'movePiece');
      return fired;
    }

    // spec: RotatePiece cw — delegate; scalars unchanged
    rotatePiece(cw) {
      const fired = this.s1.rotatePiece(cw);
      if (CHECK_INVARIANTS) checkInvariants(this, 'rotatePiece');
      return fired;
    }

    // spec: FixPiece p_new — the only non-trivial T2 logic
    fixPiece(pNew) {
      const fired = this.s1.fixPiece(pNew);                             // 1
      if (!fired) return false;                                          // 2
      const clearedLines = this.s1.clearedLines;                         // 3: T2.v s1'.(clearedLines)
      const combo2 = (clearedLines === 0) ? 0 : capAdd(this.combo, 1, MAX_SAFE_INTEGER); // 4
      const perfectClear2 = emptyGridb(this.s1.mg);                      // 5
      const pts = points(clearedLines, this.level,
                         natSub(combo2, 1), perfectClear2);               // 6: OLD level
      const total2 = capAdd(this.totalClearedLines, clearedLines, MAX_SAFE_INTEGER); // 7
      this.combo = combo2;                                                // 8
      this.perfectClear = perfectClear2;                                  // 9
      this.score = capAdd(this.score, pts, MAX_SAFE_INTEGER);             // 10: OLD level used in pts
      this.totalClearedLines = total2;                                    // 11
      this.level = 1 + natDiv(total2, 10);                                // 12: NEW total
      if (CHECK_INVARIANTS) checkInvariants(this, 'fixPiece');
      return true;                                                        // 13
    }

    // spec: gameover s1 — convenience read-only accessor, not a T2.State field;
    // gameover lives on the embedded T1 state (fₛ-projected), this is a pass-through.
    get gameover() {
      return this.s1.gameover;
    }

    // spec: FallStep p_new
    fallStep(pNew) {
      if (this.movePiece(-1, 0)) return true; // T2.MovePiece (-1) 0
      return this.fixPiece(pNew);             // T2.FixPiece
    }
  } // class Machine

  // spec: snapshot — extends T1's inline, plus the five T2 fields
  function snapshot(machine) {
    return {
      ...T1Eng.snapshot(machine.s1),
      score: machine.score,
      level: machine.level,
      combo: machine.combo,
      perfectClear: machine.perfectClear,
      totalClearedLines: machine.totalClearedLines,
    };
  }

  return {
    // free functions (§5 order)
    lineClearPoints,
    comboPoints,
    perfectClearPoints,
    points,
    emptyGridb,
    fullLineCount: T1Eng.fullLineCount, // re-exported from T1 (§4-T2a); not redefined here

    // inner engine (re-exported free functions, checkAxioms, etc.)
    T1Eng,
    checkAxioms: T1Eng.checkAxioms, // no new axioms in T2

    // helpers / invariant checkers
    checkInvariants,

    // machine
    Machine,
    snapshot,
  };
}
