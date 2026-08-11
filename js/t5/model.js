import { T as T4 } from '../t4/model.js';

const CHECK_INVARIANTS = false;

// spec: module T5 (parameter order identical to T4's — T5 adds no abstract parameters)
export function T(
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX,
  NextLen,
  MAX_SAFE_INTEGER = Number.MAX_SAFE_INTEGER,
) {
  const T4Eng = T4(Piece, InitialMainGrid, ForbiddenGrid, RotGrid, InitialY, InitialX,
                    PW, FY, FX, NextLen, MAX_SAFE_INTEGER);
  const T1Eng = T4Eng.T1Eng; // flattened — one hop regardless of how many models are stacked

  // ── Free functions (T5.v source order) ────────────────────────────────

  // spec: ShadowYImpl + ShadowY, combined (JS has no nat/Z distinction to keep
  // them separate for). Takes a T1-state-shaped object (duck-typed; in practice
  // always this.s1, the flattened getter — a real T1.Machine).
  //
  // Fuel-bounded, not py-bounded: py can legitimately go as low as -(PW-1) — a
  // piece anchored in a PW×PW rotation grid (fixed so rotation doesn't offset
  // py/px) can have its only occupied cells near the top of that box, so the
  // anchor itself can go negative while every occupied cell stays within the
  // main grid (AxiomsRotGrid guarantees >=1 occupied cell, at local row <= PW-1,
  // so Valid(py) is guaranteed false once py <= -PW, giving fuel = py+PW-1 as an
  // exact bound — not a cap at 0, which would stop the search too early for any
  // piece/rotation whose occupied cells sit high in its own bounding box).
  function shadowY(s1) {
    const valid = T1Eng.valid;
    let py = s1.py;
    let fuel = py + PW - 1;
    while (fuel > 0) {
      if (!valid(s1.mg, s1.p, py - 1, s1.px, s1.pr)) break;
      py -= 1;
      fuel -= 1;
    }
    return py;
  }

  function checkInvariants(s, message, isOccupied = (c => Piece.includes(c))) {
    T4Eng.checkInvariants(s.s4, message, isOccupied);
    // LowestShadowY's own guard is `gameover = false ->`; checking gy against a
    // fresh shadowY computation only makes sense under that same precondition —
    // a freshly-spawned piece under gameover isn't guaranteed Valid at its own
    // position, so shadowY's recomputation would be checking a claim T5.v itself
    // doesn't make in that state.
    if (!s.gameover) {
      const expected = shadowY(s.s1);
      console.assert(s.gy === expected, `LowestShadowY (gy matches shadowY) failed @ ${message}`);
      console.assert(s.gy <= s.s1.py, `gy <= py failed @ ${message}`);
    }
  }

  // ── Machine: encapsulates T5.State ─────────────────────────
  class Machine {
    // spec: Init bags H
    constructor(bagsFn) {
      this.s4 = new T4Eng.Machine(bagsFn);        // spec: T4.Init bags H
      this.gy = shadowY(this.s1);                  // spec: ShadowY s4
      if (CHECK_INVARIANTS) checkInvariants(this, 'Init');
    }

    // spec: gameover s — T5.v's own gameover helper (T4.gameover (s4 s))
    get gameover() { return this.s4.gameover; }

    // Flattened access — see T3.Machine's own get s1() for rationale.
    get s1() { return this.s4.s1; }

    // read-through getters — every T4-level field controller.js reads directly
    // outside snapshot() (same rationale as T4's §6.7)
    get level() { return this.s4.level; }
    get totalClearedLines() { return this.s4.totalClearedLines; }
    get combo() { return this.s4.combo; }
    get perfectClear() { return this.s4.perfectClear; }
    get score() { return this.s4.score; }

    // spec: UpdateShadowY s s4' — recomputes gy from the current s4
    updateShadowY() {
      this.gy = shadowY(this.s1);
    }

    // spec: MovePiece dy dx — full use; gy refreshed only on success
    movePiece(dy, dx) {
      const fired = this.s4.movePiece(dy, dx);
      if (fired) this.updateShadowY();
      if (CHECK_INVARIANTS) checkInvariants(this, 'movePiece');
      return fired;
    }

    // spec: RotatePiece cw — full use; gy refreshed only on success
    rotatePiece(cw) {
      const fired = this.s4.rotatePiece(cw);
      if (fired) this.updateShadowY();
      if (CHECK_INVARIANTS) checkInvariants(this, 'rotatePiece');
      return fired;
    }

    // spec: FixPiece bagNew H — full use; gy refreshed only on success
    fixPiece(bagNew) {
      const fired = this.s4.fixPiece(bagNew);
      if (fired) this.updateShadowY();
      if (CHECK_INVARIANTS) checkInvariants(this, 'fixPiece');
      return fired;
    }

    // spec: FallStep bagNew H
    fallStep(bagNew) {
      if (this.movePiece(-1, 0)) return true; // req-piece-fall
      return this.fixPiece(bagNew);           // req-piece-fix
    }

    // spec: HoldPiece bagNew H — full use; gy refreshed only on success
    holdPiece(bagNew) {
      const fired = this.s4.holdPiece(bagNew);
      if (fired) this.updateShadowY();
      if (CHECK_INVARIANTS) checkInvariants(this, 'holdPiece');
      return fired;
    }

    // spec: DropPiece bagNew H — relocate to gy (px unchanged), then fix
    // (req-piece-drop). A single upfront gameover check suffices here, unlike
    // T4's fixPiece: given ¬gameover before the drop, LowestShadowY guarantees
    // Valid(gy) and ¬Valid(gy-1) for the current px/pr/mg, which is exactly
    // T1.FixPiece's own guard on the relocated state — no case exists where the
    // relocation is followed by a rejection, so no peek-then-commit ordering is
    // needed.
    dropPiece(bagNew) {
      T4Eng.assertPieceSet(bagNew);
      if (this.gameover) return false;
      const s1 = this.s1;
      // spec: NewPieceYXState (gy s) (px s) s — px s, not a literal, since only
      // py is meant to change here; T1.NewPieceYXState overrides both
      // coordinates unconditionally, so the caller must pass px's current value
      // explicitly to keep it unchanged.
      const r = T1Eng.newPieceYXState(this.gy, s1.px, s1);
      s1.mg = r.mg;                 // written for uniformity (unchanged value)
      s1.p = r.p;                   // written for uniformity (unchanged value)
      s1.py = r.py;                 // spec: NewPieceYXState's one real change here
      s1.px = r.px;                 // written for uniformity (unchanged value)
      s1.pr = r.pr;                 // written for uniformity (unchanged value)
      s1.gameover = r.gameover;     // written for uniformity (unchanged value)
      s1.clearedLines = r.clearedLines; // written for uniformity (unchanged value)
      return this.fixPiece(bagNew); // guaranteed to fire, given LowestShadowY
    }
  } // class Machine

  // spec: snapshot — extends T4's inline, plus gy
  function snapshot(machine) {
    return {
      ...T4Eng.snapshot(machine.s4),
      gy: machine.gy,
    };
  }

  return {
    // free functions (§5 order)
    shadowY,

    // inner engine
    T4Eng,
    T1Eng, // flattened
    checkAxioms: T4Eng.checkAxioms, // no new axioms in T5

    // helpers / invariant checkers
    checkInvariants,

    // machine
    Machine,
    snapshot,
  };
}
