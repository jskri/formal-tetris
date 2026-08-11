import { T as T5 } from '../t5/model.js';

const CHECK_INVARIANTS = false;

// spec: module T6 (parameter order identical to T5's — T6 adds no abstract parameters)
export function T(
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX,
  NextLen,
  MAX_SAFE_INTEGER = Number.MAX_SAFE_INTEGER,
) {
  const T5Eng = T5(Piece, InitialMainGrid, ForbiddenGrid, RotGrid, InitialY, InitialX,
                    PW, FY, FX, NextLen, MAX_SAFE_INTEGER);
  const T1Eng = T5Eng.T1Eng; // flattened

  // No new free functions, no new state fields (T6.v: "No new state fields",
  // "No new parameter"). T6.State = T5.State (a type alias, not a new record),
  // so Machine subclasses T5Eng.Machine directly rather than wrapping it as a
  // field — there is nothing new to wrap.
  class Machine extends T5Eng.Machine {
    // spec: RotateKickPiece cw s — exclusive with T5.RotatePiece (T6.v's own
    // exclusivity guard: this fires only when plain rotation would NOT).
    rotateKickPiece(cw) {
      const s1 = this.s1;
      let fired = false;

      // Pure check — no mutation. This is the one place a side-effect-free
      // probe is unavoidable: unlike a failed rotatePiece() call (which leaves
      // its own fields untouched by construction), there is no way to "try a
      // real rotation and undo it" without first knowing whether it would fire.
      if (!T1Eng.canRotatePiece(cw, s1)) {
        const origPx = s1.px;
        s1.px = origPx - 1;                 // left
        fired = this.rotatePiece(cw);       // reuse T5's own method: re-checks
                                              // validity, mutates pr, refreshes gy
        if (!fired) {
          s1.px = origPx + 1;               // right, w.r.t. the ORIGINAL position
          fired = this.rotatePiece(cw);
        }
        if (!fired) s1.px = origPx;         // both kicks failed: restore
      }

      if (CHECK_INVARIANTS) T5Eng.checkInvariants(this, 'rotateKickPiece');
      return fired;
    }
  } // class Machine

  return {
    ...T5Eng, // free functions, T4Eng, T1Eng, checkAxioms, checkInvariants, snapshot — all unchanged
    Machine,  // overrides T5Eng.Machine with the subclass above
  };
}
