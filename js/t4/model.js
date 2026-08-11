import { T as T3 } from '../t3/model.js';

const CHECK_AXIOMS = true;
const CHECK_INVARIANTS = false;

// spec: module T4 (parameter order: T1-T3's, then NextLen, then defaulted MAX_SAFE_INTEGER)
export function T(
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX,
  NextLen,
  MAX_SAFE_INTEGER = Number.MAX_SAFE_INTEGER,
) {
  const T3Eng = T3(Piece, InitialMainGrid, ForbiddenGrid, RotGrid, InitialY, InitialX,
                    PW, FY, FX, MAX_SAFE_INTEGER);
  const NEXT_LEN = NextLen;
  const NUM_PIECES = Piece.length; // MaxBagLen, derived — not a separate parameter (§3)

  // ── Free functions (T4.v source order) ────────────────────────────────

  // spec: Bijective / PieceSet — dedupe + length suffices by pigeonhole (§3)
  function isPieceSet(arr) {
    return arr.length === NUM_PIECES && new Set(arr).size === NUM_PIECES;
  }

  // spec: H : PieceSet bagNew — runtime realization of the event-level precondition;
  // throws, uncaught by design (§4-T4c, §15.4).
  function assertPieceSet(arr) {
    if (!isPieceSet(arr))
      throw new Error(`assertPieceSet: not a valid piece set: ${JSON.stringify(arr)}`);
  }

  // spec: DrawNextPiece d bagNew — mutates bag_/next_ in place (§4-T4a).
  // Pop-before-refill ordering matters: the piece appended to next_ must come from
  // the OLD bag_ (bag_ (bagLen_-1) in Rocq) even on a resetting draw, never from
  // bagNew — bagNew only becomes the bag for *future* draws.
  function drawOnce(bag_, next_, bagNew) {
    const resetting = bag_.length === 1;   // bagLen_ d <=? 1; BagNonEmpty ⟹ ≤1 ⟺ ===1
    const p = next_.shift();               // next_ 0, consumed
    next_.push(bag_.pop());                // ShiftNext ... (bag_ (bagLen_ - 1))
    if (resetting) bag_.push(...bagNew);   // bagSingle branch: bag_ now empty; refill := bagNew
    return { p, resetting };
  }

  // spec: BuildInitNext + InitPieceAndDraw (§4-T4b).
  function initPieceAndDraw(bagsFn) {
    let bag_ = bagsFn(0).slice();                    // length MaxBagLen (= NUM_PIECES)
    let next_ = Array(NEXT_LEN).fill(bagsFn(0)[0]);  // length NextLen; values arbitrary —
                                                       // every entry is overwritten within
                                                       // NextLen draws below (T4.v line 169's
                                                       // own comment) — only the length has
                                                       // to be right up front.
    let bagIdx = 1;
    for (let k = 0; k < NEXT_LEN; k++) {
      const { resetting } = drawOnce(bag_, next_, bagsFn(bagIdx));
      if (resetting) bagIdx++;
    }
    const { p } = drawOnce(bag_, next_, bagsFn(bagIdx));
    return { p, bag_, next_ };
  }

  // ── Axiom checker ─────────────────────────────────────────────────────
  function checkAxioms() {
    T3Eng.checkAxioms();
    console.assert(Number.isInteger(NEXT_LEN) && NEXT_LEN > 0,
      'AxiomsNextLen: NextLen must be a positive integer');
  }

  function checkInvariants(s, message, isOccupied = (c => Piece.includes(c))) {
    T3Eng.checkInvariants(s.s3, message, isOccupied);
    console.assert(s.bag_.length > 0, `BagNonEmpty failed @ ${message}`);
    // TypeOK (PieceSet (bag s)) is about the *unbounded* Rocq function bag_,
    // bijective on [0, MaxBagLen) regardless of bagLen_'s current value —
    // popped elements aren't "forgotten" there. In the finite-array
    // representation this is not directly checkable once bag_.length <
    // NUM_PIECES (mid-cycle, the common case): isPieceSet(bag_) would require
    // arr.length === NUM_PIECES, which only holds right after a reset. The
    // representable analogue is that bag_ is always a *prefix* of some valid
    // piece set: non-empty (checked above), no longer than NUM_PIECES, and its
    // elements pairwise distinct and drawn from Piece.
    console.assert(s.bag_.length <= NUM_PIECES, `bag_ length bound failed @ ${message}`);
    console.assert(new Set(s.bag_).size === s.bag_.length,
      `bag_ elements not pairwise distinct @ ${message}`);
    console.assert(s.bag_.every(p => Piece.includes(p)), `bag_ ⊆ Piece failed @ ${message}`);
    console.assert(s.next_.length === NEXT_LEN, `next_ length failed @ ${message}`);
    console.assert(s.next_.every(p => Piece.includes(p)), `next_ ⊆ Piece failed @ ${message}`);
  }

  // ── Machine: encapsulates T4.State ─────────────────────────
  class Machine {
    // spec: Init bags H
    constructor(bagsFn) {
      const checkedBagsFn = (i) => { const b = bagsFn(i); assertPieceSet(b); return b; };
      const { p, bag_, next_ } = initPieceAndDraw(checkedBagsFn);
      this.s3 = new T3Eng.Machine(p);   // spec: T3.Init p
      this.bag_ = bag_;
      this.next_ = next_;
      if (CHECK_INVARIANTS) checkInvariants(this, 'Init');
    }

    // spec: gameover s — T4.v's own gameover helper (T3.gameover (s3 s))
    get gameover() { return this.s3.gameover; }

    // Flattened access — see T3.Machine's own get s1() for rationale.
    get s1() { return this.s3.s1; }

    // read-through getters — every T3-level field controller.js reads directly
    // outside snapshot() (same rationale as T3's §6.7)
    get level() { return this.s3.level; }
    get totalClearedLines() { return this.s3.totalClearedLines; }
    get combo() { return this.s3.combo; }
    get perfectClear() { return this.s3.perfectClear; }
    get score() { return this.s3.score; }

    // spec: MovePiece dy dx — delegate; bag_/next_ unchanged (full use)
    movePiece(dy, dx) {
      const fired = this.s3.movePiece(dy, dx);
      if (CHECK_INVARIANTS) checkInvariants(this, 'movePiece');
      return fired;
    }

    // spec: RotatePiece cw — delegate; bag_/next_ unchanged (full use)
    rotatePiece(cw) {
      const fired = this.s3.rotatePiece(cw);
      if (CHECK_INVARIANTS) checkInvariants(this, 'rotatePiece');
      return fired;
    }

    // spec: DrawNextPiece (d s) bagNew, applied to this.bag_/this.next_
    drawNextPiece(bagNew) {
      const { p } = drawOnce(this.bag_, this.next_, bagNew);
      return p;
    }

    // spec: FixPiece bagNew H — peek before the guard, commit only on success (§4-T4d)
    fixPiece(bagNew) {
      assertPieceSet(bagNew);
      const p = this.next_[0];        // pure read of next_ 0 — no mutation yet
      const fired = this.s3.fixPiece(p);
      if (!fired) return false;        // zero mutation: matches every other guarded action
      this.drawNextPiece(bagNew);       // commit now that T3.FixPiece is confirmed to fire
      if (CHECK_INVARIANTS) checkInvariants(this, 'fixPiece');
      return true;
    }

    // spec: FallStep bagNew H
    fallStep(bagNew) {
      if (this.movePiece(-1, 0)) return true; // req-piece-fall
      return this.fixPiece(bagNew);           // req-piece-fix — re-checks bagNew (§4-T4c)
    }

    // spec: HoldPiece bagNew H (§4-T4g, hazard note §4-T4h)
    holdPiece(bagNew) {
      assertPieceSet(bagNew);
      if (this.gameover) return false;
      // spec draws unconditionally and discards the result when hold !== null
      // (T4.v line 228-229); skipping the draw here instead is behaviorally
      // identical (d'' := d s in that branch means bag_/next_ are provably
      // unchanged either way) — see proofs.md §5 for why this needs no
      // fixPiece-style peek-then-commit restructuring.
      const p2 = (this.s3.hold !== null) ? this.s3.hold : this.drawNextPiece(bagNew);
      const fired = this.s3.holdPiece(p2);
      if (!fired) return false;
      if (CHECK_INVARIANTS) checkInvariants(this, 'holdPiece');
      return true;
    }
  } // class Machine

  // spec: snapshot — extends T3's inline, plus next
  function snapshot(machine) {
    return {
      ...T3Eng.snapshot(machine.s3),
      next: machine.next_.slice(), // defensive copy — view.js must never mutate
    };
  }

  // Axioms are properties of the closure-captured instance parameters, fixed
  // for the lifetime of this T(...) call — checked once here, not once per
  // `new Machine(...)` (every restart), since they can never fail differently
  // between one construction and the next.
  if (CHECK_AXIOMS) checkAxioms();

  return {
    // free functions (§5 order)
    isPieceSet,
    assertPieceSet,
    drawOnce,
    initPieceAndDraw,

    // inner engine
    T3Eng,
    T1Eng: T3Eng.T1Eng, // flattened
    checkAxioms,

    // helpers / invariant checkers
    checkInvariants,

    // machine
    Machine,
    snapshot,
  };
}
