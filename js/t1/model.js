import { mod, copyGrid, emptyRows } from '../lib/utils.js';

const CHECK_AXIOMS = true;
const CHECK_INVARIANTS = false;

// spec: module T1 (parameters in Parameter-declaration order, then bound B — D10)
export function T(
  Piece, InitialMainGrid, ForbiddenGrid,
  RotGrid, InitialY, InitialX,
  PW, FY, FX,
  MAX_SAFE_INTEGER = Number.MAX_SAFE_INTEGER,
) {
  const HM = InitialMainGrid.length;
  const WM = InitialMainGrid[0].length;
  const B = Math.max(HM, WM) + PW - 1;

  // Axioms are properties of the closure-captured instance parameters
  // (Piece, RotGrid, InitialY, ...), fixed for the lifetime of this T(...)
  // call — checked once here, not once per `new Machine(...)` (every restart),
  // since they can never fail differently between one construction and the next.
  if (CHECK_AXIOMS) checkAxioms();

  // ── Free functions (non-state Rocq defs), §5 order ───────────────────────

  // m : JS cell → Rocq bool. `false` is the one reserved sentinel (empty);
  // everything else — the literal `true` used by RotGrid/ForbiddenGrid, or a
  // Piece id stored directly in mg — is occupied. Every cell-truth test in this
  // module goes through this, so mg can carry color without changing what any
  // of them mean.
  function occ(c) { return c !== false; }

  // spec: FullyContainedIn g1 y1 x1 g2 y2 x2
  function fullyContainedIn(g1, y1, x1, g2, y2, x2) {
    return g1.every((row, y) =>
      row.every((cell, x) => {
        if (!occ(cell)) return true;
        const oy = y + y1 - y2;
        const ox = x + x1 - x2;
        return 0 <= oy && oy < g2.length && 0 <= ox && ox < g2[0].length && occ(g2[oy][ox]);
      }));
  }

  // spec: BBoxInsideBBox g1 y1 x1 g2 y2 x2
  function bboxInsideBBox(g1, y1, x1, g2, y2, x2) {
    return (y2 <= y1) && (y1 + g1.length - 1 <= y2 + g2.length - 1)
        && (x2 <= x1) && (x1 + g1[0].length - 1 <= x2 + g2[0].length - 1);
  }

  // helper for D2's clearFullLines: is `row` entirely occupied.
  function isFullRow(row) {
    return row.every(occ);
  }

  // spec: IsFullLineb g y
  function isFullLineb(g, y) {
    if (!(0 <= y && y < g.length)) return true; // implb (0≤?y<?Hg) (...) — false antecedent
    return isFullRow(g[y]);
  }

  // spec: Intersect g1 y1 x1 g2 y2 x2
  function intersect(g1, y1, x1, g2, y2, x2) {
    return g1.some((row, y) =>
      row.some((cell, x) => {
        const oy = y + y1 - y2;
        const ox = x + x1 - x2;
        return (0 <= oy && oy < g2.length) && (0 <= ox && ox < g2[0].length)
            && occ(cell) && occ(g2[oy][ox]);
      }));
  }

  // spec: OccupiedInside g1 y1 x1 g2 y2 x2
  function occupiedInside(g1, y1, x1, g2, y2, x2) {
    return g1.every((row, y) =>
      row.every((cell, x) => {
        const oy = y + y1 - y2;
        const ox = x + x1 - x2;
        // implb (L g1 y x) ((0≤?oy<?Hg2) && (0≤?ox<?Wg2))
        return !occ(cell) || (0 <= oy && oy < g2.length && 0 <= ox && ox < g2[0].length);
      }));
  }

  // spec: RotGrid (parameter) — thin pass-through, no copy (read-only callers)
  function rotGrid(p, r) {
    return RotGrid(p, r);
  }

  // spec: Valid g p py px pr
  function valid(g, p, py, px, pr) {
    const rg = rotGrid(p, pr);
    return occupiedInside(rg, py, px, g, 0, 0) && !intersect(rg, py, px, g, 0, 0);
  }

  // spec: Resize g newGh fillValue — not used directly (D2), kept for coverage/testing parity
  function resize(g, newGh, fill) {
    const w = g[0].length;
    return Array.from({ length: newGh }, (_, y) =>
      y < g.length ? g[y].slice() : Array.from({ length: w }, (_, x) => fill(x)));
  }

  // spec: ClearFullLines g — translated as a unit (D2, skill N10)
  function clearFullLines(g) {
    const kept = g.filter(row => !isFullRow(row)); // non-full rows; shares row objects with g
    return kept.concat(emptyRows(g.length - kept.length, g[0].length));
  }

  // spec: Union g1 y1 x1 g2 y2 x2 — returns whichever operand's actual cell
  // value occupies each position (not a collapsed `true`), so color survives
  // a merge. `m` (occ) of the result is unchanged: an occupied cell is still
  // occupied regardless of which operand it came from; Valid guarantees the
  // two operands never both occupy the same cell at any reachable call site,
  // so which one "wins" here is never actually a live choice.
  function union(g1, y1, x1, g2, y2, x2) {
    return g1.map((row, y) =>
      row.map((cell, x) => {
        if (occ(cell)) return cell;
        const oy = y + y1 - y2;
        const ox = x + x1 - x2;
        if ((0 <= oy && oy < g2.length) && (0 <= ox && ox < g2[0].length) && occ(g2[oy][ox]))
          return g2[oy][ox];
        return cell;
      }));
  }

  // spec: FullLineCount g
  function fullLineCount(g) {
    let count = 0;
    for (let y = 0; y < g.length; y++) if (isFullLineb(g, y)) count++;
    return count;
  }

  // spec: NewPieceState p_new s — returns a full state-shaped plain object (unlike
  // every other free function above, which returns a grid/boolean/number), mirroring
  // NewPieceState : State. mg/gameover/clearedLines pass through unchanged; only the
  // piece-identity fields (p, py, px, pr) are rewritten to the fresh-spawn values.
  function newPieceState(pNew, s) {
    return {
      mg: s.mg,
      p: pNew,
      py: InitialY(pNew),
      px: InitialX(pNew),
      pr: 0,
      gameover: s.gameover,
      clearedLines: s.clearedLines,
    };
  }

  // spec: NewPieceYXState pyNew pxNew s — like newPieceState, returns a full
  // state-shaped plain object. Distinct purpose: both py and px are overridden
  // unconditionally; p/pr are copied through unchanged (the piece's type and
  // rotation don't change — this relocates the same piece, it doesn't spawn a
  // different one). Callers that want to preserve one coordinate must pass its
  // current value explicitly (e.g. T5's DropPiece: NewPieceYXState (gy s) (px s) s
  // — px s, not a literal, since only py is meant to change there).
  function newPieceYXState(pyNew, pxNew, s) {
    return {
      mg: s.mg,
      p: s.p,
      py: pyNew,
      px: pxNew,
      pr: s.pr,
      gameover: s.gameover,
      clearedLines: s.clearedLines,
    };
  }

  // spec: CanMovePiece dyx s
  function canMovePiece(dy, dx, s) {
    const dirOK = (dy === 0 && dx === -1) || (dy === 0 && dx === 1) || (dy === -1 && dx === 0);
    return dirOK && valid(s.mg, s.p, s.py + dy, s.px + dx, s.pr);
  }

  // Implementation-freedom helper — no T1.v counterpart. Factors T1.RotatePiece's
  // own guard into a named, side-effect-free predicate so a wrapping model (T6's
  // RotateKickPiece) can check "would rotation succeed" without performing it,
  // instead of duplicating the guard expression at each call site that needs it.
  function canRotatePiece(cw, s) {
    const pr2 = mod(s.pr + (cw ? -1 : 1), 4);
    return !s.gameover && valid(s.mg, s.p, s.py, s.px, pr2);
  }

  // ── Axiom checker ─────────────────────────────────────────────────────
  function checkAxioms() {
    // AxiomsPW
    console.assert(Number.isInteger(PW) && PW > 0, 'AxiomsPW: PW must be a positive integer');

    // D8: Piece is a finite, complete, primitive enumeration
    console.assert(Array.isArray(Piece) && Piece.length > 0, 'D8: Piece must be a non-empty array');
    for (const p of Piece) {
      console.assert(['string', 'number', 'symbol'].includes(typeof p),
        'D8: Piece elements must be value-=== comparable primitives');
      console.assert(p !== false,
        'D8: Piece elements must be disjoint from `false` (the sole occ() sentinel — mg stores Piece ids directly)');
    }

    // AxiomsInitialYX
    for (const p of Piece) {
      const iy = InitialY(p);
      const ix = InitialX(p);
      // String(p), not `${p}`: D8 permits Piece to be a symbol, and template-literal
      // interpolation throws on a Symbol (`Cannot convert a Symbol value to a
      // string`) rather than coercing it — String(p) is the one conversion that
      // safely handles all three permitted primitive types.
      console.assert(1 - PW <= iy && iy < HM, `AxiomsInitialYX: InitialY(${String(p)}) out of range`);
      console.assert(1 - PW <= ix && ix < WM, `AxiomsInitialYX: InitialX(${String(p)}) out of range`);
    }

    // AxiomsRotGrid
    for (const p of Piece) {
      for (let r = 0; r < 4; r++) {
        const gr = rotGrid(p, r);
        console.assert(gr.length === PW && gr.every(row => row.length === PW),
          `AxiomsRotGrid: rotGrid(${String(p)},${r}) must be ${PW}x${PW}`);
        let occupied = false;
        for (let y = 0; y < PW && !occupied; y++)
          for (let x = 0; x < PW && !occupied; x++)
            if (occ(gr[y][x])) occupied = true;
        console.assert(occupied, `AxiomsRotGrid: rotGrid(${String(p)},${r}) must have >=1 occupied cell`);
      }
      console.assert(
        fullyContainedIn(rotGrid(p, 0), InitialY(p), InitialX(p), ForbiddenGrid, FY, FX),
        `AxiomsRotGrid: spawn of ${String(p)} must be fully contained in the forbidden zone`);
    }

    // AxiomsInitialMainGrid
    console.assert(HM > 0, 'AxiomsInitialMainGrid: H InitialMainGrid must be > 0');
    console.assert(WM > 0, 'AxiomsInitialMainGrid: W InitialMainGrid must be > 0');
    console.assert(InitialMainGrid.every((_, y) => !isFullLineb(InitialMainGrid, y)),
      'AxiomsInitialMainGrid: no full line');

    // AxiomsForbiddenGrid
    console.assert(ForbiddenGrid.length > 0, 'AxiomsForbiddenGrid: H ForbiddenGrid must be > 0');
    console.assert(ForbiddenGrid[0].length > 0, 'AxiomsForbiddenGrid: W ForbiddenGrid must be > 0');
    console.assert(FY >= 0, 'AxiomsForbiddenGrid: FY >= 0');
    console.assert(FX >= 0, 'AxiomsForbiddenGrid: FX >= 0');
    console.assert(bboxInsideBBox(ForbiddenGrid, FY, FX, InitialMainGrid, 0, 0),
      'AxiomsForbiddenGrid: ForbiddenGrid bbox must lie within InitialMainGrid');

    // D10: integer-range headroom
    console.assert(Number.isInteger(MAX_SAFE_INTEGER), 'D10: MAX_SAFE_INTEGER must be an integer');
    console.assert(B <= MAX_SAFE_INTEGER, 'D10: B must be <= MAX_SAFE_INTEGER');
    const dims = [HM, WM, PW, FY, FX, ...Piece.flatMap(p => [InitialY(p), InitialX(p)])];
    console.assert(dims.every(v => Math.abs(v) <= MAX_SAFE_INTEGER),
      'D10: every integer parameter/dimension must be within MAX_SAFE_INTEGER');
  }

  function typeOK(s, isOccupied = (c => Piece.includes(c))) {
    return Array.isArray(s.mg) && s.mg.length === HM
      && s.mg.every(r => Array.isArray(r) && r.length === WM
                         && r.every(c => c === false || isOccupied(c)))
      && Number.isInteger(s.py) && Number.isInteger(s.px)
      && Number.isInteger(s.pr) && 0 <= s.pr && s.pr <= 3
      && typeof s.gameover === 'boolean'
      && Number.isInteger(s.clearedLines) && s.clearedLines >= 0
      && Piece.includes(s.p);
  }

  function checkInvariants(s, message, isOccupied = (c => Piece.includes(c))) {
    // TypeOK
    console.assert(typeOK(s, isOccupied), `typeOK failed @ ${message}`);
    // Gameover
    console.assert(s.gameover === intersect(ForbiddenGrid, FY, FX, s.mg, 0, 0),
      `Gameover invariant failed @ ${message}`);
    // PieceOccupiedInsideBounds (unconditional)
    console.assert(occupiedInside(rotGrid(s.p, s.pr), s.py, s.px, s.mg, 0, 0),
      `PieceOccupiedInsideBounds failed @ ${message}`);
    // PieceOnFreeBlocks (guarded by !gameover)
    console.assert(s.gameover || !intersect(rotGrid(s.p, s.pr), s.py, s.px, s.mg, 0, 0),
      `PieceOnFreeBlocks failed @ ${message}`);
    // NoFullLine
    console.assert(s.mg.every((_, y) => !isFullLineb(s.mg, y)),
      `NoFullLine failed @ ${message}`);
  }

  // ── Machine: encapsulates Rocq state ─────────────────────────
  class Machine {
    // spec: Init p
    constructor(p) {
      this.mg = copyGrid(InitialMainGrid);          // D1, N3 — never alias the constant
      this.p = p;
      this.py = InitialY(p);                        // req-piece-init
      this.px = InitialX(p);
      this.pr = 0;
      this.gameover = intersect(ForbiddenGrid, FY, FX, this.mg, 0, 0);
      this.clearedLines = 0;
      if (CHECK_INVARIANTS) checkInvariants(this, 'Init');
    }

    // spec: MovePiece dy dx
    movePiece(dy, dx) {
      const py2 = this.py + dy; // req-piece-move-def
      const px2 = this.px + dx; // req-piece-move-def
      if (!(!this.gameover && canMovePiece(dy, dx, this)))
        return false; // req-piece-move-dir
      this.py = py2;
      this.px = px2;
      if (CHECK_INVARIANTS) checkInvariants(this, 'movePiece');
      return true;
    }

    // spec: RotatePiece cw
    rotatePiece(cw) {
      const pr2 = mod(this.pr + (cw ? -1 : 1), 4); // D4
      if (!(!this.gameover && valid(this.mg, this.p, this.py, this.px, pr2)))
        return false; // req-piece-rot
      this.pr = pr2;
      if (CHECK_INVARIANTS) checkInvariants(this, 'rotatePiece');
      return true;
    }

    // spec: FixPiece p_new
    fixPiece(pNew) {
      if (!(!this.gameover && !canMovePiece(-1, 0, this)))
        return false; // real guard
      if (CHECK_INVARIANTS) console.assert(Piece.includes(pNew), 'pNew in Piece'); // D5
      // simultaneous-assignment order (skill §4b, proofs.md §9):
      const u = union(this.mg, 0, 0, rotGrid(this.p, this.pr), this.py, this.px); // 1: reads pre-state
      const cl = fullLineCount(u);                  // clearedLines on pre-clear grid
      const mg2 = clearFullLines(u);                 // req-grid-clear
      this.mg = mg2;
      this.p = pNew;                                  // 2
      this.py = InitialY(pNew);                       // 3: reads post-state p
      this.px = InitialX(pNew);                        // 3
      this.pr = 0;                                     // 4
      this.gameover = intersect(ForbiddenGrid, FY, FX, mg2, 0, 0); // 5: reads post-state mg // req-piece-fix-gameover
      this.clearedLines = cl;                           // 6
      if (CHECK_INVARIANTS) checkInvariants(this, 'fixPiece');
      return true;
    }

    // spec: FallStep p_new
    fallStep(pNew) {
      if (this.movePiece(-1, 0)) return true; // req-piece-fall
      return this.fixPiece(pNew);             // req-piece-fix
    }
  } // class Machine

  // Read-only view over a grid: no exposed array reference, only height/width
  // and a per-cell getter. snapshot() uses this for mg specifically — it's the
  // one field a read-only observer (view.js) could otherwise reach in and
  // mutate directly. Every other snapshot field is already a primitive/plain
  // value, immutable in the sense that matters (reassigning it doesn't affect
  // the live Machine either way).
  function wrapGrid(g) {
    return { height: g.length, width: g[0].length, cell: (y, x) => g[y][x] };
  }

  // spec: snapshot — read-only view for read-only observers
  function snapshot(machine) {
    return {
      mg: wrapGrid(machine.mg),
      p: machine.p,
      py: machine.py,
      px: machine.px,
      pr: machine.pr,
      gameover: machine.gameover,
      clearedLines: machine.clearedLines,
    };
  }

  return {
    // free functions (§5 order)
    occ,
    fullyContainedIn,
    bboxInsideBBox,
    isFullRow,
    isFullLineb,
    intersect,
    occupiedInside,
    rotGrid,
    valid,
    resize,
    clearFullLines,
    union,
    fullLineCount,
    newPieceState,
    newPieceYXState,
    canMovePiece,
    canRotatePiece,

    // helpers / invariant checkers
    checkAxioms,
    typeOK,
    checkInvariants,

    // machine
    Machine,
    snapshot,
  };
}
