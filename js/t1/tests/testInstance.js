// testInstance.js — a small, hand-verifiable instantiation of T1.v's parameters,
// used only by the test suites (§9). Deliberately tiny so that grids, pieces and
// rotation patterns can be reasoned about by inspection; distinct from the real
// game's instance.js.

export const PW = 2;
export const FY = 4;
export const FX = 0;

// Two primitive, value-=== comparable pieces (D8).
export const Piece = ['A', 'B'];

// 6x4 main grid, all-false (no full line — AxiomsInitialMainGrid).
export const InitialMainGrid = Array.from({ length: 6 }, () => Array(4).fill(false));

// 2x4 forbidden zone (rows 4,5), all-true.
export const ForbiddenGrid = Array.from({ length: 2 }, () => Array(4).fill(true));

// Both pieces spawn at the same (y,x): row 4 (= FY), col 1.
export function InitialY(_p) { return 4; }
export function InitialX(_p) { return 1; }

const F = false, TT = true;

// A: rotation-invariant full 2x2 block (like O).
const A_GRID = [[TT, TT], [TT, TT]];

// B: a single occupied cell, at a different corner per rotation — deliberately
// asymmetric so a 4x-rotation-returns-identity-of-occupied-set test is meaningful.
const B_GRIDS = [
  [[TT, F], [F, F]],  // r=0 — bottom-left
  [[F, TT], [F, F]],  // r=1 — bottom-right
  [[F, F], [F, TT]],  // r=2 — top-right
  [[F, F], [TT, F]],  // r=3 — top-left
];

export function RotGrid(p, r) {
  const rr = (0 <= r && r <= 3) ? r : 0;
  const g = p === 'A' ? A_GRID : B_GRIDS[rr];
  return g.map(row => row.map(c => c ? p : false));
}
