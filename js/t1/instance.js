// instance.js — concrete instantiation of T1.v's abstract parameters (§11, §13).
// Runtime input; not derived from T1.v, not consumed by codegen.

export const PW = 4;
export const FY = 20;
export const FX = 0;

export const Piece = ['I', 'O', 'T', 'S', 'Z', 'J', 'L'];

export const InitialMainGrid = Array.from({ length: 22 }, () => Array(10).fill(false));
export const ForbiddenGrid = Array.from({ length: 2 }, () => Array(10).fill(true));

export function InitialY(_p) { return 19; }
export function InitialX(_p) { return 3; }

// §13.4 — exact rotated piece grids (SRS-style). g[0] = bottom row, g[3] = top row.
// r counts counter-clockwise quarter-turns.
const F = false, TT = true;
const GRIDS = {
  I: [
    [[F, F, F, F], [F, F, F, F], [TT, TT, TT, TT], [F, F, F, F]],       // r=0
    [[F, TT, F, F], [F, TT, F, F], [F, TT, F, F], [F, TT, F, F]],       // r=1
    [[F, F, F, F], [TT, TT, TT, TT], [F, F, F, F], [F, F, F, F]],       // r=2
    [[F, F, TT, F], [F, F, TT, F], [F, F, TT, F], [F, F, TT, F]],       // r=3
  ],
  O: [
    [[F, F, F, F], [F, TT, TT, F], [F, TT, TT, F], [F, F, F, F]],
    [[F, F, F, F], [F, TT, TT, F], [F, TT, TT, F], [F, F, F, F]],
    [[F, F, F, F], [F, TT, TT, F], [F, TT, TT, F], [F, F, F, F]],
    [[F, F, F, F], [F, TT, TT, F], [F, TT, TT, F], [F, F, F, F]],
  ],
  T: [
    [[F, F, F, F], [TT, TT, TT, F], [F, TT, F, F], [F, F, F, F]],       // r=0
    [[F, TT, F, F], [TT, TT, F, F], [F, TT, F, F], [F, F, F, F]],       // r=1
    [[F, TT, F, F], [TT, TT, TT, F], [F, F, F, F], [F, F, F, F]],       // r=2
    [[F, TT, F, F], [F, TT, TT, F], [F, TT, F, F], [F, F, F, F]],       // r=3
  ],
  S: [
    [[F, F, F, F], [TT, TT, F, F], [F, TT, TT, F], [F, F, F, F]],       // r=0
    [[F, TT, F, F], [TT, TT, F, F], [TT, F, F, F], [F, F, F, F]],       // r=1
    [[TT, TT, F, F], [F, TT, TT, F], [F, F, F, F], [F, F, F, F]],       // r=2
    [[F, F, TT, F], [F, TT, TT, F], [F, TT, F, F], [F, F, F, F]],       // r=3
  ],
  Z: [
    [[F, F, F, F], [F, TT, TT, F], [TT, TT, F, F], [F, F, F, F]],       // r=0
    [[TT, F, F, F], [TT, TT, F, F], [F, TT, F, F], [F, F, F, F]],       // r=1
    [[F, TT, TT, F], [TT, TT, F, F], [F, F, F, F], [F, F, F, F]],       // r=2
    [[F, TT, F, F], [F, TT, TT, F], [F, F, TT, F], [F, F, F, F]],       // r=3
  ],
  L: [
    [[F, F, F, F], [TT, TT, TT, F], [F, F, TT, F], [F, F, F, F]],       // r=0
    [[F, TT, F, F], [F, TT, F, F], [TT, TT, F, F], [F, F, F, F]],       // r=1
    [[TT, F, F, F], [TT, TT, TT, F], [F, F, F, F], [F, F, F, F]],       // r=2
    [[F, TT, TT, F], [F, TT, F, F], [F, TT, F, F], [F, F, F, F]],       // r=3
  ],
  J: [
    [[F, F, F, F], [TT, TT, TT, F], [TT, F, F, F], [F, F, F, F]],       // r=0
    [[TT, TT, F, F], [F, TT, F, F], [F, TT, F, F], [F, F, F, F]],       // r=1
    [[F, F, TT, F], [TT, TT, TT, F], [F, F, F, F], [F, F, F, F]],       // r=2
    [[F, TT, F, F], [F, TT, F, F], [F, TT, TT, F], [F, F, F, F]],       // r=3
  ],
};

// Precomputed once: RotGrid is a pure function of (p, r) over a closed, finite
// domain (7 pieces x 4 rotations = 28 outputs) — every call otherwise
// reconstructed the same colorized array from scratch. Safe to share a single
// array instance per (p, r) across all callers: nothing anywhere ever writes
// to a rotGrid cell, only reads it (model.js's occupiedInside/intersect/union,
// view.js's rg[y][x] checks) — confirmed by direct inspection of every call site.
const ROT_GRID_CACHE = {};
for (const p of Object.keys(GRIDS)) {
  ROT_GRID_CACHE[p] = GRIDS[p].map(g => g.map(row => row.map(c => c === true ? p : false)));
}

export function RotGrid(p, r) {
  const rr = (0 <= r && r <= 3) ? r : 0; // defensive default; never called outside [0,3] under typeOK
  return ROT_GRID_CACHE[p][rr];
}

export const PieceColor = {
  I: '#83a598',
  O: '#fabd2f',
  T: '#d3869b',
  S: '#b8bb26',
  Z: '#fb4934',
  J: '#458588',
  L: '#fe8019',
};
