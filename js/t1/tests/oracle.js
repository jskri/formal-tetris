// oracle.js — an independent, literal interpreter of T1.v. Grids are modeled as
// the Rocq record itself: a total function L : Z -> Z -> bool, plus HW (height,
// width) and YX (absolute origin) — and the operators GridUnion/GridIntersect/
// GridTranslate/GridInclude/Full/EmptyGrid are implemented exactly as T1.v defines
// them, over each grid's own absolute box, with no offsets threaded by hand.
//
// This is deliberately NOT model.js's encoding: model.js's fullyContainedIn/
// intersect/occupiedInside/union fuse the four idioms `⊆ Full`, `∩⊆∅`, `∪∩Full`,
// bare `⊆` into single bounds/content checks (implementation.md §4, proofs.md §3).
// That fusion is proved correct there, but a proof is not a substitute for an
// independently-encoded check: if the fusion argument itself were wrong, an oracle
// built the same way would share the bug. This file re-derives every quantity from
// the unfused algebra instead, so the two implementations have no shared blind spot.

import assert from 'node:assert/strict';

function mkGrid(L, H, W, Y = 0, X = 0) { return { L, H, W, Y, X }; }

const EmptyGrid = mkGrid(() => false, 0, 0, 0, 0);

function Full(g) { return mkGrid(() => true, g.H, g.W, g.Y, g.X); }

function inBox(g, y, x) {
  return g.Y <= y && y < g.Y + g.H && g.X <= x && x < g.X + g.W;
}

// fromArray(arr, y0, x0): the coercion ⟦arr, y0, x0⟧ from proofs.md §2 — a
// boolean[][] plus its Rocq origin, made total by gating on the box.
function fromArray(arr, y0 = 0, x0 = 0) {
  const H = arr.length, W = arr[0].length;
  return mkGrid(
    (y, x) => (y0 <= y && y < y0 + H && x0 <= x && x < x0 + W) ? arr[y - y0][x - x0] : false,
    H, W, y0, x0);
}

function materialize(g) {
  return Array.from({ length: g.H }, (_, i) =>
    Array.from({ length: g.W }, (_, j) => g.L(g.Y + i, g.X + j)));
}

// spec: GridUnion g1 g2
function gridUnion(g1, g2) {
  const minY = Math.min(g1.Y, g2.Y), minX = Math.min(g1.X, g2.X);
  const topMax = Math.max(g1.Y + g1.H, g2.Y + g2.H);
  const rightMax = Math.max(g1.X + g1.W, g2.X + g2.W);
  return mkGrid((y, x) => g1.L(y, x) || g2.L(y, x),
    topMax - minY, rightMax - minX, minY, minX);
}

// spec: GridIntersect g1 g2
function gridIntersect(g1, g2) {
  const maxY = Math.max(g1.Y, g2.Y), maxX = Math.max(g1.X, g2.X);
  const topMin = Math.min(g1.Y + g1.H, g2.Y + g2.H);
  const rightMin = Math.min(g1.X + g1.W, g2.X + g2.W);
  return mkGrid((y, x) => g1.L(y, x) && g2.L(y, x),
    topMin - maxY, rightMin - maxX, maxY, maxX);
}

// spec: GridTranslate g (dy, dx)
function gridTranslate(g, dy, dx) {
  return mkGrid((y, x) => g.L(y - dy, x - dx), g.H, g.W, g.Y + dy, g.X + dx);
}

// spec: GridInclude g1 g2 (⊆) — iterates g1's own absolute box, no manual offsets.
function subseteq(g1, g2) {
  for (let y = g1.Y; y < g1.Y + g1.H; y++) {
    for (let x = g1.X; x < g1.X + g1.W; x++) {
      if (g1.L(y, x) && !(inBox(g2, y, x) && g2.L(y, x))) return false;
    }
  }
  return true;
}

// spec: Valid g p pyx pr
function valid(g, p, py, px, pr, RotGrid) {
  const gp = gridTranslate(fromArray(RotGrid(p, pr)), py, px);
  return subseteq(gp, Full(g)) && subseteq(gridIntersect(gp, g), EmptyGrid);
}

function isFullLineb(g, y) {
  if (!(g.Y <= y && y < g.Y + g.H)) return true; // implb false _ = true
  for (let x = g.X; x < g.X + g.W; x++) if (!g.L(y, x)) return false;
  return true;
}

// Literal port of the Rocq Fixpoint FilterFullLines (fuel-based structural
// recursion). Note: the constructed grid's YX is always g's own YX — not (i, X g)
// — exactly as T1.v states it, even though i and y drift apart during recursion.
function filterFullLines(g, fuel, y, i) {
  if (fuel === 0) return mkGrid(() => false, 0, g.W, g.Y, g.X);
  if (isFullLineb(g, y)) return filterFullLines(g, fuel - 1, y + 1, i);
  const g2 = filterFullLines(g, fuel - 1, y + 1, i + 1);
  return mkGrid((y1, x) => (y1 === i ? g.L(y, x) : g2.L(y1, x)), 1 + g2.H, g.W, g.Y, g.X);
}

// spec: Resize g newGh fillValue
function resize(g, newGh, fillValue) {
  return mkGrid((y, x) => (y < g.Y + g.H ? g.L(y, x) : fillValue(x)), newGh, g.W, g.Y, g.X);
}

// spec: ClearFullLines g
function clearFullLines(g) {
  const g2 = filterFullLines(g, g.H, g.Y, g.Y);
  return resize(g2, g.H, () => false);
}

function fullLineCount(g) {
  let count = 0;
  for (let y = g.Y; y < g.Y + g.H; y++) if (isFullLineb(g, y)) count++;
  return count;
}

// ── State-level transitions (spec: MovePiece, RotatePiece, FixPiece, FallStep) ──

function canMovePiece(dy, dx, s, params) {
  const dirOK = (dy === 0 && dx === -1) || (dy === 0 && dx === 1) || (dy === -1 && dx === 0);
  return dirOK && valid(s.mg, s.p, s.py + dy, s.px + dx, s.pr, params.RotGrid);
}

function movePiece(dy, dx, s, params) {
  if (s.gameover || !canMovePiece(dy, dx, s, params)) return null;
  return { ...s, py: s.py + dy, px: s.px + dx };
}

function rotatePiece(cw, s, params) {
  const pr2 = ((s.pr + (cw ? -1 : 1)) % 4 + 4) % 4;
  if (s.gameover || !valid(s.mg, s.p, s.py, s.px, pr2, params.RotGrid)) return null;
  return { ...s, pr: pr2 };
}

function fixPiece(pNew, s, params) {
  if (s.gameover || canMovePiece(-1, 0, s, params)) return null;
  const rg = fromArray(params.RotGrid(s.p, s.pr));
  const u = gridIntersect(gridUnion(s.mg, gridTranslate(rg, s.py, s.px)), Full(s.mg));
  const mg2 = clearFullLines(u);
  return {
    mg: mg2,
    p: pNew,
    py: params.InitialY(pNew),
    px: params.InitialX(pNew),
    pr: 0,
    gameover: !subseteq(gridIntersect(params.ForbiddenGrid, mg2), EmptyGrid),
    clearedLines: fullLineCount(u),
  };
}

function fallStep(pNew, s, params) {
  return movePiece(-1, 0, s, params) ?? fixPiece(pNew, s, params);
}

function initState(p, params) {
  return {
    mg: params.InitialMainGrid,
    p,
    py: params.InitialY(p),
    px: params.InitialX(p),
    pr: 0,
    gameover: !subseteq(gridIntersect(params.ForbiddenGrid, params.InitialMainGrid), EmptyGrid),
    clearedLines: 0,
  };
}

function snapshotOf(s) {
  return {
    mg: materialize(s.mg),
    p: s.p, py: s.py, px: s.px, pr: s.pr, gameover: s.gameover, clearedLines: s.clearedLines,
  };
}

// makeParams: wraps array-based instance params (as in instance.js/testInstance.js)
// into the Grid-record form this oracle uses internally. ForbiddenGrid carries its
// Rocq origin (FY, FX); InitialMainGrid and every RotGrid(p,r) are origin (0,0).
function makeParams({ Piece, InitialMainGrid, ForbiddenGrid, RotGrid, InitialY, InitialX, FY, FX }) {
  return {
    Piece,
    InitialMainGrid: fromArray(InitialMainGrid, 0, 0),
    ForbiddenGrid: fromArray(ForbiddenGrid, FY, FX),
    RotGrid, InitialY, InitialX,
  };
}

export const oracle = {
  makeParams,
  initState,
  movePiece,
  rotatePiece,
  fixPiece,
  fallStep,
  snapshotOf,

  mkGrid,
  EmptyGrid,
  Full,
  inBox,
  fromArray,
  gridUnion,
  gridIntersect,
  gridTranslate,
  subseteq,
};

// model.js's snapshot() wraps mg as a read-only { height, width, cell(y,x) }
// accessor (D1, t1/model.js); this oracle's own mg stays a plain nested array
// (it faithfully models T1.v's genuinely bool-valued Grid.L). gridsEqual must
// accept either shape on either side, not just two wrapped grids — and must
// compare *occupancy* (occ), not raw cell values: the model's cells legitimately
// carry a Piece id where the oracle's carry a bare `true`, and the two are only
// ever supposed to agree on whether a cell is occupied, never on which exact
// value occupies it.
function gridDims(g) {
  return Array.isArray(g) ? { height: g.length, width: g[0].length } : { height: g.height, width: g.width };
}
function gridCell(g, y, x) {
  return Array.isArray(g) ? g[y][x] : g.cell(y, x);
}
function occ(c) { return c !== false; }

export function gridsEqual(g1, g2) {
  const d1 = gridDims(g1);
  const d2 = gridDims(g2);
  if (d1.height !== d2.height || d1.width !== d2.width) return false;
  for (let y = 0; y < d1.height; y++) {
    for (let x = 0; x < d1.width; x++) {
      if (occ(gridCell(g1, y, x)) !== occ(gridCell(g2, y, x))) return false;
    }
  }
  return true;
}

export function assertSnapshotsEqual(s1, s2, message) {
  const { mg: mg1, ...rest1 } = s1;
  const { mg: mg2, ...rest2 } = s2;
  assert.deepStrictEqual(rest1, rest2, message);
  assert.ok(gridsEqual(mg1, mg2), message ?? 'mg mismatch');
}
