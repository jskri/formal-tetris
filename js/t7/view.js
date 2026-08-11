// view.js — renderer. Never imports from model.js or instance.js.
// Wraps t6/view.js's render (itself a re-export of t5/view.js) rather than
// duplicating it: the main grid, hold box, preview, panels, ghost, and
// gameover overlay are exactly T6's own, drawn into `constants.gridAreaWidth`
// of the canvas. Everything from `gridAreaWidth` to `canvas.width` is this
// file's own: the mini-grid strip and the garbage gauge.

import { render as renderT6 } from '../t6/view.js';

const MINI_GAP = 4;
const GARBAGE_GAUGE_FRAC = 1 / 3; // relative to cellSize — a starting value, not measured-optimal

export function render(canvas, constants, snapshot, pieceColor = {}, banners = null, opponents = [], target = null) {
  const ctx = canvas.getContext('2d');
  const cellSize = renderT6(canvas, constants, snapshot, pieceColor, banners);

  drawGarbageGauge(ctx, constants, snapshot, cellSize);
  drawMiniStrip(ctx, canvas, constants, opponents, pieceColor, cellSize, target);
}

// ── Garbage gauge (§14.3): vertical bar flush against the playfield's left
// edge, growing bottom-up, one cellSize-height segment per pending line,
// clamped at HM. Single flat color — materialization is unconditional at the
// next fix, not timer-driven, so there is no "urgency" to color-code.
function drawGarbageGauge(ctx, constants, snapshot, cellSize) {
  const { PANEL_PX, HM } = constants;
  const amount = Math.min(snapshot.garbage ?? 0, HM); // T6 (filler) snapshots have no
  if (amount <= 0) return;                            // `garbage` field — ?? 0 hides it there
  const gaugeW = cellSize * GARBAGE_GAUGE_FRAC;
  const gh = amount * cellSize;
  ctx.fillStyle = '#B8860B';
  ctx.fillRect(PANEL_PX - gaugeW, HM * cellSize - gh, gaugeW, gh);
}

// ── Mini-grid strip (§14.2): fixed-size region reserved regardless of
// PlayerCount (controller.js's sizeCanvas allocates it); tiles opponents in
// rows × columns, individual mini cell size chosen to maximize itself within
// that fixed region — more opponents shrink each mini, never grow the strip.
function drawMiniStrip(ctx, canvas, constants, opponents, pieceColor, mainCellSize, target) {
  const stripX = constants.gridAreaWidth ?? canvas.width;
  const stripW = canvas.width - stripX;
  const stripH = canvas.height;
  const n = opponents.length;
  if (n === 0 || stripW <= 0) return;

  const labelFont = Math.max(8, Math.floor(mainCellSize * 0.5));
  const labelH = labelFont * 1.3;

  const { cols, cellSize } = bestTiling(n, stripW, stripH, constants.WM, constants.HM, labelH, MINI_GAP);
  if (cellSize <= 0) return;

  const miniW = constants.WM * cellSize;
  const miniH = constants.HM * cellSize;

  ctx.font = `${labelFont}px sans-serif`;
  ctx.textAlign = 'left';
  ctx.textBaseline = 'top';

  for (let i = 0; i < n; i++) {
    const col = i % cols;
    const row = Math.floor(i / cols);
    const ox = stripX + MINI_GAP + col * (miniW + MINI_GAP);
    const oy = MINI_GAP + row * (miniH + labelH + MINI_GAP);
    // Only meaningful with more than one opponent (PlayerCount > 2): with
    // exactly one, the target is unambiguous and a border would be redundant.
    const isTarget = opponents.length > 1 && target != null && opponents[i].playerIndex === target;
    drawMini(ctx, constants, opponents[i], ox, oy, cellSize, miniW, miniH, labelH, pieceColor, isTarget);
  }
}

// Tries every column count from 1 to n, picks whichever maximizes the
// resulting mini cellSize — the only thing that varies is how stripW/stripH
// get divided among rows/cols.
function bestTiling(n, stripW, stripH, WM, HM, labelH, gap) {
  let best = { cols: 1, cellSize: 0 };
  for (let cols = 1; cols <= n; cols++) {
    const rows = Math.ceil(n / cols);
    const availW = (stripW - (cols + 1) * gap) / cols;
    const availH = (stripH - (rows + 1) * gap - rows * labelH) / rows;
    if (availW <= 0 || availH <= 0) continue;
    const cellSize = Math.min(availW / WM, availH / HM);
    if (cellSize > best.cellSize) best = { cols, cellSize };
  }
  return best;
}

// One mini-grid: greyed placeholder before the first STATE / once
// disconnected; otherwise block colors + current piece, forbidden-zone tint
// kept, no grid lines, no ghost/next/hold (§14.2). The current target's
// border is red instead of grey and slightly thicker, when it's actually
// ambiguous which opponent that is (drawMiniStrip only sets isTarget with
// more than one opponent) — with exactly one opponent the target can only
// ever be them, so no border is drawn.
function drawMini(ctx, constants, opp, ox, oy, cellSize, miniW, miniH, labelH, pieceColor, isTarget) {
  ctx.fillStyle = '#AAAAAA';
  ctx.fillText(opp.name, ox, oy);

  const gy0 = oy + labelH;
  const dead = opp.gameover || opp.connected === false;
  const borderColor = isTarget ? '#FF0000' : '#444444';
  const borderWidth = isTarget ? 3 : 1;

  if (!opp.mg) {
    ctx.fillStyle = '#222222';
    ctx.fillRect(ox, gy0, miniW, miniH);
    ctx.strokeStyle = borderColor;
    ctx.lineWidth = borderWidth;
    ctx.strokeRect(ox + 0.5, gy0 + 0.5, miniW - 1, miniH - 1);
    ctx.lineWidth = 1;
    return;
  }

  const { FY, FX, FH, FW, HM, WM } = constants;
  const fx = ox + FX * cellSize;
  const fy = gy0 + (HM - FY - FH) * cellSize;
  ctx.fillStyle = dead ? '#1A0000' : '#3A0000';
  ctx.fillRect(fx, fy, FW * cellSize, FH * cellSize);

  const blockColor = dead ? '#555555' : null; // null: color looked up per-cell below
  for (let y = 0; y < opp.mg.length; y++) {
    for (let x = 0; x < opp.mg[0].length; x++) {
      const cell = opp.mg[y][x];
      if (cell === false) continue;
      const cx = ox + x * cellSize;
      const cy = gy0 + (HM - 1 - y) * cellSize;
      ctx.fillStyle = blockColor ?? pieceColor[cell] ?? '#888888';
      ctx.fillRect(cx + 0.5, cy + 0.5, cellSize - 1, cellSize - 1);
    }
  }

  if (!dead && opp.p != null) {
    const rg = constants.rotGrid(opp.p, opp.pr);
    const color = pieceColor[opp.p] ?? '#FFFFFF';
    for (let y = 0; y < constants.PW; y++) {
      for (let x = 0; x < constants.PW; x++) {
        if (rg[y][x] === false) continue;
        const gy = opp.py + y;
        const gx = opp.px + x;
        if (gy < 0 || gy >= HM || gx < 0 || gx >= WM) continue;
        const cx = ox + gx * cellSize;
        const cy = gy0 + (HM - 1 - gy) * cellSize;
        ctx.fillStyle = color;
        ctx.fillRect(cx + 0.5, cy + 0.5, cellSize - 1, cellSize - 1);
      }
    }
  }

  ctx.strokeStyle = borderColor;
  ctx.lineWidth = borderWidth;
  ctx.strokeRect(ox + 0.5, gy0 + 0.5, miniW - 1, miniH - 1);
  ctx.lineWidth = 1;
}
