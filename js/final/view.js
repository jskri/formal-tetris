// view.js — animation-only additions for final/. Never imports from model.js
// or instance.js (same rule as every other view.js in the tower).
//
// Reuses t5's exported primitives directly rather than t6's/t7's re-exports,
// since the clear-flash concerns the local player's own board, which is
// always t5-shaped (t6 adds no new fields/rendering; t7 wraps t6's render for
// its own board and layers a mini-strip/gauge on top — this file doesn't need
// to know about that layer at all).

import {
  cellOrigin, drawBackground, drawGridLines, drawGrid,
  holdBoxGeometry, drawHoldBox, drawPanel, drawBanners,
  previewGeometry, drawPreview,
} from '../t5/view.js';

// mgBeforeClear (from precomputeLock() in both controllers) is a plain 2D
// array — union() (t1/model.js) never wraps its output, only snapshot() does.
// drawGrid (t1/model.js) expects the read-only { height, width, cell(y,x) }
// accessor, so this file needs its own tiny wrapper — it can't import
// model.js's own wrapGrid (view.js never imports from model.js, same rule as
// every other view.js in the tower).
function wrapGrid(g) {
  return { height: g.length, width: g[0].length, cell: (y, x) => g[y][x] };
}

// Freezes the pre-clear frame (board + hold + panel + preview, no falling
// piece — it's already merged into `mgBeforeClear`) with the full rows fading
// to white. `progress` is a curve value from the controller's timer — 0
// (normal colors) through 1+ (a Tetris's pulse can briefly exceed 1; the fill
// alpha is clamped below regardless).
export function renderClearFlash(canvas, constants, snapshot, mgBeforeClear, rows, progress, pieceColor = {}) {
  const ctx = canvas.getContext('2d');
  const gridAreaWidth = constants.gridAreaWidth ?? canvas.width;
  const cellSize = Math.min((gridAreaWidth - 2 * constants.PANEL_PX) / constants.WM, canvas.height / constants.HM);
  const holdGeom = holdBoxGeometry(constants, cellSize);
  const previewGeom = previewGeometry(constants, cellSize);
  const panelPx = constants.PANEL_PX ?? 0;

  drawBackground(ctx, canvas, constants, cellSize);
  drawHoldBox(ctx, constants, snapshot, holdGeom, pieceColor);
  drawPanel(ctx, constants, snapshot, holdGeom);
  drawBanners(ctx, constants, null, holdGeom); // no banner during the flash itself
  drawPreview(ctx, constants, snapshot, previewGeom, pieceColor);
  drawGrid(ctx, wrapGrid(mgBeforeClear), constants, cellSize, pieceColor);
  drawGridLines(ctx, constants, cellSize);

  ctx.save();
  ctx.globalAlpha = Math.max(0, Math.min(1, progress));
  ctx.fillStyle = '#FFFFFF';
  for (const y of rows) {
    const { cx, cy } = cellOrigin(y, 0, cellSize, constants.HM, panelPx);
    ctx.fillRect(cx, cy + 1, constants.WM * cellSize, cellSize - 2);
  }
  ctx.restore();
}

// Garbage-arrival overlay: a quick, hard flash on the bottom `rowCount` rows
// (where materialized garbage just landed), drawn by the caller *after* its
// own normal render() for this frame — deliberately not a fade-in, just a
// short opaque flash that cuts off fast (`progress` 0→1 maps to alpha 1→0
// directly, no easing), matching "brutal, not graceful" for garbage.
export function drawGarbageFlash(canvas, constants, rowCount, progress) {
  if (rowCount <= 0) return;
  const ctx = canvas.getContext('2d');
  const gridAreaWidth = constants.gridAreaWidth ?? canvas.width;
  const cellSize = Math.min((gridAreaWidth - 2 * constants.PANEL_PX) / constants.WM, canvas.height / constants.HM);
  const panelPx = constants.PANEL_PX ?? 0;

  ctx.save();
  ctx.globalAlpha = Math.max(0, 1 - progress);
  ctx.fillStyle = '#FFD0D0';
  for (let y = 0; y < rowCount; y++) {
    const { cx, cy } = cellOrigin(y, 0, cellSize, constants.HM, panelPx);
    ctx.fillRect(cx, cy + 1, constants.WM * cellSize, cellSize - 2);
  }
  ctx.restore();
}

// Dim + "GAME OVER" heading only — deliberately omits the "press any key to
// restart" line the shared t1/view.js's drawGameOver draws. Used for a short
// window right after gameover, before the restart prompt/input both become
// active (a frantic last-second key mash shouldn't immediately restart the
// game). Not a parameter added to the shared drawGameOver: this timing is a
// final/-specific UX choice, not something t1-t6's own standalone pages
// should be forced to adopt, so it lives here instead of touching the tower.
export function drawGameOverPartial(canvas, constants, cellSize) {
  const ctx = canvas.getContext('2d');
  const gridX = constants.PANEL_PX ?? 0;
  const gridW = constants.WM * cellSize;
  ctx.fillStyle = 'rgba(0, 0, 0, 0.7)';
  ctx.fillRect(gridX, 0, gridW, canvas.height);

  const maxWidth = gridW * 0.9;
  const centerX = gridX + gridW / 2;
  ctx.fillStyle = '#FFFFFF';
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  ctx.font = `${Math.floor(canvas.height * 0.06)}px sans-serif`;
  ctx.fillText('GAME OVER', centerX, canvas.height / 2 - cellSize, maxWidth);
}
