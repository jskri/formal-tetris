// view.js — renderer. Never imports from model.js or instance.js.

import {
  cellOrigin, drawBackground, drawGridLines, drawBlock, drawGrid, drawPiece, drawGameOver,
  labelGeometry, holdBoxGeometry, drawHoldBox, drawPanel, drawBanners,
  effectiveRowRange, previewGeometry, drawPreview,
} from '../t4/view.js';

export {
  cellOrigin, drawBackground, drawGridLines, drawBlock, drawGrid, drawPiece, drawGameOver,
  labelGeometry, holdBoxGeometry, drawHoldBox, drawPanel, drawBanners,
  effectiveRowRange, previewGeometry, drawPreview,
};

const GHOST_ALPHA = 0.25; // a starting value, not a measured-optimal one

export function render(canvas, constants, snapshot, pieceColor = {}, banners = null) {
  const ctx = canvas.getContext('2d');
  // gridAreaWidth is optional: when set, the grid draws within that width
  // instead of the full canvas (used by T7's mini-grid strip, which needs
  // room to the side of the main board). Every other caller leaves it unset,
  // so this is exactly canvas.width there.
  const gridAreaWidth = constants.gridAreaWidth ?? canvas.width;
  const cellSize = Math.min((gridAreaWidth - 2 * constants.PANEL_PX) / constants.WM, canvas.height / constants.HM);
  const holdGeom = holdBoxGeometry(constants, cellSize);
  const previewGeom = previewGeometry(constants, cellSize);

  drawBackground(ctx, canvas, constants, cellSize);
  drawHoldBox(ctx, constants, snapshot, holdGeom, pieceColor);
  drawPanel(ctx, constants, snapshot, holdGeom);
  drawBanners(ctx, constants, banners, holdGeom);
  drawPreview(ctx, constants, snapshot, previewGeom, pieceColor);
  drawGrid(ctx, snapshot.mg, constants, cellSize, pieceColor);
  drawGridLines(ctx, constants, cellSize);
  drawGhost(ctx, constants, snapshot, cellSize, pieceColor);
  drawPiece(ctx, snapshot, constants, cellSize, pieceColor);
  if (snapshot.gameover) drawGameOver(ctx, canvas, constants, cellSize);
  return cellSize; // available to callers that want it; not required by render()'s own contract
}

// Ghost/shadow piece: same shape and colour as the active piece, at (gy, px, pr)
// instead of (py, px, pr), drawn faint. Cells that fall outside the visible grid
// (gy can be negative, per T5's own shadowY) are simply skipped, same clipping
// drawPiece already does for the active piece.
export function drawGhost(ctx, constants, snapshot, cellSize, pieceColor) {
  const { HM, WM, PW, PANEL_PX } = constants;
  const rg = constants.rotGrid(snapshot.p, snapshot.pr);
  const color = pieceColor[snapshot.p] ?? '#FFFFFF';
  ctx.globalAlpha = GHOST_ALPHA;
  for (let y = 0; y < PW; y++) {
    for (let x = 0; x < PW; x++) {
      if (rg[y][x] === false) continue;
      const gridY = snapshot.gy + y;
      const gridX = snapshot.px + x;
      if (gridY < 0 || gridY >= HM || gridX < 0 || gridX >= WM) continue;
      const { cx, cy } = cellOrigin(gridY, gridX, cellSize, HM, PANEL_PX);
      drawBlock(ctx, cx, cy, cellSize, color);
    }
  }
  ctx.globalAlpha = 1;
}
