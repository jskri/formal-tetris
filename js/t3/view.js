// view.js — renderer. Never imports from model.js or instance.js.

import {
  cellOrigin, drawBackground, drawGridLines, drawBlock, drawGrid, drawPiece, drawGameOver,
} from '../t1/view.js';

export {
  cellOrigin, drawBackground, drawGridLines, drawBlock, drawGrid, drawPiece, drawGameOver,
};

export function render(canvas, constants, snapshot, pieceColor = {}, banners = null) {
  const ctx = canvas.getContext('2d');
  const cellSize = Math.min((canvas.width - constants.PANEL_PX) / constants.WM, canvas.height / constants.HM);
  const geom = holdBoxGeometry(constants, cellSize);

  drawBackground(ctx, canvas, constants, cellSize);
  drawHoldBox(ctx, constants, snapshot, geom, pieceColor);
  drawPanel(ctx, constants, snapshot, geom);
  drawBanners(ctx, constants, banners, geom);
  drawGrid(ctx, snapshot.mg, constants, cellSize, pieceColor);
  drawGridLines(ctx, constants, cellSize);
  drawPiece(ctx, snapshot, constants, cellSize, pieceColor);
  if (snapshot.gameover) drawGameOver(ctx, canvas, constants, cellSize);
}

// Shared label geometry — the "Hold" label uses this convention.
export function labelGeometry(constants) {
  const margin = constants.PANEL_PX * 0.08;
  const labelFont = Math.max(10, Math.floor(constants.PANEL_PX * 0.11));
  return { margin, labelFont, labelHeight: labelFont * 1.2 };
}

// Hold-box geometry, computed once and shared across drawHoldBox/drawPanel/
// drawBanners (implementation.md §14.2) so the panel's vertical layout can't
// drift between the three functions that depend on it — including every font
// size any of the three needs, so none of them ever recomputes one independently.
// Label-aware: reserves labelHeight above the box for the "Hold" caption.
export function holdBoxGeometry(constants, cellSize) {
  const { margin, labelFont, labelHeight } = labelGeometry(constants);
  const valueFont = Math.max(12, Math.floor(constants.PANEL_PX * 0.17));
  const bannerFont = Math.max(10, Math.floor(constants.PANEL_PX * 0.10));
  const hbSize = Math.min(constants.PW * cellSize, constants.PANEL_PX - 2 * margin);
  const labelY = margin;
  const boxY = labelY + labelHeight;
  const panelTopY = boxY + hbSize + margin; // shared with drawPanel/drawBanners
  return { margin, labelFont, valueFont, bannerFont, labelY, hbSize,
           hbCellSize: hbSize / constants.PW, boxY, panelTopY };
}

// Hold box (HB): top of the panel, at the same per-cell scale as the main grid
// (clamped to the panel width — implementation.md §14.2's flagged deviation).
// Draws a "Hold" caption above the box.
export function drawHoldBox(ctx, constants, snapshot, geom, pieceColor) {
  const { margin, hbSize, hbCellSize, labelY, labelFont, boxY } = geom;
  const dim = snapshot.swapped;

  ctx.fillStyle = '#AAAAAA';
  ctx.textAlign = 'left'; ctx.textBaseline = 'top';
  ctx.font = `${labelFont}px sans-serif`;
  ctx.fillText('Hold', margin, labelY);

  if (dim) ctx.globalAlpha = 0.4;
  ctx.strokeStyle = '#555555';
  ctx.strokeRect(margin + 0.5, boxY + 0.5, hbSize - 1, hbSize - 1);

  if (snapshot.hold !== null) {
    const rg = constants.rotGrid(snapshot.hold, 0); // always rotation 0 in the HB
    const color = pieceColor[snapshot.hold] ?? '#FFFFFF';
    for (let y = 0; y < constants.PW; y++) {
      for (let x = 0; x < constants.PW; x++) {
        if (rg[y][x] === false) continue;
        const cx = margin + x * hbCellSize;
        const cy = boxY + (constants.PW - 1 - y) * hbCellSize; // same bottom-up flip as drawPiece
        drawBlock(ctx, cx, cy, hbCellSize, color);
      }
    }
  }
  if (dim) ctx.globalAlpha = 1;
}

export function drawPanel(ctx, constants, snapshot, geom) {
  const { margin, labelFont, valueFont, panelTopY } = geom;

  ctx.textAlign = 'left';
  ctx.textBaseline = 'top';
  ctx.fillStyle = '#AAAAAA';

  let y = panelTopY;
  ctx.font = `${labelFont}px sans-serif`;
  ctx.fillText('SCORE', margin, y);
  y += labelFont * 1.2;
  ctx.fillStyle = '#FFFFFF';
  ctx.font = `${valueFont}px sans-serif`;
  ctx.fillText(String(snapshot.score), margin, y);
  y += valueFont * 1.4;

  ctx.fillStyle = '#AAAAAA';
  ctx.font = `${labelFont}px sans-serif`;
  ctx.fillText('LEVEL', margin, y);
  y += labelFont * 1.2;
  ctx.fillStyle = '#FFFFFF';
  ctx.font = `${valueFont}px sans-serif`;
  ctx.fillText(String(snapshot.level), margin, y);
}

export function drawBanners(ctx, constants, banners, geom) {
  const { margin, labelFont, valueFont, bannerFont, panelTopY } = geom;
  const slotHeight = bannerFont * 1.4;

  let y = panelTopY + labelFont * 1.2 + valueFont * 1.4 + labelFont * 1.2 + valueFont * 1.4;

  ctx.textAlign = 'left';
  ctx.textBaseline = 'top';
  ctx.font = `${bannerFont}px sans-serif`;

  const visibleCombo = banners ? banners.combo - 1 : 0;
  if (banners && visibleCombo > 0) {
    ctx.fillStyle = '#FFD000';
    ctx.fillText(`${visibleCombo}-hit combo!`, margin, y);
  }
  y += slotHeight;

  if (banners && banners.perfectClear) {
    ctx.fillStyle = '#00E0FF';
    ctx.fillText('Perfect clear!', margin, y);
  }
}
