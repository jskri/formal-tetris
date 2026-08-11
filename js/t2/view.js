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

  drawBackground(ctx, canvas, constants, cellSize);
  drawPanel(ctx, constants, snapshot, cellSize);
  drawBanners(ctx, constants, banners, cellSize);
  drawGrid(ctx, snapshot.mg, constants, cellSize, pieceColor);
  drawGridLines(ctx, constants, cellSize);
  drawPiece(ctx, snapshot, constants, cellSize, pieceColor);
  if (snapshot.gameover) drawGameOver(ctx, canvas, constants, cellSize);
}

function panelMetrics(constants) {
  const { PANEL_PX } = constants;
  const margin = PANEL_PX * 0.12;
  const labelFont = Math.max(10, Math.floor(PANEL_PX * 0.11));
  const valueFont = Math.max(12, Math.floor(PANEL_PX * 0.17));
  const bannerFont = Math.max(10, Math.floor(PANEL_PX * 0.10));
  return { margin, labelFont, valueFont, bannerFont };
}

export function drawPanel(ctx, constants, snapshot, cellSize) {
  const { PANEL_PX } = constants;
  ctx.fillStyle = '#111111';
  ctx.fillRect(0, 0, PANEL_PX, ctx.canvas.height);

  const { margin, labelFont, valueFont } = panelMetrics(constants);

  ctx.textAlign = 'left';
  ctx.textBaseline = 'top';
  ctx.fillStyle = '#AAAAAA';

  let y = margin;
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

export function drawBanners(ctx, constants, banners, cellSize) {
  const { margin, labelFont, valueFont, bannerFont } = panelMetrics(constants);
  const slotHeight = bannerFont * 1.4;

  // below the LEVEL block: margin + label + value(x2 blocks) — mirrors drawPanel's layout.
  let y = margin + labelFont * 1.2 + valueFont * 1.4 + labelFont * 1.2 + valueFont * 1.4;

  ctx.textAlign = 'left';
  ctx.textBaseline = 'top';
  ctx.font = `${bannerFont}px sans-serif`;

  const visibleCombo = banners ? banners.combo - 1 : 0;
  if (banners && visibleCombo > 0) {
    ctx.fillStyle = '#FFD000';
    ctx.fillText(`${visibleCombo}-hit combo!`, margin, y);
  }
  y += slotHeight; // reserved even when the combo line is empty

  if (banners && banners.perfectClear) {
    ctx.fillStyle = '#00E0FF';
    ctx.fillText('Perfect clear!', margin, y);
  }
}
