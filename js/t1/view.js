// view.js — renderer. Never imports from model.js or instance.js.
//
// Canonical home for the seven "core" drawing primitives shared by every
// layer (t1-t5, inherited unchanged into t6/t7 via t5): drawBlock,
// cellOrigin, drawGridLines, drawGrid, drawPiece, drawBackground,
// drawGameOver. Each reads `constants.PANEL_PX` defensively (`?? 0`), so the
// exact same implementation serves t1 (no side panel) through t5 (two side
// panels) without a per-layer fork. Later layers import these rather than
// redefining them (§ view.js unification).

export function render(canvas, constants, snapshot, pieceColor = {}) {
  const ctx = canvas.getContext('2d');
  const cellSize = Math.min(canvas.width / constants.WM, canvas.height / constants.HM);

  drawBackground(ctx, canvas, constants, cellSize);
  drawGrid(ctx, snapshot.mg, constants, cellSize, pieceColor);
  drawGridLines(ctx, constants, cellSize);
  drawPiece(ctx, snapshot, constants, cellSize, pieceColor);
  if (snapshot.gameover) drawGameOver(ctx, canvas, constants, cellSize);
}

export function cellOrigin(y, x, cellSize, HM, panelPx = 0) {
  return { cx: panelPx + x * cellSize, cy: (HM - 1 - y) * cellSize };
}

function panelPxOf(constants) {
  return constants.PANEL_PX ?? 0;
}

export function drawBackground(ctx, canvas, constants, cellSize) {
  ctx.fillStyle = '#111111';
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  const { FY, FX, FH, FW, HM } = constants;
  const { cx, cy } = cellOrigin(FY + FH - 1, FX, cellSize, HM, panelPxOf(constants));
  ctx.fillStyle = '#3A0000';
  ctx.fillRect(cx, cy, FW * cellSize, FH * cellSize);
}

export function drawGridLines(ctx, constants, cellSize) {
  const { HM, WM } = constants;
  const panelPx = panelPxOf(constants);
  ctx.strokeStyle = '#333333';
  ctx.beginPath();
  for (let x = 0; x <= WM; x++) {
    ctx.moveTo(panelPx + x * cellSize, 0);
    ctx.lineTo(panelPx + x * cellSize, HM * cellSize);
  }
  ctx.stroke();
  ctx.beginPath();
  for (let y = 0; y <= HM; y++) {
    ctx.moveTo(panelPx, y * cellSize);
    ctx.lineTo(panelPx + WM * cellSize, y * cellSize);
  }
  ctx.stroke();
}

export function drawBlock(ctx, cx, cy, cellSize, color) {
  ctx.fillStyle = color;
  ctx.fillRect(cx + 1, cy + 1, cellSize - 2, cellSize - 2);
}

export function drawGrid(ctx, mg, constants, cellSize, pieceColor = {}) {
  const { HM } = constants;
  const panelPx = panelPxOf(constants);
  for (let y = 0; y < mg.height; y++) {
    for (let x = 0; x < mg.width; x++) {
      const cell = mg.cell(y, x);
      if (cell === false) continue;
      const { cx, cy } = cellOrigin(y, x, cellSize, HM, panelPx);
      drawBlock(ctx, cx, cy, cellSize, pieceColor[cell] ?? '#888888');
    }
  }
}

export function drawPiece(ctx, snapshot, constants, cellSize, pieceColor = {}) {
  const { HM, WM, PW } = constants;
  const panelPx = panelPxOf(constants);
  const rg = constants.rotGrid(snapshot.p, snapshot.pr);
  const color = pieceColor[snapshot.p] ?? '#FFFFFF';
  for (let y = 0; y < PW; y++) {
    for (let x = 0; x < PW; x++) {
      if (rg[y][x] === false) continue;
      const gy = snapshot.py + y;
      const gx = snapshot.px + x;
      if (gy < 0 || gy >= HM || gx < 0 || gx >= WM) continue;
      const { cx, cy } = cellOrigin(gy, gx, cellSize, HM, panelPx);
      drawBlock(ctx, cx, cy, cellSize, color);
    }
  }
}

// Dims only the grid region — with a side panel on each side of the grid
// (t4+), dimming canvas.width - PANEL_PX would also dim the right panel. For
// t1/t2/t3 (no right panel, PANEL_PX undefined or left-only) this dims
// exactly the grid width, not the full canvas, in a letterboxed viewport.
export function drawGameOver(ctx, canvas, constants, cellSize) {
  const gridX = panelPxOf(constants);
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

  ctx.font = `${Math.floor(canvas.height * 0.03)}px sans-serif`;
  ctx.fillText('press any key to restart', centerX, canvas.height / 2 + cellSize, maxWidth);
}
