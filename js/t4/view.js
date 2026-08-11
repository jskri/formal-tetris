// view.js — renderer. Never imports from model.js or instance.js.

import {
  cellOrigin, drawBackground, drawGridLines, drawBlock, drawGrid, drawPiece, drawGameOver,
} from '../t1/view.js';
import {
  labelGeometry, holdBoxGeometry, drawHoldBox, drawPanel, drawBanners,
} from '../t3/view.js';

export {
  cellOrigin, drawBackground, drawGridLines, drawBlock, drawGrid, drawPiece, drawGameOver,
  labelGeometry, holdBoxGeometry, drawHoldBox, drawPanel, drawBanners,
};

export function render(canvas, constants, snapshot, pieceColor = {}, banners = null) {
  const ctx = canvas.getContext('2d');
  const cellSize = Math.min((canvas.width - 2 * constants.PANEL_PX) / constants.WM, canvas.height / constants.HM);
  const holdGeom = holdBoxGeometry(constants, cellSize);
  const previewGeom = previewGeometry(constants, cellSize);

  drawBackground(ctx, canvas, constants, cellSize);
  drawHoldBox(ctx, constants, snapshot, holdGeom, pieceColor);
  drawPanel(ctx, constants, snapshot, holdGeom);
  drawBanners(ctx, constants, banners, holdGeom);
  drawPreview(ctx, constants, snapshot, previewGeom, pieceColor);
  drawGrid(ctx, snapshot.mg, constants, cellSize, pieceColor);
  drawGridLines(ctx, constants, cellSize);
  drawPiece(ctx, snapshot, constants, cellSize, pieceColor);
  if (snapshot.gameover) drawGameOver(ctx, canvas, constants, cellSize);
}

// Union of occupied rows across every piece type at rotation 0 — used to size
// preview slots by actual content instead of the full PW×PW bounding box.
// Generic: derived from Piece/rotGrid, not hardcoded to any particular tetromino
// set, so it holds for any future instantiation. AxiomsRotGrid (t1/model.js)
// guarantees every piece has >=1 occupied cell at every rotation, so minRow/maxRow
// are always well-defined here.
export function effectiveRowRange(constants) {
  let minRow = constants.PW, maxRow = -1;
  for (const p of constants.Piece) {
    const rg = constants.rotGrid(p, 0);
    for (let y = 0; y < constants.PW; y++) {
      for (let x = 0; x < constants.PW; x++) {
        if (rg[y][x] !== false) {
          if (y < minRow) minRow = y;
          if (y > maxRow) maxRow = y;
        }
      }
    }
  }
  return { minRow, maxRow };
}

// Preview-column geometry (right panel): borderless, one-cell gap, capped to fit,
// aligned so the top preview piece's top edge matches the held piece's top edge.
// Uses its own clamped cell size (like holdBoxGeometry's hbCellSize), not the raw
// grid cellSize — otherwise a piece up to PW cells wide can exceed PANEL_PX and
// bleed past the panel's own boundary.
export function previewGeometry(constants, cellSize) {
  const { margin, labelFont, labelHeight } = labelGeometry(constants);
  const { minRow, maxRow } = effectiveRowRange(constants);
  const effectiveRows = maxRow - minRow + 1;
  const previewCellSize = Math.min(cellSize, (constants.PANEL_PX - 2 * margin) / constants.PW);
  const gap = previewCellSize;
  const boxSize = effectiveRows * previewCellSize;
  const topGap = (constants.PW - 1 - maxRow) * previewCellSize;
  const boxTop = margin + labelHeight + topGap;
  const availableH = constants.HM * cellSize - margin - labelHeight - topGap - margin;
  const perSlot = boxSize + gap;
  const count = Math.max(0, Math.min(constants.NextLen, Math.floor((availableH + gap) / perSlot)));
  const rightOrigin = constants.PANEL_PX + constants.WM * cellSize;
  return {
    margin, labelFont, labelY: margin, boxTop, boxSize,
    cellSize: previewCellSize, gap, count, rightOrigin, minRow, maxRow,
  };
}

// Preview column (right panel): "Next" label + a capped stack of borderless boxes.
// No background fill here — drawBackground already covers both side panels once.
export function drawPreview(ctx, constants, snapshot, geom, pieceColor) {
  const { rightOrigin, cellSize, maxRow } = geom;
  ctx.fillStyle = '#AAAAAA';
  ctx.textAlign = 'left'; ctx.textBaseline = 'top';
  ctx.font = `${geom.labelFont}px sans-serif`;
  ctx.fillText('Next', rightOrigin + geom.margin, geom.labelY);

  for (let i = 0; i < geom.count; i++) {
    const p = snapshot.next[i];
    const rg = constants.rotGrid(p, 0); // always rotation 0, as the hold box
    const color = pieceColor[p] ?? '#FFFFFF';
    const boxY = geom.boxTop + i * (geom.boxSize + geom.gap);
    for (let y = 0; y < constants.PW; y++) {
      for (let x = 0; x < constants.PW; x++) {
        if (rg[y][x] === false) continue;
        const cx = rightOrigin + geom.margin + x * cellSize;
        // maxRow (not PW-1) is the top of the *effective* slot — every piece's
        // occupied rows fall within [minRow, maxRow] by construction of
        // effectiveRowRange, so this never goes negative.
        const cy = boxY + (maxRow - y) * cellSize;
        drawBlock(ctx, cx, cy, cellSize, color);
      }
    }
  }
}
