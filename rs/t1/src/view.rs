//! spec: view.rs — renderer (§14, `implementation.md`).
//!
//! Pure rendering: reads `&Machine<P>` by reference, once per frame
//! (D-Rust2), and draws it with macroquad's immediate-mode API. Never
//! imports `instance.rs`. The falling piece's color comes from a caller
//! closure (`draw_piece`); a locked `mg` cell colors itself via `Colored`
//! instead (`draw_grid`), since it may hold a cell type a `P::Piece`-only
//! closure couldn't name.
//!
//! `Layout`, `compute_layout`, the grid-drawing helpers, and the `BG_COLOR`/
//! `GAME_OVER_*` constants are `pub` so other layers can reuse them on their
//! own `Machine<P>`/`Layout` instead of redefining a copy. `cell_origin`
//! stays private since callers only reach cells through the `pub`
//! procedures above; `draw_game_over` stays private since it's
//! T1-specific (fills the whole window with the built-in bitmap font,
//! unlike layers with a side panel).

use crate::model::{Machine, Params, PieceOrExtra};
use macroquad::prelude::*;

/// Per-cell color for whatever a `PieceOrExtra` variant holds. Named
/// `Colored` rather than `Color` since `macroquad::prelude::Color` already
/// claims that name in this module.
pub trait Colored {
    fn color(&self) -> [f32; 4];
}

/// `CellExtra = Infallible` for `T1.v`–`T6.v` (D1); this impl only makes
/// `draw_grid` type-check for those layers — the zero-arm `match` is a
/// compile-time proof it's never called.
impl Colored for std::convert::Infallible {
    fn color(&self) -> [f32; 4] {
        match *self {}
    }
}

/// spec: §14.1 — layout constants, extracted once in `main.rs`; read-only,
/// never written back to the engine.
pub struct RenderConstants {
    pub hm: i64,
    pub wm: i64,
    pub pw: i64,
    pub fy: i64,
    pub fx: i64,
    pub fh: i64,
    pub fw: i64,
}

pub const BG_COLOR: Color = Color::new(0.067, 0.067, 0.067, 1.00);
const FORBIDDEN_ZONE_COLOR: Color = Color::new(0.6, 0.1, 0.1, 0.35);
const GRID_LINE_COLOR: Color = Color::new(0.20, 0.20, 0.20, 1.0);
pub const GAME_OVER_TEXT_COLOR: Color = WHITE;
pub const GAME_OVER_BG_COLOR: Color = Color::new(0.0, 0.0, 0.0, 0.55);

/// spec: §14.2 — top/bottom margin, as a fraction of window height
/// (D-Grid-Centering). No horizontal counterpart: width uses the full
/// window.
const VERTICAL_MARGIN_FRACTION: f32 = 0.05;

/// spec: §14.2 — grid placement, recomputed every frame from the live
/// window; no cached dimensions, no resize handler (D-Grid-Centering).
/// `pub` fields so a wrapper layer's own `Layout` can embed one of these
/// as its base geometry.
pub struct Layout {
    pub cell_size: f32,
    pub origin_x: f32,
    pub origin_y: f32,
}

pub fn compute_layout(constants: &RenderConstants) -> Layout {
    let margin_y = screen_height() * VERTICAL_MARGIN_FRACTION;
    let usable_height = (screen_height() - 2.0 * margin_y).max(0.0);
    let cell_size = f32::min(
        screen_width() / constants.wm as f32,
        usable_height / constants.hm as f32,
    );
    let origin_x = (screen_width() - constants.wm as f32 * cell_size) / 2.0;
    let origin_y = margin_y + (usable_height - constants.hm as f32 * cell_size) / 2.0;
    Layout {
        cell_size,
        origin_x,
        origin_y,
    }
}

/// spec: §14.3 — coordinate transform: flips `y` to screen space (down =
/// larger pixel `y`) since the engine's `y` counts up from the bottom and
/// never flips it (D3).
fn cell_origin(y: i64, x: i64, hm: i64, layout: &Layout) -> (f32, f32) {
    (
        layout.origin_x + x as f32 * layout.cell_size,
        layout.origin_y + (hm - 1 - y) as f32 * layout.cell_size,
    )
}

pub fn draw_block(cx: f32, cy: f32, cell_size: f32, color: Color) {
    // small inset so adjacent blocks show a hairline seam
    let inset = (cell_size * 0.04).max(1.0);
    draw_rectangle(
        cx + inset,
        cy + inset,
        cell_size - 2.0 * inset,
        cell_size - 2.0 * inset,
        color,
    );
}

/// spec: §14.4 — forbidden-zone tint only; `main.rs`'s per-frame
/// `clear_background` call handles the whole-window clear.
pub fn draw_background(constants: &RenderConstants, layout: &Layout) {
    for dy in 0..constants.fh {
        for dx in 0..constants.fw {
            let (y, x) = (constants.fy + dy, constants.fx + dx);
            if y < 0 || y >= constants.hm || x < 0 || x >= constants.wm {
                continue;
            }
            let (cx, cy) = cell_origin(y, x, constants.hm, layout);
            draw_rectangle(
                cx,
                cy,
                layout.cell_size,
                layout.cell_size,
                FORBIDDEN_ZONE_COLOR,
            );
        }
    }
}

pub fn draw_grid_lines(constants: &RenderConstants, layout: &Layout) {
    let w = constants.wm as f32 * layout.cell_size;
    let h = constants.hm as f32 * layout.cell_size;
    for x in 0..=constants.wm {
        let px = layout.origin_x + x as f32 * layout.cell_size;
        draw_line(
            px,
            layout.origin_y,
            px,
            layout.origin_y + h,
            1.0,
            GRID_LINE_COLOR,
        );
    }
    for y in 0..=constants.hm {
        let py = layout.origin_y + y as f32 * layout.cell_size;
        draw_line(
            layout.origin_x,
            py,
            layout.origin_x + w,
            py,
            1.0,
            GRID_LINE_COLOR,
        );
    }
}

/// Locked blocks (`machine.mg`). Each cell colors itself via `Colored`
/// (covering both a real piece and, at a higher layer, a `CellExtra`
/// reservation per D1), so no closure parameter is needed here.
pub fn draw_grid<P: Params>(
    mg: &[Vec<Option<PieceOrExtra<P>>>],
    constants: &RenderConstants,
    layout: &Layout,
) where
    P::Piece: Colored,
    P::CellExtra: Colored,
{
    for (y, row) in mg.iter().enumerate() {
        for (x, cell) in row.iter().enumerate() {
            if let Some(cell) = cell {
                let [r, g, b, a] = match cell {
                    PieceOrExtra::Piece(p) => p.color(),
                    PieceOrExtra::Extra(e) => e.color(),
                };
                let (cx, cy) = cell_origin(y as i64, x as i64, constants.hm, layout);
                draw_block(cx, cy, layout.cell_size, Color::new(r, g, b, a));
            }
        }
    }
}

pub fn draw_piece<P: Params>(
    machine: &Machine<P>,
    constants: &RenderConstants,
    layout: &Layout,
    piece_color: &impl Fn(P::Piece) -> [f32; 4],
) {
    let pg = P::rot_grid(machine.p, machine.pr);
    let [r, g, b, a] = piece_color(machine.p);
    let color = Color::new(r, g, b, a);
    for dy in 0..constants.pw {
        for dx in 0..constants.pw {
            if pg[dy as usize][dx as usize].is_some() {
                let (y, x) = (machine.py + dy, machine.px + dx);
                if y < 0 || y >= constants.hm || x < 0 || x >= constants.wm {
                    continue; // may be partially outside the main grid's box
                }
                let (cx, cy) = cell_origin(y, x, constants.hm, layout);
                draw_block(cx, cy, layout.cell_size, color);
            }
        }
    }
}

fn draw_game_over(cell_size: f32) {
    let text = "GAME OVER";
    let font_size = (cell_size * 1.2).max(16.0);
    let dims = measure_text(text, None, font_size as u16, 1.0);
    let (w, h) = (screen_width(), screen_height());
    draw_rectangle(0.0, 0.0, w, h, GAME_OVER_BG_COLOR);
    draw_text(
        text,
        (w - dims.width) / 2.0,
        (h - dims.height) / 2.0 + dims.offset_y,
        font_size,
        GAME_OVER_TEXT_COLOR,
    );
}

/// spec: §14.1 — public entry point. Call order: locked blocks →
/// forbidden-zone tint → grid lines → falling piece → game-over overlay if
/// applicable (§14.4).
pub fn render<P: Params>(
    constants: &RenderConstants,
    machine: &Machine<P>,
    piece_color: impl Fn(P::Piece) -> [f32; 4],
) where
    P::Piece: Colored,
    P::CellExtra: Colored,
{
    let layout = compute_layout(constants);
    clear_background(BG_COLOR);
    draw_grid(&machine.mg, constants, &layout);
    draw_background(constants, &layout);
    draw_grid_lines(constants, &layout);
    draw_piece(machine, constants, &layout, &piece_color);
    if machine.gameover {
        draw_game_over(layout.cell_size);
    }
}
