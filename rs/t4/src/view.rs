//! spec: view.rs — renderer (§14, `implementation.md`).
//!
//! Reads a `&Machine<P>` once per frame (D-Rust2, skill §3.1) and draws it
//! with macroquad's immediate-mode API; piece colors come from a caller
//! closure. Defines only the preview column and its geometry (§14.2-§14.5);
//! every other draw call reaches `t3::view`/`t2::view`'s own `pub` API
//! directly (§0.2, §7.1).

use crate::model::{Machine, Params};
use macroquad::prelude::*;
use std::collections::VecDeque;
use t2::view::Colored; // `draw_grid`'s bound, reached through `t2::view`.

// t1::view::RenderConstants, reused per §12 via t3::view's re-export.
pub use t3::view::RenderConstants;

/// spec: §14.1 (t2/implementation.md) — banner state, re-exported from
/// `t2::view` unchanged.
pub use t3::view::Banner;

/// spec: §14.2 (`implementation.md`) — grid/panel/hold-box geometry reuses
/// `t3::view::Layout` (`base`) unmodified; only the preview-column geometry
/// is new. `pub` fields (t5/implementation.md §0.2) for future embedding.
pub struct Layout {
    pub base: t3::view::Layout,
    pub right_origin: f32, // x where the preview column's content starts (before its own margin)
    pub preview_label_y: f32, // y where the "Next" text baseline sits
    pub preview_box_top: f32, // y where the first preview slot starts
    pub preview_cell_size: f32,
    pub preview_gap: f32,      // vertical gap between preview slots
    pub preview_box_size: f32, // slot height (uniform across every piece type)
    pub preview_count: usize,  // how many of NEXT_LEN entries actually fit
    pub max_row: i64,          // needed again in draw_preview's per-cell y transform
}

/// spec: §14.3 — union of occupied rows across every piece type at rotation
/// 0. Bound on `t1::model::Params` only (no `NEXT_LEN` needed).
fn effective_row_range<P: t1::model::Params>() -> (i64, i64) {
    let mut min_row = P::PW;
    let mut max_row = -1i64;
    for &p in P::piece_all() {
        let rg = P::rot_grid(p, 0);
        for (y, line) in rg.iter().enumerate().take(P::PW as usize) {
            for cell in line.iter().take(P::PW as usize) {
                if cell.is_some() {
                    min_row = min_row.min(y as i64);
                    max_row = max_row.max(y as i64);
                }
            }
        }
    }
    (min_row, max_row)
}

/// spec: §14.2 — right (preview) panel reuses the left panel's
/// `panel_width`; centering makes the right margin provably equal to
/// `origin_x`. `pub` (t5/implementation.md §0.2) — visibility only.
pub fn compute_layout<P: Params>(constants: &RenderConstants) -> Layout {
    let base = t3::view::compute_layout(constants);
    let (min_row, max_row) = effective_row_range::<P>();
    let effective_rows = (max_row - min_row + 1) as f32;
    let panel_width = base.base.panel_width;
    let m = t2::view::panel_metrics(panel_width);
    let cell_size = base.base.base.cell_size;

    let preview_cell_size = cell_size.min((panel_width - 2.0 * m.margin_x) / constants.pw as f32);
    let preview_gap = preview_cell_size;
    let preview_box_size = effective_rows * preview_cell_size;
    // Hold box draws in a full PW×PW box, so a piece's top edge sits
    // (PW-1-maxRow) cells below the box top; reproduce that offset here so
    // the top preview piece aligns with the held piece.
    let top_gap = (constants.pw as f32 - 1.0 - max_row as f32) * preview_cell_size;
    let preview_label_y = m.margin_y;
    let preview_box_top = m.margin_y + m.label_font as f32 + top_gap;

    let available_h =
        constants.hm as f32 * cell_size - m.margin_y - m.label_font as f32 - top_gap - m.margin_y;
    let per_slot = preview_box_size + preview_gap;
    let preview_count = (((available_h + preview_gap) / per_slot).floor().max(0.0) as usize)
        .min(P::NEXT_LEN as usize);
    // spec: §14.4 — silent truncation if preview_count < NEXT_LEN, matching
    // the hold box's clip/clamp precedent.

    let desired = t2::view::desired_panel_px();
    let gap = desired * t2::view::PANEL_GRID_GAP_FRACTION; // same fraction the left panel uses
    let right_origin = base.base.base.origin_x + constants.wm as f32 * cell_size + gap;

    Layout {
        base,
        right_origin,
        preview_label_y,
        preview_box_top,
        preview_cell_size,
        preview_gap,
        preview_box_size,
        preview_count,
        max_row,
    }
}

/// spec: req-preview-len/pop; §14.4 — borderless (unlike the hold box), and
/// uses a uniform slot height so `preview_count` doesn't jump frame-to-frame
/// based on which pieces are queued. `pub` (t5/implementation.md §0.2).
pub fn draw_preview<P: Params>(
    constants: &RenderConstants,
    layout: &Layout,
    next: &VecDeque<P::Piece>,
    piece_color: &impl Fn(P::Piece) -> [f32; 4],
    font: Option<&Font>,
) {
    let m = t2::view::panel_metrics(layout.base.base.panel_width);
    let x = layout.right_origin + m.margin_x;

    t2::view::draw_text_label(
        "Next",
        x,
        layout.preview_label_y,
        m.label_font,
        t2::view::LABEL_COLOR,
        font,
    );

    for (i, &p) in next.iter().take(layout.preview_count).enumerate() {
        let rg = P::rot_grid(p, 0); // always rotation 0, as the hold box
        let [r, g, b, a] = piece_color(p);
        let color = Color::new(r, g, b, a);
        let box_y =
            layout.preview_box_top + i as f32 * (layout.preview_box_size + layout.preview_gap);
        for (y, line) in rg.iter().enumerate().take(constants.pw as usize) {
            for (xx, cell) in line.iter().enumerate().take(constants.pw as usize) {
                if cell.is_none() {
                    continue; // exact-sentinel test (D1), not truthiness
                }
                let cx = x + xx as f32 * layout.preview_cell_size;
                let cy = box_y + (layout.max_row - y as i64) as f32 * layout.preview_cell_size;
                t2::view::draw_block(cx, cy, layout.preview_cell_size, color);
            }
        }
    }
}

/// spec: §14.1/§14.5 — public entry point. Call order: clear → hold box →
/// panel → banners → preview column → locked blocks → forbidden-zone tint →
/// grid lines → falling piece → game-over overlay. `font` is loaded once by
/// `main.rs` and passed in by reference every frame.
/// `layout.base.base.base` is `t1::view::Layout` (§14.5 — depth-4 nesting).
pub fn render<P: Params>(
    constants: &RenderConstants,
    machine: &Machine<P>,
    piece_color: impl Fn(P::Piece) -> [f32; 4],
    banner: Option<&Banner>,
    font: Option<&Font>,
) where
    P::Piece: Colored,
    P::CellExtra: Colored,
{
    let layout = compute_layout::<P>(constants);
    clear_background(t2::view::BG_COLOR);
    t3::view::draw_hold_box(constants, &layout.base, &machine.s3, &piece_color, font);
    let below_level_y = t2::view::draw_panel(
        &layout.base.base,
        &machine.s3.s2,
        layout.base.panel_top,
        font,
    );
    t2::view::draw_banners(&layout.base.base, below_level_y, banner, font);
    draw_preview::<P>(constants, &layout, &machine.next, &piece_color, font);
    t2::view::draw_grid(&machine.s3.s2.s1.mg, constants, &layout.base.base.base);
    t2::view::draw_background(constants, &layout.base.base.base);
    t2::view::draw_grid_lines(constants, &layout.base.base.base);
    t2::view::draw_piece(
        &machine.s3.s2,
        constants,
        &layout.base.base.base,
        &piece_color,
    );
    if machine.s3.s2.s1.gameover {
        t2::view::draw_game_over(constants, &layout.base.base, font);
    }
}
