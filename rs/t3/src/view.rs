//! spec: view.rs — renderer (§14, `implementation.md`).
//!
//! Pure rendering: reads a `&Machine<P>` once per frame (D-Rust2) and draws
//! it with macroquad's immediate-mode API. Piece-color mapping is supplied
//! by the caller as a closure, as in `t1::view`/`t2::view`. Reaches
//! rendering exclusively through `t2::view`, never `t1::view` directly —
//! `t3::model` wraps `t2::model`, not `t1::model`, and this file mirrors
//! that boundary. Defines only what's genuinely new: the hold box.

use crate::model::Machine;
use macroquad::prelude::*;
use t1::model::Params; // the parameter trait bound — no `T3Params` wrapper exists (§0.1)
use t2::view::Colored; // `draw_grid`'s bound, reached through `t2::view`

// byte-identical to t1::view::RenderConstants; reached through t2::view's
// re-export, not t1::view's.
pub use t2::view::RenderConstants;

/// spec: §15.5 (t2/implementation.md) — transient banner state; re-exported
/// rather than redeclared, so there is one `Banner` type in the workspace.
pub use t2::view::Banner;

const HOLD_BOX_COLOR: Color = Color::new(0.33, 0.33, 0.33, 1.0); // #555555
const HOLD_BOX_DIM_ALPHA: f32 = 0.4;

/// spec: §14.2 — grid/panel geometry is `t2::view::compute_layout`'s own
/// `Layout` (`base`), reused unmodified; only the hold-box geometry, carved
/// out of the top of that panel column, is new.
///
/// Fields and `compute_layout`/`draw_hold_box` are `pub` so `t4::view` can
/// embed this `Layout` as its own `base` and call both directly.
pub struct Layout {
    pub base: t2::view::Layout,
    pub hold_label_y: f32,  // y where the "Hold" text baseline sits
    pub hold_box_top: f32,  // y where the hold box's border starts
    pub hold_box_size: f32, // side length of the (square) hold box
    pub panel_top: f32,     // y where SCORE/LEVEL/banners start — below the hold box
}

pub fn compute_layout(constants: &RenderConstants) -> Layout {
    let base = t2::view::compute_layout(constants);
    let m = t2::view::panel_metrics(base.panel_width);
    let hold_label_y = m.margin_y + m.label_font as f32;
    let hold_box_top = hold_label_y + m.label_font as f32 * 0.4;
    let hold_box_size =
        (constants.pw as f32 * base.base.cell_size).min(base.panel_width - 2.0 * m.margin_x);
    let panel_top = hold_box_top + hold_box_size + m.margin_y;

    Layout {
        base,
        hold_label_y,
        hold_box_top,
        hold_box_size,
        panel_top,
    }
}

/// spec: §14.4 — "Hold" label + square border + held-piece glyph at
/// rotation 0. Dimmed when `machine.swapped` (not available until the next
/// fix), restored to full opacity right after. Uses its own local transform
/// (`hold_box_size / pw`), not `t2::view`'s private `cell_origin` — the
/// hold box isn't a grid cell, it's a fixed-size square at the panel's own
/// scale.
pub fn draw_hold_box<P: Params>(
    constants: &RenderConstants,
    layout: &Layout,
    machine: &Machine<P>,
    piece_color: &impl Fn(P::Piece) -> [f32; 4],
    font: Option<&Font>,
) {
    let m = t2::view::panel_metrics(layout.base.panel_width);
    let x = layout.base.panel_left + m.margin_x;

    t2::view::draw_text_label(
        "Hold",
        x,
        layout.hold_label_y,
        m.label_font,
        t2::view::LABEL_COLOR,
        font,
    );

    let alpha_scale = if machine.swapped {
        HOLD_BOX_DIM_ALPHA
    } else {
        1.0
    };
    let border_color = Color::new(
        HOLD_BOX_COLOR.r,
        HOLD_BOX_COLOR.g,
        HOLD_BOX_COLOR.b,
        alpha_scale,
    );
    draw_rectangle_lines(
        x,
        layout.hold_box_top,
        layout.hold_box_size,
        layout.hold_box_size,
        2.0,
        border_color,
    );

    if let Some(held) = machine.hold {
        let rg = P::rot_grid(held, 0); // always rotation 0 in the hold box
        let [r, g, b, a] = piece_color(held);
        let color = Color::new(r, g, b, a * alpha_scale);
        let hb_cell = layout.hold_box_size / constants.pw as f32;
        for (y, line) in rg.iter().enumerate().take(constants.pw as usize) {
            for (xx, cell) in line.iter().enumerate().take(constants.pw as usize) {
                if cell.is_none() {
                    continue; // exact-sentinel test (D1), not truthiness
                }
                let cx = x + xx as f32 * hb_cell;
                let cy = layout.hold_box_top + (constants.pw as usize - 1 - y) as f32 * hb_cell; // same bottom-up flip as draw_piece
                t2::view::draw_block(cx, cy, hb_cell, color);
            }
        }
    }
}

/// spec: §14.1/§14.7 — public entry point. Call order: clear → hold box →
/// panel → banners → locked blocks → forbidden-zone tint → grid lines →
/// falling piece → game-over overlay. `font` is loaded once by `main.rs`
/// and passed in by reference every frame. Every step past the hold box
/// delegates straight into `t2::view`, narrowing to `&layout.base.base` for
/// the grid-only procedures.
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
    let layout = compute_layout(constants);
    clear_background(t2::view::BG_COLOR);
    draw_hold_box(constants, &layout, machine, &piece_color, font);
    let below_level_y = t2::view::draw_panel(&layout.base, &machine.s2, layout.panel_top, font);
    t2::view::draw_banners(&layout.base, below_level_y, banner, font);
    t2::view::draw_grid(&machine.s2.s1.mg, constants, &layout.base.base);
    t2::view::draw_background(constants, &layout.base.base);
    t2::view::draw_grid_lines(constants, &layout.base.base);
    t2::view::draw_piece(&machine.s2, constants, &layout.base.base, &piece_color);
    if machine.s2.s1.gameover {
        t2::view::draw_game_over(constants, &layout.base, font);
    }
}
