//! spec: view.rs — renderer (§14, `implementation.md`).
//!
//! Pure rendering: reads a `&Machine<P>` once per frame (D-Rust2, skill
//! §3.1) and draws it with macroquad's immediate-mode API. Never imports
//! `instance.rs`; piece-color mapping is supplied by the caller as a
//! closure, as in `t1::view`–`t4::view`. Only `draw_ghost` is new here —
//! everything else reaches `t4::view`'s/`t3::view`'s/`t2::view`'s own
//! `pub` API directly (skill §7), the same one-layer-deeper reuse
//! `t4::view` already uses on `t3::view`.

use crate::model::{Machine, Params};
use macroquad::prelude::*;
use t2::view::Colored; // `draw_grid`'s bound, reached through `t2::view` (same as `t3::view`'s/`t4::view`'s own).

// byte-identical fields to t1::view::RenderConstants (hm, wm, pw, fy, fx,
// fh, fw); reused via t4::view's own re-export (§12).
pub use t4::view::RenderConstants;

/// spec: §15.2 (t2/implementation.md) — controller-owned transient banner
/// state, re-exported rather than redeclared (as `t4::view` reuses
/// `t3::view`'s own).
pub use t4::view::Banner;

/// spec: §14.2 — starting, not measured-optimal, value (same caveat as
/// every prior layer's cosmetic constants).
const GHOST_ALPHA: f32 = 0.25;

/// spec: §14.3 — view-only rendering of `gy`/`px`/`pr`/`p`'s ghost
/// projection (no `T5.v` counterpart). Inlines `t1::view::draw_piece`'s
/// coordinate transform rather than reusing it (no row-source
/// parameterization there); no special-casing for `gy == py` since the
/// active piece drawn afterward covers it. req-piece-shadow. `pub`, like
/// `compute_layout`/`draw_preview`, so callers can compose their own
/// render pass (used by `final/`'s gameover-lockout screen).
pub fn draw_ghost<P: Params>(
    constants: &RenderConstants,
    layout: &t1::view::Layout,
    machine: &Machine<P>,
    piece_color: &impl Fn(P::Piece) -> [f32; 4],
) {
    let s1 = &machine.s4.s3.s2.s1;
    let pg = P::rot_grid(s1.p, s1.pr);
    let [r, g, b, a] = piece_color(s1.p);
    let color = Color::new(r, g, b, a * GHOST_ALPHA);
    for dy in 0..constants.pw {
        for dx in 0..constants.pw {
            if pg[dy as usize][dx as usize].is_none() {
                continue; // exact-sentinel test (D1), not truthiness
            }
            let (y, x) = (machine.gy + dy, s1.px + dx);
            if y < 0 || y >= constants.hm || x < 0 || x >= constants.wm {
                continue; // may be partially outside the main grid's box
            }
            let cx = layout.origin_x + x as f32 * layout.cell_size;
            let cy = layout.origin_y + (constants.hm - 1 - y) as f32 * layout.cell_size;
            t2::view::draw_block(cx, cy, layout.cell_size, color);
        }
    }
}

/// spec: §14.1/§14.4 — public entry point. Call order: whole-canvas clear
/// → hold box → panel → banners → preview column → locked blocks →
/// forbidden-zone tint → grid lines → ghost piece → falling piece →
/// game-over overlay if applicable. `font` is loaded once by `main.rs`
/// and passed in by reference every frame; `render` never loads or owns
/// it. Returns `()` — no return value is needed yet, so none is added
/// speculatively.
///
/// §14.4: `t5::view` has no `Layout` of its own — `draw_ghost` needs no
/// geometry beyond `t4::view::Layout`'s existing chain
/// (`layout.base.base.base` is `t1::view::Layout`).
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
    let layout = t4::view::compute_layout::<P>(constants); // pub (§0.2)
    clear_background(t2::view::BG_COLOR);
    t3::view::draw_hold_box(constants, &layout.base, &machine.s4.s3, &piece_color, font);
    let below_level_y = t2::view::draw_panel(
        &layout.base.base,
        &machine.s4.s3.s2,
        layout.base.panel_top,
        font,
    );
    t2::view::draw_banners(&layout.base.base, below_level_y, banner, font);
    t4::view::draw_preview::<P>(constants, &layout, &machine.s4.next, &piece_color, font); // pub (§0.2)
    t2::view::draw_grid(&machine.s4.s3.s2.s1.mg, constants, &layout.base.base.base);
    t2::view::draw_background(constants, &layout.base.base.base);
    t2::view::draw_grid_lines(constants, &layout.base.base.base);
    draw_ghost::<P>(constants, &layout.base.base.base, machine, &piece_color); // new — between grid lines and piece
    t2::view::draw_piece(
        &machine.s4.s3.s2,
        constants,
        &layout.base.base.base,
        &piece_color,
    );
    if machine.s4.s3.s2.s1.gameover {
        t2::view::draw_game_over(constants, &layout.base.base, font);
    }
}
