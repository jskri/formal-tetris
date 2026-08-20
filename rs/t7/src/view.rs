//! spec: view.rs — renderer (§14, `implementation.md`).
//!
//! Own-board rendering reuses `t6::view::render` on `machine.s6` as an
//! opaque whole; the garbage gauge and opponent-mini strip are new,
//! self-contained regions added to the right, without reflowing the
//! inherited grid/panel layout (§14.1). The mini strip starts past
//! `t4::view`'s own preview column, not at the grid edge, since the
//! preview column already occupies part of the right margin and starting
//! at the grid edge would draw minis over it (§14.3). The garbage gauge,
//! only `cell_size/3` wide, fits in the grid-to-preview gap instead.
//!
//! Deviation from `implementation.md` §14.1's pseudocode: `piece_color` is
//! taken as an explicit closure parameter — the same convention
//! `t1::view`–`t5::view`'s own `render` already use — rather than calling
//! `t1::instance::piece_color` directly, since a direct call only
//! type-checks for the one instantiation where `P::Piece =
//! t1::instance::Piece`, not for `P: Params` in general.
//!
//! Deviation from `implementation.md` §14.3's `OpponentView<P>` shape: the
//! board-shaped fields (`mg`/`p`/`py`/`px`/`pr`) are wrapped in
//! `Option<OpponentBoard<P>>` here instead of being mandatory, so "no
//! `State` yet" is representable as `None` rather than a sentinel inside a
//! mandatory `mg`.

use crate::model::{Machine, Params};
use macroquad::prelude::*;
use t1::view::Colored;

// byte-identical fields to t1::view::RenderConstants; reused through the
// chain, per implementation.md §12, same as every prior layer.
/// spec: §15.2 (t2/implementation.md) — controller-owned transient banner
/// state, reused unchanged.
pub use t6::view::Banner;
pub use t6::view::RenderConstants;

/// spec: §14.2 — garbage gauge fill color, deliberately distinct from
/// `GARBAGE_BLOCK_COLOR`: the gauge warns about garbage not yet
/// materialized, so it must not look like the block it becomes. Cosmetic
/// starting value, not measured-optimal.
pub const GARBAGE_GAUGE_COLOR: [f32; 4] = [
    0x8a as f32 / 255.0,
    0x6d as f32 / 255.0,
    0x1f as f32 / 255.0,
    1.0,
];
/// spec: §14.2/§11 — locked garbage cell color, read by `instance.rs`'s
/// `Colored` impl for `crate::model::Garbage`.
pub const GARBAGE_BLOCK_COLOR: [f32; 4] = [
    0x88 as f32 / 255.0,
    0x88 as f32 / 255.0,
    0x88 as f32 / 255.0,
    1.0,
];

const GARBAGE_GAUGE_FRAC: f32 = 1.0 / 3.0; // relative to cell_size — starting value, not measured-optimal
const MINI_GAP: f32 = 4.0;
const DEAD_MINI_COLOR: Color = Color::new(0.33, 0.33, 0.33, 1.0);
const MINI_BORDER_COLOR: Color = Color::new(0.27, 0.27, 0.27, 1.0);
const MINI_TARGET_BORDER_COLOR: Color = Color::new(0.9, 0.15, 0.1, 1.0);
const MINI_PLACEHOLDER_BG: Color = Color::new(0.13, 0.13, 0.13, 1.0);
const MINI_LABEL_COLOR: Color = Color::new(0.7, 0.7, 0.7, 1.0);

/// spec: §14.3 — an opponent's own board, populated once at least one wire
/// `State` (`net.rs`, §15.3) has been observed for that player.
pub struct OpponentBoard<P: Params> {
    pub mg: Vec<Vec<Option<t1::model::PieceOrExtra<P>>>>,
    pub p: P::Piece,
    pub py: i64,
    pub px: i64,
    pub pr: u8,
}

/// spec: §14.3 — no `T7.v` counterpart; populated by `main.rs`, never
/// through `Machine`'s own fields (an opponent's board is never local
/// state).
pub struct OpponentView<P: Params> {
    pub player_index: usize,
    pub name: String,
    pub board: Option<OpponentBoard<P>>, // None: no board observed yet — flat gray placeholder
    pub gameover: bool,
    pub connected: bool,
}

/// spec: §14.1 — public entry point: `t6::view::render` draws `machine.s6`
/// as an opaque whole, then `draw_side_regions` adds the gauge and mini
/// strip in the margin beyond it.
pub fn render<P: Params>(
    constants: &RenderConstants,
    machine: &Machine<P>,
    piece_color: impl Fn(P::Piece) -> [f32; 4],
    banner: Option<&Banner>,
    opponents: &[OpponentView<P>],
    font: Option<&Font>,
) where
    P::Piece: Colored,
    P::CellExtra: Colored,
{
    t6::view::render(constants, &machine.s6, &piece_color, banner, font);
    draw_side_regions(constants, machine, piece_color, opponents, font);
}

/// spec: §14.2/§14.3 — the gauge and mini strip alone, without the
/// own-board half. Split out for `S8` (§15.0): the real `Machine<P>` stays
/// alive headless behind a filler board, and this keeps rendering off it.
pub fn draw_side_regions<P: Params>(
    constants: &RenderConstants,
    machine: &Machine<P>,
    piece_color: impl Fn(P::Piece) -> [f32; 4],
    opponents: &[OpponentView<P>],
    font: Option<&Font>,
) where
    P::Piece: Colored,
    P::CellExtra: Colored,
{
    // Recomputed rather than threaded through from `t6::view::render`'s own
    // call: `t4::view::compute_layout::<P>` is a pure function of
    // `constants` and the window size, so calling it again here with the
    // same inputs reproduces the identical `Layout`.
    let l4 = t4::view::compute_layout::<P>(constants);
    let layout = &l4.base.base.base; // t1::view::Layout
    let grid_right_x = layout.origin_x + constants.wm as f32 * layout.cell_size;
    let gauge_w = layout.cell_size * GARBAGE_GAUGE_FRAC;
    draw_garbage_gauge(constants, layout, grid_right_x, gauge_w, machine.garbage);
    // spec: §14.3 — strip starts past the preview column, not the grid edge.
    let strip_x = l4.right_origin + l4.base.base.panel_width + MINI_GAP;
    draw_opponent_minis(
        constants,
        opponents,
        &piece_color,
        strip_x,
        machine.target,
        font,
    );
}

/// spec: §14.2 — vertical bar, one `cell_size`-height segment per unit of
/// `garbage`, clamped at `HM`, single flat color, flush against the grid's
/// right edge — no `T7.v` counterpart (rendering only).
fn draw_garbage_gauge(
    constants: &RenderConstants,
    layout: &t1::view::Layout,
    gauge_x: f32,
    gauge_w: f32,
    garbage: i64,
) {
    let amount = garbage.clamp(0, constants.hm);
    if amount <= 0 {
        return;
    }
    let gh = amount as f32 * layout.cell_size;
    let gy = layout.origin_y + constants.hm as f32 * layout.cell_size - gh;
    let [r, g, b, a] = GARBAGE_GAUGE_COLOR;
    draw_rectangle(gauge_x, gy, gauge_w, gh, Color::new(r, g, b, a));
}

/// spec: §14.3 — fixed-size region (`strip_x` to `screen_width()`)
/// regardless of `opponents.len()`; mini size is chosen to tile all
/// entries within it, so more opponents shrink each mini rather than
/// growing the strip.
fn draw_opponent_minis<P: Params>(
    constants: &RenderConstants,
    opponents: &[OpponentView<P>],
    piece_color: &impl Fn(P::Piece) -> [f32; 4],
    strip_x: f32,
    target: usize,
    font: Option<&Font>,
) where
    P::Piece: Colored,
    P::CellExtra: Colored,
{
    let strip_w = screen_width() - strip_x;
    let strip_h = screen_height();
    let n = opponents.len();
    if n == 0 || strip_w <= 0.0 {
        return;
    }

    let label_font = (strip_w * 0.12).max(8.0);
    let label_h = label_font * 1.3;

    let (cols, cell_size) = best_tiling(
        n,
        strip_w,
        strip_h,
        constants.wm,
        constants.hm,
        label_h,
        MINI_GAP,
    );
    if cell_size <= 0.0 {
        return;
    }
    let mini_w = constants.wm as f32 * cell_size;
    let mini_h = constants.hm as f32 * cell_size;

    for (i, opp) in opponents.iter().enumerate() {
        let col = (i % cols) as f32;
        let row = (i / cols) as f32;
        let ox = strip_x + MINI_GAP + col * (mini_w + MINI_GAP);
        let oy = MINI_GAP + row * (mini_h + label_h + MINI_GAP);
        // spec: §14.3 — border override only matters with more than one opponent.
        let is_target = opponents.len() > 1 && opp.player_index == target;
        draw_mini(
            constants,
            opp,
            ox,
            oy,
            cell_size,
            mini_w,
            mini_h,
            label_h,
            piece_color,
            is_target,
            font,
        );
    }
}

/// Tries every column count from 1 to `n`, picks whichever maximizes the
/// resulting mini `cell_size` — the only thing that varies is how
/// `strip_w`/`strip_h` get divided among rows/cols.
fn best_tiling(
    n: usize,
    strip_w: f32,
    strip_h: f32,
    wm: i64,
    hm: i64,
    label_h: f32,
    gap: f32,
) -> (usize, f32) {
    let mut best = (1usize, 0.0f32);
    for cols in 1..=n {
        let rows = n.div_ceil(cols);
        let avail_w = (strip_w - (cols as f32 + 1.0) * gap) / cols as f32;
        let avail_h = (strip_h - (rows as f32 + 1.0) * gap - rows as f32 * label_h) / rows as f32;
        if avail_w <= 0.0 || avail_h <= 0.0 {
            continue;
        }
        let cell_size = (avail_w / wm as f32).min(avail_h / hm as f32);
        if cell_size > best.1 {
            best = (cols, cell_size);
        }
    }
    best
}

/// spec: §14.3 — one mini-grid: gray placeholder before the first board
/// observation or once disconnected/gameover; otherwise block colors +
/// current piece, forbidden-zone tint, no grid lines, no ghost/next/hold.
/// Border color/width for the current target are set by
/// `draw_opponent_minis`.
#[allow(clippy::too_many_arguments)]
fn draw_mini<P: Params>(
    constants: &RenderConstants,
    opp: &OpponentView<P>,
    ox: f32,
    oy: f32,
    cell_size: f32,
    mini_w: f32,
    mini_h: f32,
    label_h: f32,
    piece_color: &impl Fn(P::Piece) -> [f32; 4],
    is_target: bool,
    font: Option<&Font>,
) where
    P::Piece: Colored,
    P::CellExtra: Colored,
{
    let label_font_size = (label_h / 1.3).max(8.0).round() as u16;
    t2::view::draw_text_label(
        &opp.name,
        ox,
        oy + label_font_size as f32,
        label_font_size,
        MINI_LABEL_COLOR,
        font,
    );

    let gy0 = oy + label_h;
    let (border_color, border_width) = if is_target {
        (MINI_TARGET_BORDER_COLOR, 3.0)
    } else {
        (MINI_BORDER_COLOR, 1.0)
    };

    let Some(board) = &opp.board else {
        draw_rectangle(ox, gy0, mini_w, mini_h, MINI_PLACEHOLDER_BG);
        draw_rectangle_lines(ox, gy0, mini_w, mini_h, border_width, border_color);
        return;
    };

    let dead = opp.gameover || !opp.connected;

    let (fh, fw) = (constants.fh, constants.fw);
    let fx = ox + constants.fx as f32 * cell_size;
    let fy = gy0 + (constants.hm - constants.fy - fh) as f32 * cell_size;
    let forbidden_color = if dead {
        Color::new(0.2, 0.03, 0.03, 1.0)
    } else {
        Color::new(0.35, 0.06, 0.06, 1.0)
    };
    draw_rectangle(
        fx,
        fy,
        fw as f32 * cell_size,
        fh as f32 * cell_size,
        forbidden_color,
    );

    for (y, row) in board.mg.iter().enumerate() {
        for (x, cell) in row.iter().enumerate() {
            let Some(cell) = cell else { continue };
            let color = if dead {
                DEAD_MINI_COLOR
            } else {
                let [r, g, b, a] = match cell {
                    t1::model::PieceOrExtra::Piece(p) => p.color(),
                    t1::model::PieceOrExtra::Extra(e) => e.color(),
                };
                Color::new(r, g, b, a)
            };
            let cx = ox + x as f32 * cell_size;
            let cy = gy0 + (constants.hm - 1 - y as i64) as f32 * cell_size;
            draw_rectangle(cx + 0.5, cy + 0.5, cell_size - 1.0, cell_size - 1.0, color);
        }
    }

    if !dead {
        let pg = P::rot_grid(board.p, board.pr);
        let [r, g, b, a] = piece_color(board.p);
        for dy in 0..constants.pw {
            for dx in 0..constants.pw {
                if pg[dy as usize][dx as usize].is_none() {
                    continue;
                }
                let (y, x) = (board.py + dy, board.px + dx);
                if y < 0 || y >= constants.hm || x < 0 || x >= constants.wm {
                    continue;
                }
                let cx = ox + x as f32 * cell_size;
                let cy = gy0 + (constants.hm - 1 - y) as f32 * cell_size;
                draw_rectangle(
                    cx + 0.5,
                    cy + 0.5,
                    cell_size - 1.0,
                    cell_size - 1.0,
                    Color::new(r, g, b, a),
                );
            }
        }
    }

    draw_rectangle_lines(ox, gy0, mini_w, mini_h, border_width, border_color);
}
