//! Clear-flash / garbage-flash / gameover-partial timers and their draw
//! functions. Both timer types are plain state carried alongside
//! `RunState` in the caller's frame loop, advanced by the same `now`
//! (`get_time()`) every other per-frame calculation already uses.

use macroquad::prelude::*;

use t1::model::{is_full_row, PieceOrExtra};
use t6::model::Params;
use t6::view::RenderConstants;

pub const CLEAR_ANIM_SECS: f64 = 0.18;
pub const TETRIS_ANIM_SECS: f64 = 0.32;
pub const GARBAGE_ANIM_SECS: f64 = 0.13;
pub const TETRIS_SHAKE_PX: f32 = 6.0;
/// Base amplitude for a garbage-arrival shake — scaled by `row_count.min(2)`
/// at the call site, since a bigger delivery should read as a harder hit.
pub const GARBAGE_SHAKE_PX: f32 = 8.0;

/// The merged-grid-plus-full-rows pair `precompute_clear` returns — named
/// so call sites don't have to spell out the nested generic type.
pub type ClearPrecompute<P> = (Vec<Vec<Option<PieceOrExtra<P>>>>, Vec<usize>);

/// Armed on a locking action that clears at least one line. `grid` is the
/// placed-but-uncleared board (this piece's cells merged in, at its
/// position/rotation the instant before the authoritative fix/fall/drop
/// call ran) and `rows` are the row indices that qualify as full in it.
pub struct ClearAnim<P: Params> {
    pub grid: Vec<Vec<Option<PieceOrExtra<P>>>>,
    pub rows: Vec<usize>,
    pub tetris: bool,
    pub start: f64,
}

impl<P: Params> ClearAnim<P> {
    pub fn new(grid: Vec<Vec<Option<PieceOrExtra<P>>>>, rows: Vec<usize>, start: f64) -> Self {
        let tetris = rows.len() == 4;
        ClearAnim {
            grid,
            rows,
            tetris,
            start,
        }
    }

    pub fn duration(&self) -> f64 {
        if self.tetris {
            TETRIS_ANIM_SECS
        } else {
            CLEAR_ANIM_SECS
        }
    }

    pub fn done(&self, now: f64) -> bool {
        now - self.start >= self.duration()
    }
}

/// R-ProgressCurve: linear ramp for a 1-3 line clear; a Tetris clear
/// pulses instead via an early-white curve plus a decaying sine ripple.
/// Values can briefly exceed `1.0` — callers clamp alpha, not this curve.
pub fn progress<P: Params>(anim: &ClearAnim<P>, now: f64) -> f32 {
    let t = ((now - anim.start) / anim.duration()).max(0.0) as f32;
    if anim.tetris {
        let base = (t * 1.3).min(1.0);
        let flicker = (t * std::f32::consts::PI * 6.0).sin() * (1.0 - t) * 0.4;
        base + flicker
    } else {
        t
    }
}

/// R-GarbageArm: armed only once garbage actually materializes, never
/// merely "garbage was pending". Duration `GARBAGE_ANIM_SECS`, alpha
/// `1.0 → 0.0` linearly — a hard, fast-cutoff flash, not a fade-in.
pub struct GarbageAnim {
    pub row_count: u8,
    pub start: f64,
}

impl GarbageAnim {
    pub fn done(&self, now: f64) -> bool {
        now - self.start >= GARBAGE_ANIM_SECS
    }

    pub fn progress(&self, now: f64) -> f32 {
        (((now - self.start) / GARBAGE_ANIM_SECS).max(0.0) as f32).min(1.0)
    }
}

/// A decaying random offset — `remaining_frac` is `1.0` at the start of the
/// shake, `0.0` once it's over. Applied by the caller as a translation of
/// the render origin for the duration of a Tetris clear or a garbage
/// arrival.
pub fn shake_offset(amp_px: f32, remaining_frac: f32) -> (f32, f32) {
    let amp = amp_px * remaining_frac.max(0.0);
    let dx = macroquad::rand::gen_range(-amp, amp);
    let dy = macroquad::rand::gen_range(-amp, amp);
    (dx, dy)
}

/// R-ClearPrecompute: reconstructs the "placed, not yet cleared" grid a
/// fix/fall/drop call is about to consume and never itself exposes, from
/// the same public inputs that call reads. `(py, px)` are explicit params
/// (rather than read off a `Machine`) so one function serves both the
/// soft-lock call site (the piece's current `py`/`px`) and the hard-drop
/// call site (`machine.gy` in place of `py`).
pub fn precompute_clear<P: t1::model::Params>(
    mg: &[Vec<Option<PieceOrExtra<P>>>],
    p: P::Piece,
    py: i64,
    px: i64,
    pr: u8,
) -> ClearPrecompute<P> {
    let mut grid: Vec<Vec<Option<PieceOrExtra<P>>>> = mg.to_vec();
    let hm = grid.len() as i64;
    let wm = grid.first().map_or(0, |row| row.len()) as i64;
    let pg = P::rot_grid(p, pr);
    for dy in 0..P::PW {
        for dx in 0..P::PW {
            if pg[dy as usize][dx as usize].is_none() {
                continue; // exact-sentinel test (D1), not truthiness
            }
            let (y, x) = (py + dy, px + dx);
            if y < 0 || y >= hm || x < 0 || x >= wm {
                continue; // may be partially outside the main grid's box
            }
            grid[y as usize][x as usize] = Some(PieceOrExtra::Piece(p));
        }
    }
    let y_start = py.max(0);
    let y_end = (py + P::PW).min(hm);
    let mut rows = Vec::new();
    for y in y_start..y_end {
        if is_full_row(&grid[y as usize], Option::is_some) {
            rows.push(y as usize);
        }
    }
    (grid, rows)
}

/// Redraws the frozen `grid` (no falling piece — already merged in) via
/// the same primitives the ordinary renderer uses, then fills only `rows`
/// white at `alpha = progress.clamp(0.0, 1.0)`. Mirrors
/// `t5::view::render`'s own call sequence minus the ghost/falling-piece/
/// gameover-overlay steps, with no banner (never shown during the flash
/// itself). Takes `&t6::model::Machine<P>` (not `&t7::model::Machine<P>`)
/// so one function serves both engines — a multiplayer caller passes
/// `&session.machine.as_ref().unwrap().s6`.
///
/// `shake` is a small pixel offset applied only to the highlighted rows
/// themselves, not to the whole frame — the board/panel/preview are drawn
/// at their ordinary position, and offsetting known-good screen-space
/// coordinates by a constant can't invert macroquad's top-left-origin
/// space the way swapping in a translated `Camera2D` would.
#[allow(clippy::too_many_arguments)]
pub fn draw_clear_flash<P: Params>(
    constants: &RenderConstants,
    machine: &t6::model::Machine<P>,
    grid: &[Vec<Option<PieceOrExtra<P>>>],
    rows: &[usize],
    progress: f32,
    shake: (f32, f32),
    piece_color: &impl Fn(P::Piece) -> [f32; 4],
    font: Option<&Font>,
) where
    P::Piece: t2::view::Colored,
    P::CellExtra: t2::view::Colored,
{
    let layout = t4::view::compute_layout::<P>(constants);
    clear_background(t2::view::BG_COLOR);
    t3::view::draw_hold_box(constants, &layout.base, &machine.s4.s3, piece_color, font);
    t2::view::draw_panel(
        &layout.base.base,
        &machine.s4.s3.s2,
        layout.base.panel_top,
        font,
    );
    t4::view::draw_preview::<P>(constants, &layout, &machine.s4.next, piece_color, font);
    t2::view::draw_grid(grid, constants, &layout.base.base.base);
    t2::view::draw_background(constants, &layout.base.base.base);
    t2::view::draw_grid_lines(constants, &layout.base.base.base);

    let base = &layout.base.base.base; // t1::view::Layout: cell_size/origin_x/origin_y
    let (dx, dy) = shake;
    let alpha = progress.clamp(0.0, 1.0);
    let color = Color::new(1.0, 1.0, 1.0, alpha);
    for &y in rows {
        // Same bottom-up flip t1::view's own (private) cell_origin uses:
        // board y counts up from the bottom, screen y grows down.
        let cy = base.origin_y + (constants.hm - 1 - y as i64) as f32 * base.cell_size;
        draw_rectangle(
            base.origin_x + dx,
            cy + dy,
            constants.wm as f32 * base.cell_size,
            base.cell_size,
            color,
        );
    }
}

/// Drawn by the caller *after* its own normal frame render — not a
/// replacement, deliberately not a fade-in: a flat reddish fill over the
/// bottom `row_count` rows (board `y` already counts up from the bottom)
/// at `alpha = 1.0 - progress`. `shake` offsets only these rows — see
/// `draw_clear_flash`'s own doc comment for why the whole frame is never
/// shaken via a camera swap.
pub fn draw_garbage_flash(
    constants: &RenderConstants,
    layout: &t1::view::Layout,
    row_count: u8,
    progress: f32,
    shake: (f32, f32),
) {
    if row_count == 0 {
        return;
    }
    let (dx, dy) = shake;
    let alpha = (1.0 - progress).clamp(0.0, 1.0);
    let color = Color::new(1.0, 0.816, 0.816, alpha); // #FFD0D0
    for y in 0..row_count as i64 {
        let cy = layout.origin_y + (constants.hm - 1 - y) as f32 * layout.cell_size;
        draw_rectangle(
            layout.origin_x + dx,
            cy + dy,
            constants.wm as f32 * layout.cell_size,
            layout.cell_size,
            color,
        );
    }
}

/// R-DrawNoGameover: mirrors `t5::view::render`'s body (same argument
/// order) minus its trailing gameover-overlay call, so the single-player
/// lockout window can show the frozen board without mutating `machine`'s
/// own `gameover` field to dodge that branch. The caller layers
/// `draw_gameover_partial` on top for the dim+heading itself.
pub fn draw_board_without_gameover_overlay<P: Params>(
    constants: &RenderConstants,
    machine: &t6::model::Machine<P>,
    piece_color: impl Fn(P::Piece) -> [f32; 4],
    banner: Option<&t2::view::Banner>,
    font: Option<&Font>,
) where
    P::Piece: t2::view::Colored,
    P::CellExtra: t2::view::Colored,
{
    let layout = t4::view::compute_layout::<P>(constants);
    clear_background(t2::view::BG_COLOR);
    t3::view::draw_hold_box(constants, &layout.base, &machine.s4.s3, &piece_color, font);
    let below_level_y = t2::view::draw_panel(
        &layout.base.base,
        &machine.s4.s3.s2,
        layout.base.panel_top,
        font,
    );
    t2::view::draw_banners(&layout.base.base, below_level_y, banner, font);
    t4::view::draw_preview::<P>(constants, &layout, &machine.s4.next, &piece_color, font);
    t2::view::draw_grid(&machine.s4.s3.s2.s1.mg, constants, &layout.base.base.base);
    t2::view::draw_background(constants, &layout.base.base.base);
    t2::view::draw_grid_lines(constants, &layout.base.base.base);
    t5::view::draw_ghost::<P>(constants, &layout.base.base.base, machine, &piece_color);
    t2::view::draw_piece(
        &machine.s4.s3.s2,
        constants,
        &layout.base.base.base,
        &piece_color,
    );
}

/// Dim overlay + "GAME OVER" heading only, omitting whatever restart-prompt
/// line the normal gameover render already draws elsewhere — used during a
/// lockout window before the restart prompt/input becomes active.
pub fn draw_gameover_partial(
    constants: &RenderConstants,
    layout: &t1::view::Layout,
    font: Option<&Font>,
) {
    let grid_x = layout.origin_x;
    let grid_w = constants.wm as f32 * layout.cell_size;
    draw_rectangle(
        grid_x,
        0.0,
        grid_w,
        screen_height(),
        Color::new(0.0, 0.0, 0.0, 0.7),
    );

    let text = "GAME OVER";
    let size = (screen_height() * 0.06) as u16;
    let dims = measure_text(text, font, size, 1.0);
    let cx = grid_x + grid_w / 2.0 - dims.width / 2.0;
    let cy = screen_height() / 2.0;
    t2::view::draw_text_label(text, cx, cy, size, WHITE, font);
}
