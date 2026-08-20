//! spec: view.rs — renderer (§14).
//!
//! Pure rendering: reads a `&Machine<P>` once per frame (D-Rust2) and draws
//! it with macroquad's immediate-mode API; piece color supplied by the
//! caller as a closure. Wraps `t1::view`'s grid layout/drawing (§14.1) and
//! adds a left info panel and transient banners with no T1 counterpart
//! (§14.4); both are `pub` for reuse by further wrapper layers.

use crate::model::Machine;
use macroquad::prelude::*;
use t1::model::Params;

// §12: fields identical to t1::view::RenderConstants, reused rather than redeclared.
pub use t1::view::RenderConstants;
// §12/§14.4: colours reused as-is; draw_game_over below matches T1's scheme,
// differing only in drawn region and font.
pub use t1::view::{BG_COLOR, GAME_OVER_BG_COLOR, GAME_OVER_TEXT_COLOR};
// §0.1/§14.4: no panel-aware logic in these, so reused verbatim.
pub use t1::view::{draw_background, draw_block, draw_grid, draw_grid_lines, Colored};

/// spec: §15.2 — controller-owned transient banner state, snapshotted at
/// the triggering fix. `None` when no banner is active.
pub struct Banner {
    pub combo: u64,
    pub perfect_clear: bool,
    pub t: f64,
}

pub const LABEL_COLOR: Color = Color::new(0.55, 0.55, 0.55, 1.0);
const VALUE_COLOR: Color = WHITE;
const COMBO_COLOR: Color = Color::new(1.0, 0.816, 0.0, 1.0); // #FFD000
const PERFECT_CLEAR_COLOR: Color = Color::new(0.0, 0.878, 1.0, 1.0); // #00E0FF

/// spec: §14.2 — panel width fraction/clamp, and the gap to the grid's left
/// edge (relative to the panel's own width, so it scales with it).
const PANEL_FRACTION: f32 = 0.22;
const PANEL_MIN_PX: f32 = 120.0;
const PANEL_MAX_PX: f32 = 360.0;
// `pub`: reused by a further wrapper layer's own mirrored side panel, so the
// gap stays visually identical on both sides (§14.2).
pub const PANEL_GRID_GAP_FRACTION: f32 = 0.08;

/// spec: §14.2 (D-Grid-Centering) — desired panel width from `screen_width()`,
/// recomputed every frame, no cached dimension; `compute_layout` clamps it to
/// whatever margin the (unmodified) centered grid leaves on the left.
// `pub` for the same reason as `PANEL_GRID_GAP_FRACTION` above.
pub fn desired_panel_px() -> f32 {
    (screen_width() * PANEL_FRACTION).clamp(PANEL_MIN_PX, PANEL_MAX_PX)
}

/// spec: §14.2 — `base` is `t1::view::compute_layout`'s own `Layout`,
/// embedded unmodified; the panel never shrinks or offsets the grid's
/// centering. `panel_left`/`panel_width` place the info panel in the left
/// margin `base.origin_x` already leaves, snug against the grid rather than
/// pinned to the window edge.
pub struct Layout {
    pub base: t1::view::Layout,
    pub panel_left: f32,
    pub panel_width: f32,
}

pub fn compute_layout(constants: &RenderConstants) -> Layout {
    let base = t1::view::compute_layout(constants);

    let desired = desired_panel_px();
    let gap = desired * PANEL_GRID_GAP_FRACTION;
    let panel_width = desired.min((base.origin_x - gap).max(0.0));
    let panel_left = (base.origin_x - gap - panel_width).max(0.0);

    Layout {
        base,
        panel_left,
        panel_width,
    }
}

/// spec: §14.4 — thin adapter over `t1::view::draw_piece` (same body; no
/// panel-aware logic), needed because `Machine<P>` here wraps
/// `t1::model::Machine<P>` as `s1`, so it can't be a plain `pub use`.
pub fn draw_piece<P: Params>(
    machine: &Machine<P>,
    constants: &RenderConstants,
    layout: &t1::view::Layout,
    piece_color: &impl Fn(P::Piece) -> [f32; 4],
) {
    t1::view::draw_piece(&machine.s1, constants, layout, piece_color)
}

/// spec: §14.4 — overlay spans the grid region only (`[origin_x,
/// screen_width())`), leaving the panel readable; reuses T1's colours but
/// not its logic (T1 has no panel to exclude, no loaded `Font`). The dimmed
/// rectangle also covers the empty margin past the grid's right edge, but
/// the text is centered on the grid's own box specifically — centering
/// against the wider rectangle would drag it off the grid's actual center.
pub fn draw_game_over(constants: &RenderConstants, layout: &Layout, font: Option<&Font>) {
    let text = "GAME OVER";
    let font_size = (layout.base.cell_size * 1.2).max(16.0).round() as u16;
    let dims = measure_text(text, font, font_size, 1.0);
    let (w, h) = (screen_width(), screen_height());
    let grid_x0 = layout.base.origin_x;
    let grid_width = constants.wm as f32 * layout.base.cell_size;
    draw_rectangle(grid_x0, 0.0, w - grid_x0, h, GAME_OVER_BG_COLOR);
    draw_text_label(
        text,
        grid_x0 + (grid_width - dims.width) / 2.0,
        (h - dims.height) / 2.0 + dims.offset_y,
        font_size,
        GAME_OVER_TEXT_COLOR,
        font,
    );
}

/// spec: §14.4 — routes text through `draw_text_ex` with an explicit
/// `font` rather than `draw_text`'s built-in bitmap font, which pixelates
/// once stretched to panel-sized text.
pub fn draw_text_label(
    text: &str,
    x: f32,
    y: f32,
    font_size: u16,
    color: Color,
    font: Option<&Font>,
) {
    draw_text_ex(
        text,
        x,
        y,
        TextParams {
            font,
            font_size,
            font_scale: 1.0,
            color,
            ..Default::default()
        },
    );
}

/// spec: §14.4 — layout shared by `draw_panel`/`draw_banners` so the two
/// stay aligned with each other; `pub` for reuse by further wrapper layers
/// sizing their own content against the same panel column.
pub struct PanelMetrics {
    pub margin_y: f32,
    pub margin_x: f32,
    pub label_font: u16,
    pub value_font: u16,
    pub banner_font: u16,
}

/// spec: §14.4 — `panel_width` is the sole scale reference for both axes;
/// there is no separate "panel height" (the panel is just a column of text,
/// as tall as its content). Margins and fonts all derive from it so they
/// stay proportioned to each other.
pub fn panel_metrics(panel_width: f32) -> PanelMetrics {
    PanelMetrics {
        margin_y: panel_width * 0.12,
        margin_x: panel_width * 0.24,
        label_font: (panel_width * 0.10).max(9.0) as u16,
        value_font: (panel_width * 0.10).max(10.0) as u16,
        banner_font: (panel_width * 0.10).max(9.0) as u16,
    }
}

/// spec: §14.4 — draws SCORE/LEVEL top-down at `panel_metrics`'s margin,
/// starting at `top` (passed in rather than derived internally, so a
/// wrapper with content above the panel can supply its own start point).
/// Returns the y just below the LEVEL block, for `draw_banners` to stack on
/// without either function hardcoding the other's height.
pub fn draw_panel<P: Params>(
    layout: &Layout,
    machine: &Machine<P>,
    top: f32,
    font: Option<&Font>,
) -> f32 {
    let m = panel_metrics(layout.panel_width);
    let x = layout.panel_left + m.margin_x;
    let mut y = top + m.label_font as f32;

    draw_text_label("SCORE", x, y, m.label_font, LABEL_COLOR, font);
    y += m.value_font as f32 * 1.1;
    draw_text_label(
        &machine.score.to_string(),
        x,
        y,
        m.value_font,
        VALUE_COLOR,
        font,
    );
    y += m.value_font as f32 * 2.0;

    draw_text_label("LEVEL", x, y, m.label_font, LABEL_COLOR, font);
    y += m.value_font as f32 * 1.1;
    draw_text_label(
        &machine.level.to_string(),
        x,
        y,
        m.value_font,
        VALUE_COLOR,
        font,
    );
    y += m.value_font as f32 * 2.0;

    y
}

/// spec: §14.4 — combo/perfect-clear banners below `below_level_y`
/// (`draw_panel`'s return value), each in a fixed slot (`banner_font ×
/// 1.4`) reserved even when empty, so the perfect-clear line's position
/// doesn't depend on whether the combo line is drawn.
///
/// Displays the stored `combo` field as-is (§4-T2b: internally offset for
/// scoring, not for display) — first clearing fix leaves `combo == 1` (no
/// banner), next leaves `combo == 2` ("2-hit combo!"), and so on.
pub fn draw_banners(
    layout: &Layout,
    below_level_y: f32,
    banner: Option<&Banner>,
    font: Option<&Font>,
) {
    let m = panel_metrics(layout.panel_width);
    let x = layout.panel_left + m.margin_x;
    let slot = m.banner_font as f32 * 1.4;
    let mut y = below_level_y + m.margin_y;

    if let Some(b) = banner {
        if b.combo >= 2 {
            draw_text_label(
                &format!("{}-hit combo!", b.combo),
                x,
                y + m.banner_font as f32,
                m.banner_font,
                COMBO_COLOR,
                font,
            );
        }
    }
    y += slot;

    if let Some(b) = banner {
        if b.perfect_clear {
            draw_text_label(
                "Perfect clear!",
                x,
                y + m.banner_font as f32,
                m.banner_font,
                PERFECT_CLEAR_COLOR,
                font,
            );
        }
    }
}

/// spec: §14.1 — public entry point. Call order (§14.6): whole-canvas
/// clear → panel → banners → locked blocks → forbidden-zone tint → grid
/// lines → falling piece → game-over overlay if applicable. `font` is
/// loaded once by `main.rs` (§15) and passed in by reference every frame —
/// `render` never loads or owns it.
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
    clear_background(BG_COLOR);
    let below_level_y = draw_panel(
        &layout,
        machine,
        panel_metrics(layout.panel_width).margin_y,
        font,
    );
    draw_banners(&layout, below_level_y, banner, font);
    draw_grid(&machine.s1.mg, constants, &layout.base);
    draw_background(constants, &layout.base);
    draw_grid_lines(constants, &layout.base);
    draw_piece(machine, constants, &layout.base, &piece_color);
    if machine.s1.gameover {
        draw_game_over(constants, &layout, font);
    }
}
