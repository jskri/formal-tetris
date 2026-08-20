//! Miscellaneous primitives shared by every crate's `main.rs`: constants,
//! types, and free functions with no dependency on any `Machine<P>`'s
//! shape. `Action::fire` is defined per crate instead of here
//! (R-ActionFireNotMethod); no shared dispatch trait exists across crates'
//! `Machine<P>` for the same reason a shared `process_input` doesn't
//! (R-ProcessInputNoSharedTrait).

use crate::model::Params;
use gilrs::{Button, Gamepad};
use macroquad::miniquad::conf::{Icon, Platform};
use macroquad::prelude::*;

// spec: §15.2 — fixed values, same for every crate.
pub const DAS_DELAY: f64 = 0.170;
pub const ARR: f64 = 0.050;

/// App id GNOME/Wayland (and X11's `WM_CLASS`) report for this window; must
/// match `install-desktop-icon.sh`'s `StartupWMClass` for Wayland's
/// taskbar/alt-tab icon, since `miniquad`'s Wayland backend ignores
/// `Conf::icon` pixels (only its X11 backend uses them).
pub const LINUX_WM_CLASS: &str = "tetris";

/// spec: §15.2 — window/platform setup (D-Window): fullscreen at startup,
/// `Esc` is the only way to quit. `platform` uses macroquad's defaults
/// except `linux_wm_class`; confirmed working fullscreen on Wayland as-is.
pub fn window_conf() -> Conf {
    Conf {
        window_title: "Tetris".to_owned(),
        fullscreen: false,
        icon: Some(tetris_icon()),
        platform: Platform {
            linux_wm_class: LINUX_WM_CLASS,
            ..Default::default()
        },
        ..Default::default()
    }
}

/// Rasterizes a S-shaped mark at each icon side length `miniquad` wants
/// (16/32/64), sampling one pixel center per cell against the four 5x5
/// squares in the 16x16 mark — exact since every edge falls on a
/// quarter-unit boundary, which 16/32/64 all evenly divide.
fn rasterize_mark(side: usize) -> Vec<u8> {
    const SQUARES: [(f64, f64); 4] = [(0.0, 2.75), (5.5, 2.75), (5.5, 8.25), (11.0, 8.25)];
    const SQUARE_SIDE: f64 = 5.0;
    const COLOR: [u8; 4] = [0xfb, 0x49, 0x34, 0xff];

    let mut pixels = vec![0u8; side * side * 4];
    for y in 0..side {
        for x in 0..side {
            let ux = (x as f64 + 0.5) * 16.0 / side as f64;
            let uy = (y as f64 + 0.5) * 16.0 / side as f64;
            let hit = SQUARES.iter().any(|&(sx, sy)| {
                ux >= sx && ux < sx + SQUARE_SIDE && uy >= sy && uy < sy + SQUARE_SIDE
            });
            if hit {
                let i = (y * side + x) * 4;
                pixels[i..i + 4].copy_from_slice(&COLOR);
            }
        }
    }
    pixels
}

fn tetris_icon() -> Icon {
    Icon {
        small: rasterize_mark(16).try_into().unwrap(),
        medium: rasterize_mark(32).try_into().unwrap(),
        big: rasterize_mark(64).try_into().unwrap(),
    }
}

/// spec: §15.2 — physical key currently bound to Cw/Ccw's logical letters
/// `x`/`z` (D17, D-Logical-Keys), tracked at runtime since it depends on
/// the system keyboard layout. Left/Right/Down use the fixed arrow keys.
#[derive(Default)]
pub struct LogicalKeys {
    pub cw: Option<KeyCode>,
    pub ccw: Option<KeyCode>,
}

impl LogicalKeys {
    /// Updates the Cw/Ccw binding from this frame's newly-pressed key and
    /// character stream. Ambiguous frames (not exactly one new key) are
    /// skipped (R-LogicalKeysEdgeCase); checks `get_keys_pressed()`'s
    /// `HashSet` length directly rather than collecting it first
    /// (R-LogicalKeysHashSet).
    pub fn update(&mut self) {
        let pressed_now = get_keys_pressed();
        while let Some(c) = get_char_pressed() {
            if pressed_now.len() == 1 {
                let kc = *pressed_now.iter().next().expect("len() == 1 checked above");
                match c.to_ascii_lowercase() {
                    'x' => self.cw = Some(kc),
                    'z' => self.ccw = Some(kc),
                    _ => {}
                }
            }
        }
    }
}

pub struct RepeatTimer {
    pub pressed_at: f64,
    pub last_fire: f64,
}

impl RepeatTimer {
    pub fn new(now: f64) -> Self {
        RepeatTimer {
            pressed_at: now,
            last_fire: now,
        }
    }
}

/// spec: §15.2 — `Instance::piece_all()[macroquad::rand::gen_range(0,
/// Instance::piece_all().len())]`, generic over `P`.
pub fn random_piece<P: Params>() -> P::Piece {
    let all = P::piece_all();
    all[macroquad::rand::gen_range(0usize, all.len())]
}

/// spec: §15.2 — the model's five input actions (D17). `fire` is a free
/// function rather than a method here, by design (R-ActionFireNotMethod).
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Action {
    Left,
    Right,
    Down,
    Cw,
    Ccw,
}

impl Action {
    pub const ALL: [Action; 5] = [
        Action::Left,
        Action::Right,
        Action::Down,
        Action::Cw,
        Action::Ccw,
    ];

    pub fn repeats(self) -> bool {
        matches!(self, Action::Left | Action::Right | Action::Down)
    }

    // spec: §15.2 — bindings table (D17, D-Logical-Keys).
    pub fn key(self, logical: &LogicalKeys) -> Option<KeyCode> {
        match self {
            Action::Left => Some(KeyCode::Left),
            Action::Right => Some(KeyCode::Right),
            Action::Down => Some(KeyCode::Down),
            Action::Cw => logical.cw,
            Action::Ccw => logical.ccw,
        }
    }

    // spec: §15.2 — gamepad "button N" follows the standard controller
    // ordering: button 0 = South, button 1 = East.
    pub fn gamepad_button(self) -> Button {
        match self {
            Action::Left => Button::DPadLeft,
            Action::Right => Button::DPadRight,
            Action::Down => Button::DPadDown,
            Action::Cw => Button::East,   // button 1
            Action::Ccw => Button::South, // button 0
        }
    }

    /// spec: §15.2 — merges keyboard (`is_key_down`, D-Logical-Keys for
    /// Cw/Ccw) and gamepad (`is_pressed`) readings into one held/not-held
    /// result. `pad` is looked up once per frame by the caller, not
    /// per-action (R-GilrsPerFrameLookup).
    pub fn is_held(self, logical: &LogicalKeys, pad: Option<Gamepad<'_>>) -> bool {
        self.key(logical).is_some_and(is_key_down)
            || pad.is_some_and(|p| p.is_pressed(self.gamepad_button()))
    }

    /// Edge-triggered reading, used only for the restart check. Keyboard
    /// uses `is_key_pressed`; gamepad has no last-frame cache available
    /// here, so it falls back to "held" — harmless for a restart check,
    /// since this path isn't reached again until the next game over.
    pub fn just_pressed(self, logical: &LogicalKeys, pad: Option<Gamepad<'_>>) -> bool {
        self.key(logical).is_some_and(is_key_pressed)
            || pad.is_some_and(|p| p.is_pressed(self.gamepad_button()))
    }
}

pub fn any_action_just_pressed(logical: &LogicalKeys, pad: Option<Gamepad<'_>>) -> bool {
    Action::ALL.iter().any(|a| a.just_pressed(logical, pad))
}
