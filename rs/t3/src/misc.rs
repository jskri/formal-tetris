//! spec: main.rs — the `Action` shape shared by every crate from `T3.v`
//! onward (§15): `T3.v` adds `Hold` to `T1.v`/`T2.v`'s five events.
//! R-ActionSharedT4: this six-variant set, its bindings, and its
//! held/just-pressed reads are reused unchanged by t4; `fire` is
//! deliberately not declared here since dispatch is per-crate.

use gilrs::{Button, Gamepad};
use macroquad::prelude::*;
use t1::misc::LogicalKeys;

/// spec: §15 — one input action, `T3.v`'s six (`T1.v`/`T2.v`'s five, plus
/// `Hold`).
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Action {
    Left,
    Right,
    Down,
    Cw,
    Ccw,
    Hold,
}

impl Action {
    pub const ALL: [Action; 6] = [
        Action::Left,
        Action::Right,
        Action::Down,
        Action::Cw,
        Action::Ccw,
        Action::Hold,
    ];

    /// spec: §15.1 — `Hold` is non-repeating, same class as `Cw`/`Ccw`: a
    /// discrete choice per press, not a held direction (even though
    /// `req-hold-limit` already makes a redundant attempt a no-op).
    pub fn repeats(self) -> bool {
        matches!(self, Action::Left | Action::Right | Action::Down)
    }

    pub fn key(self, logical: &LogicalKeys) -> Option<KeyCode> {
        match self {
            Action::Left => Some(KeyCode::Left),
            Action::Right => Some(KeyCode::Right),
            Action::Down => Some(KeyCode::Down),
            Action::Cw => logical.cw,
            Action::Ccw => logical.ccw,
            Action::Hold => Some(KeyCode::Space),
        }
    }

    /// spec: §15.1 — gamepad button index 3: `Button::North` under gilrs's
    /// standard-gamepad mapping (South=0, East=1, West=2, North=3).
    pub fn gamepad_button(self) -> Button {
        match self {
            Action::Left => Button::DPadLeft,
            Action::Right => Button::DPadRight,
            Action::Down => Button::DPadDown,
            Action::Cw => Button::East,
            Action::Ccw => Button::South,
            Action::Hold => Button::North,
        }
    }

    pub fn is_held(self, logical: &LogicalKeys, pad: Option<Gamepad<'_>>) -> bool {
        self.key(logical).is_some_and(is_key_down)
            || pad.is_some_and(|p| p.is_pressed(self.gamepad_button()))
    }

    pub fn just_pressed(self, logical: &LogicalKeys, pad: Option<Gamepad<'_>>) -> bool {
        self.key(logical).is_some_and(is_key_pressed)
            || pad.is_some_and(|p| p.is_pressed(self.gamepad_button()))
    }
}

pub fn any_action_just_pressed(logical: &LogicalKeys, pad: Option<Gamepad<'_>>) -> bool {
    Action::ALL.iter().any(|a| a.just_pressed(logical, pad))
}
