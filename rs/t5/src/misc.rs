//! spec: main.rs — the `Action` shape for `T5.v` (§15, `implementation.md`):
//! `T3.v`'s six variants (`t3::misc::Action`'s own doc comment) plus `Drop`
//! (req-piece-drop), the first genuinely new player-facing action since
//! `Hold` — unlike `T4.v`, which reused `t3::misc::Action` verbatim.
//! `fire` stays out of this module for the same reason `t1::misc::Action`/
//! `t3::misc::Action` exclude it: the dispatch target is per-crate.

use gilrs::{Button, Gamepad};
use macroquad::prelude::*;
use t1::misc::LogicalKeys;

/// spec: §15 — one input action, `T5.v`'s seven (`T3.v`'s six, plus `Drop`).
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Action {
    Left,
    Right,
    Down,
    Cw,
    Ccw,
    Hold,
    Drop,
}

impl Action {
    pub const ALL: [Action; 7] = [
        Action::Left,
        Action::Right,
        Action::Down,
        Action::Cw,
        Action::Ccw,
        Action::Hold,
        Action::Drop,
    ];

    /// spec: §15.1 — `Drop` is non-repeating, same class as `Hold`/`Cw`/`Ccw`.
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
            Action::Drop => Some(KeyCode::Up),
        }
    }

    /// spec: §15.1 — `DPadUp` for `Drop`, consistent with the existing
    /// D-pad bindings on the repeating directional actions.
    pub fn gamepad_button(self) -> Button {
        match self {
            Action::Left => Button::DPadLeft,
            Action::Right => Button::DPadRight,
            Action::Down => Button::DPadDown,
            Action::Cw => Button::East,
            Action::Ccw => Button::South,
            Action::Hold => Button::North,
            Action::Drop => Button::DPadUp,
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
