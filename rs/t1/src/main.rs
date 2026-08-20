#![deny(warnings)]
//! spec: main.rs — entry point (§15, `implementation.md`).

use gilrs::{Gamepad, Gilrs};
use macroquad::prelude::*;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use t1::instance;
use t1::misc::{random_piece, window_conf, Action, LogicalKeys, RepeatTimer, ARR, DAS_DELAY};
use t1::model::{self, Machine, Params};
use t1::view;

type Instance = instance::Tetris;

// spec: §15.4, D16 — fall period is a UI-pacing constant, not derived
// from the model.
const FALL_PERIOD_SECS: f64 = 1.0;

/// spec: §15.5 — one input action (`Action`, D17). `fire` is a free
/// function, not an `Action` method (R-ActionFireNotMethod): its dispatch
/// target is per-crate.
fn fire<P: Params>(action: Action, machine: &mut Machine<P>) {
    match action {
        Action::Left => {
            machine.move_piece(0, -1);
        }
        Action::Right => {
            machine.move_piece(0, 1);
        }
        Action::Down => {
            machine.fall_step(random_piece::<P>());
        }
        Action::Cw => {
            machine.rotate_piece(true);
        }
        Action::Ccw => {
            machine.rotate_piece(false);
        }
    }
}

fn any_action_just_pressed(logical: &LogicalKeys, pad: Option<Gamepad<'_>>) -> bool {
    Action::ALL.iter().any(|a| a.just_pressed(logical, pad))
}

/// spec: §15.5 — merged held-state + shared DAS engine: fires once on
/// press, then DAS-delays before auto-repeat; non-repeating actions fire
/// once per press. `pad` is looked up once per frame by the caller
/// (R-GilrsPerFrameLookup). Uses `HashMap::entry` for the repeat
/// bookkeeping instead of separate get/insert/remove calls
/// (R-ProcessInputEntryAPI).
fn process_input<P: Params>(
    machine: &mut Machine<P>,
    repeat: &mut HashMap<Action, RepeatTimer>,
    logical: &LogicalKeys,
    pad: Option<Gamepad<'_>>,
) {
    if machine.gameover {
        // no separate "waiting for restart" flag: `gameover` is monotone
        // once true, so it alone gates the restart check
        if any_action_just_pressed(logical, pad) {
            *machine = Machine::new(random_piece::<P>(), random_piece::<P>);
        }
        repeat.clear();
        return;
    }
    let now = get_time();
    for action in Action::ALL {
        let is_held = action.is_held(logical, pad);
        match repeat.entry(action) {
            Entry::Vacant(e) => {
                if is_held {
                    fire(action, machine);
                    e.insert(RepeatTimer::new(now)); // one-shot "already fired" marker for non-repeating actions
                }
            }
            Entry::Occupied(mut e) => {
                if !is_held {
                    e.remove();
                } else if action.repeats()
                    && now - e.get().pressed_at >= DAS_DELAY
                    && now - e.get().last_fire >= ARR
                {
                    fire(action, machine);
                    e.get_mut().last_fire = now;
                }
                // else: held but either non-repeating (already fired,
                // waiting for release) or still within the DAS/ARR window.
            }
        }
    }
}

/// spec: §15.4 — macroquad entry point. Per-frame state lives in this
/// async fn's own locals, never a `static`. Runs fullscreen (D-Window);
/// `Esc` quits.
#[macroquad::main(window_conf)]
async fn main() {
    if model::CHECK_AXIOMS {
        model::check_axioms::<Instance>(); // once, before touching Instance (§7)
    }

    let constants = view::RenderConstants {
        hm: Instance::initial_main_grid().len() as i64,
        wm: Instance::initial_main_grid()[0].len() as i64,
        pw: Instance::PW,
        fy: Instance::FY,
        fx: Instance::FX,
        fh: Instance::forbidden_grid().len() as i64,
        fw: Instance::forbidden_grid()[0].len() as i64,
    };

    let mut machine =
        Machine::<Instance>::new(random_piece::<Instance>(), random_piece::<Instance>);
    let mut key_repeat: HashMap<Action, RepeatTimer> = HashMap::new();
    let mut logical_keys = LogicalKeys::default();
    // spec: §15.4, R-GilrsFallback — a failed `Gilrs::new()` leaves
    // gamepad support disabled for the run rather than aborting startup.
    let mut gilrs = match Gilrs::new() {
        Ok(g) => Some(g),
        Err(e) => {
            eprintln!("gamepad support disabled ({e}); continuing keyboard-only");
            None
        }
    };
    let mut last_fall = get_time();

    loop {
        if is_key_pressed(KeyCode::Escape) {
            macroquad::miniquad::window::order_quit();
            return; // window teardown isn't necessarily instant (R-WindowTeardown)
        }

        logical_keys.update(); // spec: §15.4, D-Logical-Keys
        if let Some(g) = &mut gilrs {
            while g.next_event().is_some() {} // drain; state is read via gilrs.gamepad(id), not the event stream
        }
        // one gamepad lookup per frame, shared by every action
        // (R-GilrsPerFrameLookup).
        let pad = gilrs
            .as_ref()
            .and_then(|g| g.gamepads().next())
            .map(|(_, pad)| pad);
        process_input(&mut machine, &mut key_repeat, &logical_keys, pad);

        let now = get_time();
        if now - last_fall >= FALL_PERIOD_SECS {
            machine.fall_step(random_piece::<Instance>()); // req-piece-fall
            last_fall = now;
        }

        view::render(&constants, &machine, instance::piece_color);
        next_frame().await;
    }
}
