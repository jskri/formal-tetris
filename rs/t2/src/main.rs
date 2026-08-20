#![deny(warnings)]
//! main.rs — entry point (§15, `implementation.md`).

use gilrs::{Gamepad, Gilrs};
use macroquad::prelude::*;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use t1::misc::{random_piece, window_conf, Action, LogicalKeys, RepeatTimer, ARR, DAS_DELAY};
use t1::model::Params;
use t2::instance;
use t2::model::{self, Machine};
use t2::view;

type Instance = instance::Tetris;

// spec: §15.9 — embedded TTF for vector-quality text at any size.
// JetBrains Mono, SIL Open Font License 1.1 — see `assets/OFL.txt`.
const FONT_BYTES: &[u8] = include_bytes!("../../assets/JetBrainsMono-Regular.ttf");

// spec: §15.1 — classic-gravity fall-speed curve.
const BASE_PERIOD_SECS: f64 = 1.0; // level 1 (1.0 × 0.8^0)
const MIN_PERIOD_SECS: f64 = 0.016; // floor (~one 60 Hz frame)
const EPS: f64 = 1e-6; // keeps the base positive for very high levels

/// spec: §15.1 — time-per-cell(level) = (0.8 − (level−1)·0.007)^(level−1), floored.
/// UI-pacing only (D16-style: no `Params`/`Machine` counterpart).
fn fall_period(level: u64) -> f64 {
    let base = (0.8 - (level as f64 - 1.0) * 0.007).max(EPS);
    let secs = base.powf(level as f64 - 1.0);
    (BASE_PERIOD_SECS * secs).max(MIN_PERIOD_SECS)
}

// spec: §15.2 — combo / perfect-clear banner visible duration.
const BANNER_SECS: f64 = 1.2;

/// spec: §15 — routes through `t2::model::Machine`'s wrapper methods so
/// score/level/combo/perfectClear/totalClearedLines stay in sync with every
/// action. Free function rather than a method on `Action`: `Action` is
/// shared with T1, but its dispatch target isn't.
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

/// spec: §15.2 — level→fall-speed schedule + transient banner, kept
/// together as UI-only state rather than threaded through `Machine`.
struct RunState {
    prev_level: u64,
    current_gravity_period: f64,
    last_fall: f64,
    prev_total_cleared_lines: u64,
    banner: Option<view::Banner>,
}

impl RunState {
    fn fresh(now: f64) -> Self {
        RunState {
            prev_level: 1,
            current_gravity_period: fall_period(1),
            last_fall: now,
            prev_total_cleared_lines: 0,
            banner: None,
        }
    }
}

/// spec: §15.2 — level-change rescheduling + banner capture, run after
/// every state-changing input, on the main loop's own clock. Clear
/// detection diffs `total_cleared_lines` rather than reading
/// `s1.cleared_lines` alone (§9).
fn after_action<P: Params>(machine: &Machine<P>, now: f64, run: &mut RunState) {
    if machine.level != run.prev_level {
        run.current_gravity_period = fall_period(machine.level);
        run.prev_level = machine.level;
        run.last_fall = now; // faster gravity takes effect now, discarding
    } // whatever had already accumulated toward the previous period

    if machine.total_cleared_lines > run.prev_total_cleared_lines {
        run.banner = Some(view::Banner {
            combo: machine.combo,
            perfect_clear: machine.perfect_clear,
            t: now,
        });
    }
    run.prev_total_cleared_lines = machine.total_cleared_lines;
}

/// spec: §15.4 — merged held-state + shared DAS engine (as T1's), plus
/// §15.3's restart, extended to also reset `RunState`, and the
/// `after_action` call every action path goes through.
fn process_input<P: Params>(
    machine: &mut Machine<P>,
    repeat: &mut HashMap<Action, RepeatTimer>,
    logical: &LogicalKeys,
    pad: Option<Gamepad<'_>>,
    run: &mut RunState,
) {
    let now = get_time();
    if machine.s1.gameover {
        if any_action_just_pressed(logical, pad) {
            *machine = Machine::new(random_piece::<P>(), random_piece::<P>);
            *run = RunState::fresh(now);
        }
        repeat.clear();
        return;
    }
    for action in Action::ALL {
        let is_held = action.is_held(logical, pad);
        match repeat.entry(action) {
            Entry::Vacant(e) => {
                if is_held {
                    fire(action, machine);
                    e.insert(RepeatTimer::new(now));
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
            }
        }
    }
    after_action(machine, now, run);
}

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
    let mut gilrs = match Gilrs::new() {
        Ok(g) => Some(g),
        Err(e) => {
            eprintln!("gamepad support disabled ({e}); continuing keyboard-only");
            None
        }
    };
    let mut run = RunState::fresh(get_time());
    let font = load_ttf_font_from_bytes(FONT_BYTES).expect("embedded font must parse");

    loop {
        if is_key_pressed(KeyCode::Escape) {
            macroquad::miniquad::window::order_quit();
            return;
        }

        logical_keys.update();
        if let Some(g) = &mut gilrs {
            while g.next_event().is_some() {}
        }
        let pad = gilrs
            .as_ref()
            .and_then(|g| g.gamepads().next())
            .map(|(_, pad)| pad);
        process_input(&mut machine, &mut key_repeat, &logical_keys, pad, &mut run);

        let now = get_time();
        if !machine.s1.gameover && now - run.last_fall >= run.current_gravity_period {
            run.last_fall = now;
            machine.fall_step(random_piece::<Instance>()); // req-piece-fall
            after_action(&machine, now, &mut run);
        }

        if let Some(b) = &run.banner {
            if now - b.t > BANNER_SECS {
                run.banner = None;
            }
        }

        view::render(
            &constants,
            &machine,
            instance::piece_color,
            run.banner.as_ref(),
            Some(&font),
        );
        next_frame().await;
    }
}
