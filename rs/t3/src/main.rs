#![deny(warnings)]
//! spec: main.rs — entry point (§15, `implementation.md`).

use gilrs::{Gamepad, Gilrs};
use macroquad::prelude::*;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use t1::misc::{random_piece, window_conf, LogicalKeys, RepeatTimer, ARR, DAS_DELAY};
use t1::model::Params;
use t3::instance;
use t3::misc::{any_action_just_pressed, Action};
use t3::model::{self, Machine};
use t3::view;

type Instance = instance::Tetris;

// spec: t2/implementation.md §15.9 — embedded TTF (JetBrains Mono, OFL
// 1.1, see `assets/OFL.txt`) so text rasterizes as vector glyphs, not
// macroquad's bitmap font. `include_bytes!` path is relative to this file,
// not `CARGO_MANIFEST_DIR`; every crate reaches `assets/` via `../../`.
const FONT_BYTES: &[u8] = include_bytes!("../../assets/JetBrainsMono-Regular.ttf");

// spec: §15.1 (t2/implementation.md) — classic-gravity fall-speed curve,
// unchanged by T3 (`T3.v` places no requirement on fall timing either).
const BASE_PERIOD_SECS: f64 = 1.0;
const MIN_PERIOD_SECS: f64 = 0.016;
const EPS: f64 = 1e-6;

fn fall_period(level: u64) -> f64 {
    let base = (0.8 - (level as f64 - 1.0) * 0.007).max(EPS);
    let secs = base.powf(level as f64 - 1.0);
    (BASE_PERIOD_SECS * secs).max(MIN_PERIOD_SECS)
}

const BANNER_SECS: f64 = 1.2;

/// spec: §15 — routes through `t3::model::Machine`'s wrapper methods so
/// hold/swapped stay in sync with every action.
/// spec: R-ActionSharedT4 — `Action` is shared with `t4`; only `fire`'s
/// dispatch is per-crate.
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
        Action::Hold => {
            machine.hold_piece(random_piece::<P>());
        }
    }
}

/// spec: §15.1/§15.2 (t2/implementation.md) — level→fall-speed schedule +
/// transient banner, unchanged from T2's `RunState`; T3 adds no state here
/// (`render` reads `machine.swapped` fresh every frame instead).
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

/// spec: §15.2 (t2/implementation.md) — level-change rescheduling + banner
/// capture; runs after every state-changing input including `Hold`, for
/// uniformity, though a hold changes none of the fields inspected here.
/// spec: R-AfterActionHop — reads one hop deeper (`machine.s2.*`) than
/// T2's `after_action`, matching this floor's extra nesting.
fn after_action<P: Params>(machine: &Machine<P>, now: f64, run: &mut RunState) {
    if machine.s2.level != run.prev_level {
        run.current_gravity_period = fall_period(machine.s2.level);
        run.prev_level = machine.s2.level;
        run.last_fall = now;
    }

    if machine.s2.total_cleared_lines > run.prev_total_cleared_lines {
        run.banner = Some(view::Banner {
            combo: machine.s2.combo,
            perfect_clear: machine.s2.perfect_clear,
            t: now,
        });
    }
    run.prev_total_cleared_lines = machine.s2.total_cleared_lines;
}

/// spec: t1/implementation.md §15.5 — merged held-state + shared DAS
/// engine (as T1/T2), plus restart (also resetting `RunState`) and the
/// `after_action` call every action path goes through. `Hold` is just
/// another `Action::ALL` entry, tap-edge branch — same dispatch as
/// `Cw`/`Ccw`, no special-casing.
fn process_input<P: Params>(
    machine: &mut Machine<P>,
    repeat: &mut HashMap<Action, RepeatTimer>,
    logical: &LogicalKeys,
    pad: Option<Gamepad<'_>>,
    run: &mut RunState,
) {
    let now = get_time();
    if machine.s2.s1.gameover {
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
        model::check_axioms::<Instance>(); // spec: R-CheckAxiomsOnce — once, before first Machine (§7)
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
        if !machine.s2.s1.gameover && now - run.last_fall >= run.current_gravity_period {
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
