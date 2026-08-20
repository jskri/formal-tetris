#![deny(warnings)]
//! spec: main.rs — entry point (§15, `implementation.md`).

use gilrs::{Gamepad, Gilrs};
use macroquad::prelude::*;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use t1::misc::{random_piece, window_conf, LogicalKeys, RepeatTimer, ARR, DAS_DELAY};
use t1::model::Params as T1Params; // needed for the concrete Instance::… calls below:
                                   // a concrete type's associated items still need the
                                   // declaring trait imported directly, unlike a generic
                                   // P: Params bound which reaches them via the supertrait
use t6::instance;
use t6::misc::{any_action_just_pressed, Action};
use t6::model::{Machine, Params, T6MachineExt};
use t6::view;

type Instance = instance::Tetris;

// spec: t3/implementation.md §15.3 — embedded TTF, JetBrains Mono (OFL 1.1,
// see assets/OFL.txt). include_bytes!'s path is relative to this file, not
// CARGO_MANIFEST_DIR; assets/ lives once at the workspace root.
const FONT_BYTES: &[u8] = include_bytes!("../../assets/JetBrainsMono-Regular.ttf");

// spec: §15.1 (t2/implementation.md) — classic-gravity fall-speed curve,
// unchanged by T6.
const BASE_PERIOD_SECS: f64 = 1.0;
const MIN_PERIOD_SECS: f64 = 0.016;
const EPS: f64 = 1e-6;

fn fall_period(level: u64) -> f64 {
    let base = (0.8 - (level as f64 - 1.0) * 0.007).max(EPS);
    let secs = base.powf(level as f64 - 1.0);
    (BASE_PERIOD_SECS * secs).max(MIN_PERIOD_SECS)
}

const BANNER_SECS: f64 = 1.2;

/// spec: §15.2 — `Cw`/`Ccw` try a plain rotation, then a kick on failure;
/// a `main.rs`-level orchestration decision, not a `T6.v` definition (§1).
fn rotate<P: Params>(machine: &mut Machine<P>, cw: bool) -> bool {
    machine.rotate_piece(cw) || machine.rotate_kick_piece(cw)
}

/// spec: §15 — dispatches `Action` via `Machine<P>`'s methods (§1) plus
/// `rotate` above for `Cw`/`Ccw`. Free function rather than a method on
/// `Action`: its dispatch target isn't shared with any other crate either.
fn fire<P: Params>(action: Action, machine: &mut Machine<P>) {
    match action {
        Action::Left => {
            machine.move_piece(0, -1);
        }
        Action::Right => {
            machine.move_piece(0, 1);
        }
        Action::Down => {
            machine.fall_step(&shuffle_bag::<P>());
        }
        Action::Cw => {
            rotate(machine, true);
        }
        Action::Ccw => {
            rotate(machine, false);
        }
        Action::Hold => {
            machine.hold_piece(&shuffle_bag::<P>());
        }
        Action::Drop => {
            machine.drop_piece(&shuffle_bag::<P>());
        }
    }
}

/// spec: §15.1 (`t4/implementation.md`) — req-preview-init's fair
/// randomization source, Fisher–Yates over the full `P::piece_all()`.
/// Re-declared rather than imported: `main.rs` is a binary, not part of
/// any crate's library surface (§15.3).
fn shuffle_bag<P: Params>() -> Vec<P::Piece> {
    let mut a: Vec<P::Piece> = P::piece_all().to_vec();
    for i in (1..a.len()).rev() {
        let j = macroquad::rand::gen_range(0usize, i + 1);
        a.swap(i, j);
    }
    a
}

/// spec: §15.2 (`t4/implementation.md`) — `bags_fn`'s referential-consistency
/// requirement, satisfied by memoization. A fresh closure per game (startup
/// and every restart), not a module-level cache, so bags never leak across
/// restarts.
fn make_bags_fn<P: Params>() -> impl FnMut(u64) -> Vec<P::Piece> {
    let mut bags: Vec<Vec<P::Piece>> = Vec::new();
    move |i: u64| {
        let i = i as usize;
        while bags.len() <= i {
            bags.push(shuffle_bag::<P>());
        }
        bags[i].clone()
    }
}

/// spec: §15.1/§15.2 (t2/implementation.md) — the level→fall-speed schedule
/// and the transient banner, unchanged in shape from every prior model's
/// `RunState`; T6 adds nothing here (§6.2 — no new field, no new getter).
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
/// capture, run after every state-changing input including the new kick
/// path. Field-path nesting unchanged from T5 (§6.2).
fn after_action<P: Params>(machine: &Machine<P>, now: f64, run: &mut RunState) {
    if machine.s4.s3.s2.level != run.prev_level {
        run.current_gravity_period = fall_period(machine.s4.s3.s2.level);
        run.prev_level = machine.s4.s3.s2.level;
        run.last_fall = now;
    }

    if machine.s4.s3.s2.total_cleared_lines > run.prev_total_cleared_lines {
        run.banner = Some(view::Banner {
            combo: machine.s4.s3.s2.combo,
            perfect_clear: machine.s4.s3.s2.perfect_clear,
            t: now,
        });
    }
    run.prev_total_cleared_lines = machine.s4.s3.s2.total_cleared_lines;
}

/// spec: §15.3 — merged held-state + shared DAS engine, as T1–T5's, plus
/// restart and the `after_action` call every action path goes through.
/// `Cw`/`Ccw` are picked up by the same tap-edge/DAS branches with no
/// further change — `rotate` (above) is what tries the kick, not this
/// dispatch loop.
fn process_input<P: Params>(
    machine: &mut Machine<P>,
    repeat: &mut HashMap<Action, RepeatTimer>,
    logical: &LogicalKeys,
    pad: Option<Gamepad<'_>>,
    run: &mut RunState,
) {
    let now = get_time();
    if machine.s4.s3.s2.s1.gameover {
        if any_action_just_pressed(logical, pad) {
            *machine = Machine::new(make_bags_fn::<P>(), random_piece::<P>);
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
    if t5::model::CHECK_AXIOMS {
        t5::model::check_axioms::<Instance>(); // once, before touching Instance (§7)
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
        Machine::<Instance>::new(make_bags_fn::<Instance>(), random_piece::<Instance>);
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
        if !machine.s4.s3.s2.s1.gameover && now - run.last_fall >= run.current_gravity_period {
            run.last_fall = now;
            machine.fall_step(&shuffle_bag::<Instance>()); // req-piece-fall
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
