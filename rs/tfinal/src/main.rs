#![deny(warnings)]
//! `final/` — entry point. Drives two engines: single-player directly on
//! `t6::model::Machine<t1::instance::Tetris>`, multiplayer through
//! `t7::session::Session` driving `t7::model::Machine<Instance>`. The
//! screen/menu/lobby machinery (`t7::app`/`t7::text`) is reused as a library
//! module; this file's own additions are procedural sound (`sound.rs`),
//! line-clear/garbage animations (`anim.rs`), a single-player hall of fame
//! (`highscores.rs`), and the hooks threading those through the shared
//! per-action dispatch (`fire_single_with_effects`/`fire_with_effects`) and
//! gravity ticks.
//!
//! Bags are per-player and purely local, unchanged from `t7`.

mod anim;
mod highscores;
mod sound;

use gilrs::{Gamepad, Gilrs};
use macroquad::prelude::*;
use std::collections::HashMap;
use std::time::SystemTime;
use t1::misc::{window_conf, LogicalKeys, RepeatTimer};
use t1::model::Params;
use t6::model::T6MachineExt as _;
use t7::app::{
    after_action, draw_gameover_filler_overlay, draw_host_lobby, draw_host_lost, draw_join_lobby,
    draw_mode_select, draw_role_select, draw_waiting_overlay, draw_winner_screen, fire_single,
    fresh_single, poll_menu_nav, process_input, step_host_lobby, step_host_lost, step_join_lobby,
    step_mode_select, step_playing_transition, step_role_select, step_waiting_session, step_winner,
    AfterActionEvents, GamepadEdges, HostLobby, HostLobbyOutcome, JoinLobby, JoinLobbyOutcome,
    ModeSelectOutcome, PlayingTransition, RoleSelectOutcome, RunState, SingleInstance, TextCursor,
    WaitingOutcome, Winner, WinnerOutcome, BODY_COLOR, CODE_COLOR, HINT_COLOR, TITLE_COLOR,
};
use t7::misc::Action;
use t7::session::{Instance, Session};
use t7::text::{drive_backspace_repeat, poll_text_edit, TextInput};
use t7::view;

use sound::{Sfx, SoundEngine};

const FONT_BYTES: &[u8] = include_bytes!("../../assets/JetBrainsMono-Regular.ttf");

const BANNER_SECS: f64 = 1.2;

/// R-SPGameoverLockout: delay before single-player's own gameover screen
/// accepts a hall-of-fame prompt or restart.
const SP_GAMEOVER_LOCKOUT_SECS: f64 = 1.0;

/// The filler machine's own restart-on-keypress lockout once it tops out —
/// distinct from `t7::app::GAMEOVER_FILLER_DELAY_SECS`, which gates entry
/// *into* the filler after the real match's gameover.
const FILLER_GAMEOVER_LOCKOUT_SECS: f64 = 1.0;

const HOF_NAME_MAX_LEN: usize = 20;

/// Plays the sound effects tied to a clear's cumulative outcome (level-up,
/// clear/perfect-clear/combo), read off `t7::app::after_action`'s event
/// report rather than re-detected here.
fn play_after_action_sfx(events: &AfterActionEvents, sound: &SoundEngine) {
    if events.level_up.is_some() {
        sound.play(Sfx::LevelUp);
    }
    if let Some(c) = &events.clear {
        sound.play(Sfx::Clear(c.lines.clamp(1, 4) as u8));
        if c.perfect_clear {
            sound.play(Sfx::PerfectClear);
        }
        if c.combo > 1 {
            sound.play(Sfx::Combo(c.combo.min(10) as u8));
        }
    }
}

// ── App state: the screen machine ────────────────────────────────────────

enum App {
    ModeSelect,
    RoleSelect,
    Single(SpGame),
    Host(HostLobby),
    Join(JoinLobby),
    Waiting(Waiting),
    Playing(Playing),
    Winner(Winner),
    HostLost,
}

/// R-SPPostFlow: single-player's post-gameover screen sequence.
enum SpPost {
    None,
    NameEntry {
        score: u64,
        level: u64,
        lines: u64,
        name: TextInput,
        backspace_repeat: Option<RepeatTimer>,
    },
    HallOfFame {
        entries: Vec<highscores::Entry>,
        highlight: Option<u64>,
        notice: bool,
    },
}

struct SpGame {
    machine: t6::model::Machine<SingleInstance>,
    clear_anim: Option<anim::ClearAnim<SingleInstance>>,
    gameover_since: Option<f64>,
    post: SpPost,
}

impl SpGame {
    fn fresh() -> Self {
        SpGame {
            machine: fresh_single(),
            clear_anim: None,
            gameover_since: None,
            post: SpPost::None,
        }
    }
}

/// The waiting room (`S6`): a `t6::model::Machine` filler game, plus its own
/// clear-flash/gameover-lockout state.
struct Waiting {
    session: Session,
    filler: t6::model::Machine<SingleInstance>,
    filler_clear_anim: Option<anim::ClearAnim<SingleInstance>>,
    filler_gameover_since: Option<f64>,
}

/// `S7`, and `S8` when `filler` is `Some`. During `S8` the real
/// `t7::model::Machine` inside `session` is kept alive headless.
struct Playing {
    session: Session,
    filler: Option<t6::model::Machine<SingleInstance>>,
    own_gameover_since: Option<f64>,
    filler_clear_anim: Option<anim::ClearAnim<SingleInstance>>,
    filler_gameover_since: Option<f64>,
    mp_clear_anim: Option<anim::ClearAnim<Instance>>,
    mp_garbage_anim: Option<anim::GarbageAnim>,
    /// Last frame's `connected_view`, indexed by player — diffed for a
    /// `true → false` transition to fire `Sfx::Disconnect`. Starts empty,
    /// so the first frame just initializes it.
    connected_prev: Vec<bool>,
}

/// The name this peer will announce, falling back to `fallback` when the
/// field is blank.
fn entered_name(field: &TextInput, fallback: &str) -> String {
    let t = field.text.trim();
    if t.is_empty() {
        fallback.to_owned()
    } else {
        t.to_owned()
    }
}

/// True while something other than `update_logical_keys` is going to read
/// `get_char_pressed()` this frame — gates that other reader's exclusive
/// access to the queue (see `update_logical_keys`) and the mute key, so
/// typing into a text field never toggles mute mid-word. Covers `Single`'s
/// name-entry field and Hall-of-Fame alnum-restart check, plus `Host`/
/// `Join`'s text-entry fields; for the latter two, knowing the screen is
/// `Host`/`Join` is enough — their step functions poll the text-edit queue
/// unconditionally regardless of which field has focus.
fn char_queue_reserved(app: &App) -> bool {
    matches!(app, App::Host(_) | App::Join(_))
        || matches!(app, App::Single(game) if !matches!(game.post, SpPost::None))
}

// ── Rendering: single-player's own screens ──────────────────────────────

/// Single-player's own name-entry sub-screen — a fresh high score, entered
/// before the hall-of-fame list is shown.
fn draw_name_entry(score: u64, level: u64, lines: u64, name: &TextInput, font: Option<&Font>) {
    clear_background(t2::view::BG_COLOR);
    let mut c = TextCursor::new();
    c.big("NEW HIGH SCORE!", TITLE_COLOR, font);
    c.gap();
    c.line(
        &format!("Score {score}   Level {level}   Lines {lines}"),
        BODY_COLOR,
        font,
    );
    c.gap();
    c.field("Name", &name.text, true, true, true, font);
    c.gap();
    c.line("[Enter] submit", HINT_COLOR, font);
}

fn draw_hall_of_fame(
    entries: &[highscores::Entry],
    highlight: Option<u64>,
    notice: bool,
    font: Option<&Font>,
) {
    clear_background(t2::view::BG_COLOR);
    let mut c = TextCursor::new();
    c.big("HALL OF FAME", TITLE_COLOR, font);
    c.gap();
    if notice {
        c.line("Scores can't be saved right now.", HINT_COLOR, font);
        c.gap();
    }
    if entries.is_empty() {
        c.line("No scores yet — go set one!", BODY_COLOR, font);
    } else {
        c.line(
            &format!(
                "{:<4} {:<w$} {:>8} {:>6} {:>6}",
                "",
                "Player",
                "Score",
                "Level",
                "Lines",
                w = HOF_NAME_MAX_LEN
            ),
            HINT_COLOR,
            font,
        );
        for (i, e) in entries.iter().enumerate() {
            let color = if Some(e.score) == highlight {
                CODE_COLOR
            } else {
                BODY_COLOR
            };
            c.line(
                &format!(
                    "{:<4} {:<w$} {:>8} {:>6} {:>6}",
                    format!("{}.", i + 1),
                    e.name,
                    e.score,
                    e.level,
                    e.lines,
                    w = HOF_NAME_MAX_LEN
                ),
                color,
                font,
            );
        }
    }
    c.gap();
    c.line("[enter/space] play again   [esc] menu", HINT_COLOR, font);
}

// ── Input ───────────────────────────────────────────────────────────────

/// Learns which physical key currently produces `'x'`/`'z'`/`'m'`
/// (case-insensitive), same technique as `t1::misc::LogicalKeys::update`
/// for Cw/Ccw, extended to Mute. Both must be learned in one pass over
/// `get_char_pressed()`: it's a single-consumption queue, so a separate
/// mute-learning loop in the same frame would race with `LogicalKeys::update`
/// and drain it first. Only call while `!char_queue_reserved(&app)` — another
/// active reader would lose its keystrokes to this loop otherwise.
fn update_logical_keys(logical: &mut LogicalKeys, mute: &mut Option<KeyCode>) {
    let pressed_now = get_keys_pressed();
    while let Some(c) = get_char_pressed() {
        if pressed_now.len() == 1 {
            let kc = *pressed_now.iter().next().expect("len() == 1 checked above");
            match c.to_ascii_lowercase() {
                'x' => logical.cw = Some(kc),
                'z' => logical.ccw = Some(kc),
                'm' => *mute = Some(kc),
                _ => {}
            }
        }
    }
}

/// The filler game shared by the waiting room (`S6`) and the mid-match wait
/// (`S8`): single-player dispatch/gravity/gameover-restart over a
/// `Machine<SingleInstance>` neither screen actually waits on — topping out
/// just restarts on the next keypress once its lockout elapses. Kept local
/// rather than `t7::app::drive_filler_input`, whose gravity tick calls
/// `fall_step` directly instead of going through a caller-supplied
/// `dispatch`; here it must go through `fire_single_with_effects` so a
/// gravity-driven lock is never silent.
#[allow(clippy::too_many_arguments)]
fn drive_filler(
    filler: &mut t6::model::Machine<SingleInstance>,
    key_repeat: &mut HashMap<Action, RepeatTimer>,
    logical_keys: &LogicalKeys,
    pad: Option<Gamepad<'_>>,
    run: &mut RunState,
    now: f64,
    sound: &SoundEngine,
    clear_anim: &mut Option<anim::ClearAnim<SingleInstance>>,
    gameover_since: &mut Option<f64>,
) {
    let gameover = filler.s4.s3.s2.s1.gameover;
    process_input(gameover, key_repeat, logical_keys, pad, now, |action| {
        fire_single_with_effects(action, filler, sound, clear_anim, now)
    });

    if gameover {
        if gameover_since.is_none() {
            sound.play(Sfx::Gameover);
            *gameover_since = Some(now);
        }
        let elapsed = gameover_since.is_some_and(|s| now - s >= FILLER_GAMEOVER_LOCKOUT_SECS);
        if elapsed && t1::misc::any_action_just_pressed(logical_keys, pad) {
            *filler = fresh_single();
            *run = RunState::fresh(now);
            *clear_anim = None;
            *gameover_since = None;
        }
    } else if now - run.last_fall >= run.current_gravity_period {
        run.last_fall = now;
        fire_single_with_effects(Action::Down, filler, sound, clear_anim, now); // req-piece-fall
    }
    let events = after_action(&filler.s4.s3.s2, now, run);
    play_after_action_sfx(&events, sound);
}

/// Single-player dispatch (also used for the shared filler): sound and
/// clear-flash arming layered on `t7::app::fire_single`. R-HookPlacement:
/// hooks fire from `on_result` after the mutating call, except
/// `precompute_clear` (R-ClearPrecompute), which runs before it.
fn fire_single_with_effects(
    action: Action,
    machine: &mut t6::model::Machine<SingleInstance>,
    sound: &SoundEngine,
    clear_anim: &mut Option<anim::ClearAnim<SingleInstance>>,
    now: f64,
) -> bool {
    let s1 = &machine.s4.s3.s2.s1;
    let about_to_lock = matches!(action, Action::Down) && !t1::model::can_move_piece(-1, 0, s1);
    let pre = match action {
        Action::Down if about_to_lock => {
            Some(anim::precompute_clear(&s1.mg, s1.p, s1.py, s1.px, s1.pr))
        }
        Action::Drop => Some(anim::precompute_clear(
            &s1.mg, s1.p, machine.gy, s1.px, s1.pr,
        )),
        _ => None,
    };
    let mut locked = false;
    let fired = fire_single(action, machine, |ok| {
        if !ok {
            return;
        }
        match action {
            Action::Left | Action::Right => sound.play(Sfx::Move),
            Action::Cw | Action::Ccw => sound.play(Sfx::Rotate),
            Action::Hold => sound.play(Sfx::Hold),
            Action::Down if about_to_lock => {
                sound.play(Sfx::Fix);
                locked = true;
            }
            Action::Down => sound.play(Sfx::Move),
            Action::Drop => {
                sound.play(Sfx::Drop);
                locked = true;
            }
        }
    });
    if locked {
        if let Some((grid, rows)) = pre {
            if !rows.is_empty() {
                *clear_anim = Some(anim::ClearAnim::new(grid, rows, now));
            }
        }
    }
    fired
}

/// Multiplayer dispatch — same hook shape as `fire_single_with_effects`,
/// over `t7::model::Machine<Instance>`, plus garbage-arrival sound/
/// animation once a lock materializes any. `apply_lock_effects` needs
/// `machine`'s post-call state (`cleared_lines`/`perfect_clear`), which is
/// unreachable from inside `on_result` since the dispatch call still holds
/// `machine` by unique reference there — so `on_result` only sets `locked`
/// and plays `Fix`/`Drop`, and `apply_lock_effects` runs after the call
/// returns.
fn fire_with_effects(
    action: Action,
    machine: &mut t7::model::Machine<Instance>,
    wm: i64,
    sound: &SoundEngine,
    clear_anim: &mut Option<anim::ClearAnim<Instance>>,
    garbage_anim: &mut Option<anim::GarbageAnim>,
    now: f64,
) -> bool {
    let s1 = &machine.s6.s4.s3.s2.s1;
    let about_to_lock = matches!(action, Action::Down) && !t1::model::can_move_piece(-1, 0, s1);
    let pre = match action {
        Action::Down if about_to_lock => {
            Some(anim::precompute_clear(&s1.mg, s1.p, s1.py, s1.px, s1.pr))
        }
        Action::Drop => Some(anim::precompute_clear(
            &s1.mg,
            s1.p,
            machine.s6.gy,
            s1.px,
            s1.pr,
        )),
        _ => None,
    };
    let garbage_before = machine.garbage;
    let mut locked = false;
    let fired = t7::session::fire(action, machine, wm, |ok| {
        if !ok {
            return;
        }
        match action {
            Action::Left | Action::Right => sound.play(Sfx::Move),
            Action::Cw | Action::Ccw => sound.play(Sfx::Rotate),
            Action::Hold => sound.play(Sfx::Hold),
            Action::Down if about_to_lock => {
                sound.play(Sfx::Fix);
                locked = true;
            }
            Action::Down => sound.play(Sfx::Move),
            Action::Drop => {
                sound.play(Sfx::Drop);
                locked = true;
            }
        }
    });
    if locked {
        apply_lock_effects(
            machine,
            garbage_before,
            pre,
            sound,
            clear_anim,
            garbage_anim,
            now,
        );
    }
    fired
}

fn apply_lock_effects(
    machine: &t7::model::Machine<Instance>,
    garbage_before: i64,
    pre: Option<anim::ClearPrecompute<Instance>>,
    sound: &SoundEngine,
    clear_anim: &mut Option<anim::ClearAnim<Instance>>,
    garbage_anim: &mut Option<anim::GarbageAnim>,
    now: f64,
) {
    if let Some((grid, rows)) = pre {
        if !rows.is_empty() {
            *clear_anim = Some(anim::ClearAnim::new(grid, rows, now));
        }
    }
    if garbage_before > 0 {
        let cleared_lines = machine.s6.cleared_lines();
        let perfect_clear = machine.s6.s4.s3.s2.perfect_clear;
        let (_, rem_garbage) =
            t7::model::gen_rem_garbage(garbage_before, cleared_lines, perfect_clear);
        let hm = machine.s6.mg().len() as i64;
        let eff_rem = rem_garbage.min(hm);
        if eff_rem > 0 {
            sound.play(Sfx::GarbageSlam(eff_rem.min(8) as u8));
            *garbage_anim = Some(anim::GarbageAnim {
                row_count: eff_rem as u8,
                start: now,
            });
        }
    }
}

// ── main ────────────────────────────────────────────────────────────────

#[macroquad::main(window_conf)]
async fn main() {
    if t5::model::CHECK_AXIOMS {
        t5::model::check_axioms::<Instance>();
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
    let font = load_ttf_font_from_bytes(FONT_BYTES).expect("embedded font must parse");
    let sound = SoundEngine::new();

    let mut app = App::ModeSelect;
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
    let mut menu_index: usize = 0;
    let mut menu_pad = GamepadEdges::default();
    let mut logical_mute: Option<KeyCode> = None;

    loop {
        let now = get_time();
        let escape = is_key_pressed(KeyCode::Escape);
        if !char_queue_reserved(&app) {
            update_logical_keys(&mut logical_keys, &mut logical_mute);
            if logical_mute.is_some_and(is_key_pressed) {
                sound.toggle_muted();
            }
        }

        match &mut app {
            // ── S1 Mode Select ─────────────────────────────────────────
            App::ModeSelect => {
                let pad = gilrs
                    .as_ref()
                    .and_then(|g| g.gamepads().next())
                    .map(|(_, pad)| pad);
                let nav = poll_menu_nav(pad, &mut menu_pad);
                match step_mode_select(escape, nav, &mut menu_index) {
                    ModeSelectOutcome::Quit => {
                        macroquad::miniquad::window::order_quit();
                        return;
                    }
                    ModeSelectOutcome::EnterSingle => {
                        app = App::Single(SpGame::fresh());
                        run = RunState::fresh(now);
                        key_repeat.clear();
                    }
                    ModeSelectOutcome::EnterRoleSelect => {
                        app = App::RoleSelect;
                        menu_index = 0;
                    }
                    ModeSelectOutcome::Stay => {}
                }
                draw_mode_select(menu_index, "   [M] mute", Some(&font));
            }

            // ── S2 Role Select ─────────────────────────────────────────
            App::RoleSelect => {
                let pad = gilrs
                    .as_ref()
                    .and_then(|g| g.gamepads().next())
                    .map(|(_, pad)| pad);
                let nav = poll_menu_nav(pad, &mut menu_pad);
                match step_role_select(escape, nav, &mut menu_index) {
                    RoleSelectOutcome::Stay => {}
                    RoleSelectOutcome::Back => app = App::ModeSelect,
                    RoleSelectOutcome::Host(lobby) => app = App::Host(*lobby),
                    RoleSelectOutcome::Join(lobby) => app = App::Join(lobby),
                }
                if matches!(app, App::RoleSelect) {
                    draw_role_select(menu_index, Some(&font));
                }
            }

            // ── S3 Host Lobby ──────────────────────────────────────────
            App::Host(lobby) => {
                let pad = gilrs
                    .as_ref()
                    .and_then(|g| g.gamepads().next())
                    .map(|(_, pad)| pad);
                match step_host_lobby(
                    lobby,
                    escape,
                    pad,
                    &mut menu_pad,
                    &mut run,
                    &mut key_repeat,
                    now,
                ) {
                    HostLobbyOutcome::Stay => {}
                    HostLobbyOutcome::Back => app = App::ModeSelect,
                    HostLobbyOutcome::Started => {
                        let App::Host(lobby) = std::mem::replace(&mut app, App::ModeSelect) else {
                            unreachable!()
                        };
                        app = App::Playing(Playing {
                            session: lobby.session,
                            filler: None,
                            own_gameover_since: None,
                            filler_clear_anim: None,
                            filler_gameover_since: None,
                            mp_clear_anim: None,
                            mp_garbage_anim: None,
                            connected_prev: Vec::new(),
                        });
                    }
                }
                if let App::Host(lobby) = &app {
                    draw_host_lobby(lobby, "   [M] mute", Some(&font));
                }
            }

            // ── S4 Join Screen ─────────────────────────────────────────
            App::Join(lobby) => {
                let pad = gilrs
                    .as_ref()
                    .and_then(|g| g.gamepads().next())
                    .map(|(_, pad)| pad);
                match step_join_lobby(
                    lobby,
                    escape,
                    pad,
                    &mut menu_pad,
                    &mut run,
                    &mut key_repeat,
                    now,
                ) {
                    JoinLobbyOutcome::Stay => {}
                    JoinLobbyOutcome::Back => app = App::ModeSelect,
                    JoinLobbyOutcome::Connected(session) => {
                        app = App::Waiting(Waiting {
                            session: *session,
                            filler: fresh_single(),
                            filler_clear_anim: None,
                            filler_gameover_since: None,
                        });
                    }
                }
                if let App::Join(lobby) = &app {
                    draw_join_lobby(lobby, "   [M] mute", Some(&font));
                }
            }

            // ── S6 Waiting Room ────────────────────────────────────────
            App::Waiting(waiting) => {
                match step_waiting_session(&mut waiting.session, escape, now) {
                    WaitingOutcome::Left => app = App::ModeSelect,
                    WaitingOutcome::ToPlaying => {
                        run = RunState::fresh(now);
                        key_repeat.clear();
                        let App::Waiting(w) = std::mem::replace(&mut app, App::ModeSelect) else {
                            unreachable!()
                        };
                        app = App::Playing(Playing {
                            session: w.session,
                            filler: None,
                            own_gameover_since: None,
                            filler_clear_anim: None,
                            filler_gameover_since: None,
                            mp_clear_anim: None,
                            mp_garbage_anim: None,
                            connected_prev: Vec::new(),
                        });
                    }
                    WaitingOutcome::HostLost => app = App::HostLost,
                    WaitingOutcome::Stay => {
                        if let Some(g) = &mut gilrs {
                            while g.next_event().is_some() {}
                        }
                        let pad = gilrs
                            .as_ref()
                            .and_then(|g| g.gamepads().next())
                            .map(|(_, pad)| pad);
                        drive_filler(
                            &mut waiting.filler,
                            &mut key_repeat,
                            &logical_keys,
                            pad,
                            &mut run,
                            now,
                            &sound,
                            &mut waiting.filler_clear_anim,
                            &mut waiting.filler_gameover_since,
                        );
                        let expired = waiting
                            .filler_clear_anim
                            .as_ref()
                            .is_some_and(|a| a.done(now));
                        if expired {
                            waiting.filler_clear_anim = None;
                        }
                        if let Some(a) = &waiting.filler_clear_anim {
                            let p = anim::progress(a, now);
                            anim::draw_clear_flash(
                                &constants,
                                &waiting.filler,
                                &a.grid,
                                &a.rows,
                                p,
                                (0.0, 0.0),
                                &t1::instance::piece_color,
                                Some(&font),
                            );
                        } else {
                            t6::view::render(
                                &constants,
                                &waiting.filler,
                                t1::instance::piece_color,
                                run.banner.as_ref(),
                                Some(&font),
                            );
                        }
                        draw_waiting_overlay(&waiting.session, Some(&font));
                    }
                }
            }

            // ── S7 Gameplay, and S8 mid-match filler ───────────────────
            App::Playing(playing) => {
                if escape {
                    playing.session.leave();
                    app = App::ModeSelect;
                } else {
                    playing.session.pump(now);
                    if let Some(g) = &mut gilrs {
                        while g.next_event().is_some() {}
                    }
                    let pad = gilrs
                        .as_ref()
                        .and_then(|g| g.gamepads().next())
                        .map(|(_, pad)| pad);
                    let wm = constants.wm;

                    // The real Machine is driven only in S7; in S8 it stays
                    // alive headless (still pumped, still fed receive_*),
                    // and the filler takes the input instead.
                    if playing.filler.is_none() {
                        let gameover = playing
                            .session
                            .machine
                            .as_ref()
                            .map(|m| m.s6.s4.s3.s2.s1.gameover);
                        if let Some(gameover) = gameover {
                            let mut clear_anim = playing.mp_clear_anim.take();
                            let mut garbage_anim = playing.mp_garbage_anim.take();
                            process_input(
                                gameover,
                                &mut key_repeat,
                                &logical_keys,
                                pad,
                                now,
                                |action| {
                                    playing.session.fire_and_broadcast(|machine| {
                                        fire_with_effects(
                                            action,
                                            machine,
                                            wm,
                                            &sound,
                                            &mut clear_anim,
                                            &mut garbage_anim,
                                            now,
                                        )
                                    })
                                },
                            );

                            let gameover_now = playing
                                .session
                                .machine
                                .as_ref()
                                .is_some_and(|m| m.s6.s4.s3.s2.s1.gameover);
                            if !gameover_now && now - run.last_fall >= run.current_gravity_period {
                                run.last_fall = now;
                                playing.session.fire_and_broadcast(|machine| {
                                    fire_with_effects(
                                        Action::Down,
                                        machine,
                                        wm,
                                        &sound,
                                        &mut clear_anim,
                                        &mut garbage_anim,
                                        now,
                                    )
                                });
                            }
                            playing.mp_clear_anim = clear_anim;
                            playing.mp_garbage_anim = garbage_anim;
                        }
                        if let Some(machine) = &playing.session.machine {
                            let events = after_action(&machine.s6.s4.s3.s2, now, &mut run);
                            play_after_action_sfx(&events, &sound);
                        }
                    }

                    // Disconnect sfx: diff each opponent's connected flag
                    // against last frame's snapshot.
                    if let Some(machine) = &playing.session.machine {
                        let my_index = machine.my_index;
                        let opponents = playing.session.opponent_views();
                        if playing.connected_prev.len() == machine.connected_view.len() {
                            for opp in &opponents {
                                if playing.connected_prev[opp.player_index] && !opp.connected {
                                    sound.play(Sfx::Disconnect);
                                }
                            }
                        }
                        let mut connected = vec![true; machine.connected_view.len()];
                        for opp in &opponents {
                            connected[opp.player_index] = opp.connected;
                        }
                        if my_index < connected.len() {
                            connected[my_index] = machine.connected_view[my_index];
                        }
                        playing.connected_prev = connected;
                    }

                    let my_index = playing.session.machine.as_ref().map(|m| m.my_index);
                    let was_waiting_for_gameover = playing.own_gameover_since.is_some();
                    let filler_is_none = playing.filler.is_none();
                    match step_playing_transition(
                        &playing.session,
                        filler_is_none,
                        &mut playing.own_gameover_since,
                        &logical_keys,
                        pad,
                        now,
                    ) {
                        PlayingTransition::ToWinner { winner } => {
                            if winner == my_index {
                                sound.play(Sfx::Winner);
                            }
                            let App::Playing(p) = std::mem::replace(&mut app, App::ModeSelect)
                            else {
                                unreachable!()
                            };
                            app = App::Winner(Winner {
                                session: p.session,
                                winner,
                            });
                            menu_index = 0;
                        }
                        PlayingTransition::ToHostLost => {
                            sound.play(Sfx::HostLost);
                            app = App::HostLost;
                        }
                        PlayingTransition::GameoverWaitStarted => {
                            if !was_waiting_for_gameover {
                                sound.play(Sfx::Gameover);
                            }
                        }
                        PlayingTransition::EnteredFiller => {
                            playing.filler = Some(fresh_single());
                            playing.own_gameover_since = None;
                            playing.filler_clear_anim = None;
                            playing.filler_gameover_since = None;
                            run = RunState::fresh(now);
                            key_repeat.clear();
                        }
                        PlayingTransition::Continue => {}
                    }

                    if let App::Playing(playing) = &mut app {
                        if let Some(filler) = playing.filler.as_mut() {
                            drive_filler(
                                filler,
                                &mut key_repeat,
                                &logical_keys,
                                pad,
                                &mut run,
                                now,
                                &sound,
                                &mut playing.filler_clear_anim,
                                &mut playing.filler_gameover_since,
                            );
                        }
                        // Either way the T7 view draws: in S8 the own-board
                        // half shows the filler, while the mini-grid strip
                        // and garbage gauge stay live off the headless
                        // Machine.
                        if let Some(machine) = &playing.session.machine {
                            let opponents = playing.session.opponent_views();
                            match &playing.filler {
                                None => {
                                    let clear_expired =
                                        playing.mp_clear_anim.as_ref().is_some_and(|a| a.done(now));
                                    if clear_expired {
                                        playing.mp_clear_anim = None;
                                    }
                                    if let Some(a) = &playing.mp_clear_anim {
                                        let p = anim::progress(a, now);
                                        let remaining = ((a.duration() - (now - a.start))
                                            / a.duration())
                                        .max(0.0)
                                            as f32;
                                        let (dx, dy) = if a.tetris {
                                            anim::shake_offset(anim::TETRIS_SHAKE_PX, remaining)
                                        } else {
                                            (0.0, 0.0)
                                        };
                                        anim::draw_clear_flash(
                                            &constants,
                                            &machine.s6,
                                            &a.grid,
                                            &a.rows,
                                            p,
                                            (dx, dy),
                                            &t1::instance::piece_color,
                                            Some(&font),
                                        );
                                    } else {
                                        let garbage_expired = playing
                                            .mp_garbage_anim
                                            .as_ref()
                                            .is_some_and(|a| a.done(now));
                                        if garbage_expired {
                                            playing.mp_garbage_anim = None;
                                        }
                                        view::render(
                                            &constants,
                                            machine,
                                            t1::instance::piece_color,
                                            run.banner.as_ref(),
                                            &opponents,
                                            Some(&font),
                                        );
                                        if let Some(a) = &playing.mp_garbage_anim {
                                            let p = a.progress(now);
                                            let amp = anim::GARBAGE_SHAKE_PX
                                                * (a.row_count as f32).min(2.0);
                                            let (dx, dy) = anim::shake_offset(amp, 1.0 - p);
                                            let layout =
                                                t4::view::compute_layout::<Instance>(&constants);
                                            anim::draw_garbage_flash(
                                                &constants,
                                                &layout.base.base.base,
                                                a.row_count,
                                                p,
                                                (dx, dy),
                                            );
                                        }
                                    }
                                }
                                Some(filler) => {
                                    let expired = playing
                                        .filler_clear_anim
                                        .as_ref()
                                        .is_some_and(|a| a.done(now));
                                    if expired {
                                        playing.filler_clear_anim = None;
                                    }
                                    if let Some(a) = &playing.filler_clear_anim {
                                        let p = anim::progress(a, now);
                                        anim::draw_clear_flash(
                                            &constants,
                                            filler,
                                            &a.grid,
                                            &a.rows,
                                            p,
                                            (0.0, 0.0),
                                            &t1::instance::piece_color,
                                            Some(&font),
                                        );
                                    } else {
                                        t6::view::render(
                                            &constants,
                                            filler,
                                            t1::instance::piece_color,
                                            run.banner.as_ref(),
                                            Some(&font),
                                        );
                                    }
                                    view::draw_side_regions(
                                        &constants,
                                        machine,
                                        t1::instance::piece_color,
                                        &opponents,
                                        Some(&font),
                                    );
                                    draw_gameover_filler_overlay(Some(&font));
                                }
                            }
                        }
                    }
                }
            }

            // ── S9 Winner Screen ───────────────────────────────────────
            App::Winner(winner) => {
                let pad = gilrs
                    .as_ref()
                    .and_then(|g| g.gamepads().next())
                    .map(|(_, pad)| pad);
                match step_winner(winner, pad, &mut menu_pad, &mut menu_index, now) {
                    WinnerOutcome::Stay => {}
                    WinnerOutcome::Leave => app = App::ModeSelect,
                    WinnerOutcome::RematchAsHost => {
                        let App::Winner(w) = std::mem::replace(&mut app, App::ModeSelect) else {
                            unreachable!()
                        };
                        let session = w.session;
                        let name = TextInput::with(session.my_name.clone());
                        app = App::Host(HostLobby::new(session, name));
                    }
                    WinnerOutcome::RematchAsJoiner => {
                        let App::Winner(w) = std::mem::replace(&mut app, App::ModeSelect) else {
                            unreachable!()
                        };
                        run = RunState::fresh(now);
                        key_repeat.clear();
                        app = App::Waiting(Waiting {
                            session: w.session,
                            filler: fresh_single(),
                            filler_clear_anim: None,
                            filler_gameover_since: None,
                        });
                    }
                }
                if let App::Winner(w) = &app {
                    draw_winner_screen(w, menu_index, Some(&font));
                }
            }

            // ── S10 Host Lost ──────────────────────────────────────────
            App::HostLost => {
                let pad = gilrs
                    .as_ref()
                    .and_then(|g| g.gamepads().next())
                    .map(|(_, pad)| pad);
                if step_host_lost(escape, pad, &mut menu_pad) {
                    app = App::ModeSelect;
                }
                if matches!(app, App::HostLost) {
                    draw_host_lost(Some(&font));
                }
            }

            // spec: single-player — the T6 engine, unchanged and
            // un-wrapped: no garbage, no target, no views, no network.
            App::Single(game) => {
                if escape {
                    app = App::ModeSelect;
                } else {
                    // logical_keys/logical_mute learning is skipped this frame
                    // whenever game.post != None (see char_queue_reserved).
                    if let Some(g) = &mut gilrs {
                        while g.next_event().is_some() {}
                    }
                    let pad = gilrs
                        .as_ref()
                        .and_then(|g| g.gamepads().next())
                        .map(|(_, pad)| pad);
                    let gameover = game.machine.s4.s3.s2.s1.gameover;

                    if matches!(game.post, SpPost::None) {
                        process_input(
                            gameover,
                            &mut key_repeat,
                            &logical_keys,
                            pad,
                            now,
                            |action| {
                                fire_single_with_effects(
                                    action,
                                    &mut game.machine,
                                    &sound,
                                    &mut game.clear_anim,
                                    now,
                                )
                            },
                        );

                        if gameover {
                            if game.gameover_since.is_none() {
                                sound.play(Sfx::Gameover);
                                game.gameover_since = Some(now);
                            }
                        } else if now - run.last_fall >= run.current_gravity_period {
                            run.last_fall = now;
                            fire_single_with_effects(
                                Action::Down,
                                &mut game.machine,
                                &sound,
                                &mut game.clear_anim,
                                now,
                            ); // req-piece-fall
                        }
                        let events = after_action(&game.machine.s4.s3.s2, now, &mut run);
                        play_after_action_sfx(&events, &sound);

                        if let Some(since) = game.gameover_since {
                            if now - since >= SP_GAMEOVER_LOCKOUT_SECS {
                                let s2 = &game.machine.s4.s3.s2;
                                let (score, level, lines) =
                                    (s2.score, s2.level, s2.total_cleared_lines);
                                let entries = highscores::get_high_scores();
                                let storage_ok = highscores::is_storage_available();
                                game.post = if storage_ok && highscores::qualifies(&entries, score)
                                {
                                    SpPost::NameEntry {
                                        score,
                                        level,
                                        lines,
                                        name: TextInput::default(),
                                        backspace_repeat: None,
                                    }
                                } else {
                                    SpPost::HallOfFame {
                                        entries,
                                        highlight: None,
                                        notice: !storage_ok,
                                    }
                                };
                            }
                        }
                    } else if let SpPost::NameEntry {
                        score,
                        level,
                        lines,
                        name,
                        backspace_repeat,
                    } = &mut game.post
                    {
                        let edit = poll_text_edit();
                        name.apply(&edit, HOF_NAME_MAX_LEN);
                        drive_backspace_repeat(name, backspace_repeat, now);
                        if is_key_pressed(KeyCode::Enter) {
                            let entered = entered_name(name, "Player");
                            let (score, level, lines) = (*score, *level, *lines);
                            let entries = highscores::record_score(
                                entered,
                                score,
                                level,
                                lines,
                                SystemTime::now(),
                            );
                            game.post = SpPost::HallOfFame {
                                entries,
                                highlight: Some(score),
                                notice: false,
                            };
                        }
                    } else if let SpPost::HallOfFame { .. } = &game.post {
                        let alnum_pressed =
                            std::iter::from_fn(get_char_pressed).any(|c| c.is_ascii_alphanumeric());
                        if is_key_pressed(KeyCode::Enter)
                            || is_key_pressed(KeyCode::Space)
                            || alnum_pressed
                        {
                            *game = SpGame::fresh();
                            run = RunState::fresh(now);
                            key_repeat.clear();
                        }
                    }
                }

                if let App::Single(game) = &mut app {
                    match &game.post {
                        SpPost::None => {
                            let expired = game.clear_anim.as_ref().is_some_and(|a| a.done(now));
                            if expired {
                                game.clear_anim = None;
                            }
                            if let Some(a) = &game.clear_anim {
                                let p = anim::progress(a, now);
                                let remaining = ((a.duration() - (now - a.start)) / a.duration())
                                    .max(0.0)
                                    as f32;
                                let (dx, dy) = if a.tetris {
                                    anim::shake_offset(anim::TETRIS_SHAKE_PX, remaining)
                                } else {
                                    (0.0, 0.0)
                                };
                                anim::draw_clear_flash(
                                    &constants,
                                    &game.machine,
                                    &a.grid,
                                    &a.rows,
                                    p,
                                    (dx, dy),
                                    &t1::instance::piece_color,
                                    Some(&font),
                                );
                            } else if game.machine.s4.s3.s2.s1.gameover
                                && game
                                    .gameover_since
                                    .is_some_and(|s| now - s < SP_GAMEOVER_LOCKOUT_SECS)
                            {
                                anim::draw_board_without_gameover_overlay(
                                    &constants,
                                    &game.machine,
                                    t1::instance::piece_color,
                                    run.banner.as_ref(),
                                    Some(&font),
                                );
                                let layout = t4::view::compute_layout::<SingleInstance>(&constants);
                                anim::draw_gameover_partial(
                                    &constants,
                                    &layout.base.base.base,
                                    Some(&font),
                                );
                            } else {
                                t6::view::render(
                                    &constants,
                                    &game.machine,
                                    t1::instance::piece_color,
                                    run.banner.as_ref(),
                                    Some(&font),
                                );
                            }
                        }
                        SpPost::NameEntry {
                            score,
                            level,
                            lines,
                            name,
                            ..
                        } => {
                            draw_name_entry(*score, *level, *lines, name, Some(&font));
                        }
                        SpPost::HallOfFame {
                            entries,
                            highlight,
                            notice,
                        } => {
                            draw_hall_of_fame(entries, *highlight, *notice, Some(&font));
                        }
                    }
                }
            }
        }

        if let Some(b) = &run.banner {
            if now - b.t > BANNER_SECS {
                run.banner = None;
            }
        }

        // A persistent indicator, over every screen, so muting is never a
        // silent state the player has to remember they set.
        if sound.is_muted() {
            let size = (screen_height() * 0.022).max(12.0) as u16;
            t2::view::draw_text_label(
                "MUTED",
                screen_width() * 0.02,
                size as f32 * 1.2,
                size,
                HINT_COLOR,
                Some(&font),
            );
        }

        next_frame().await;
    }
}
