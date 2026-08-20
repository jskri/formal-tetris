#![deny(warnings)]
//! spec: main.rs — entry point, screen state machine, host relay (§15,
//! `implementation.md`).
//!
//! §0.4: a thin reference caller for `t7::app`/`t7::text` (both `pub mod`,
//! reusable by other binaries) — nothing beyond the `App` enum, its own
//! `Waiting`/`Playing` payload structs, the frame loop driving `t7::app`'s
//! step functions, and the single-player screen (§1: served directly by
//! `t6::model::Machine`, `t7::model::Machine` never constructed). Being a
//! binary target, no other crate can link against it.
//!
//! Two multiplayer roles, chosen at `S2`'s role-select screen, reached from
//! `S1`'s "Multi Player":
//! - **Host a match** — one STUN lookup and one connection code per
//!   prospective joiner, roster assignment on `Join`, `Players`
//!   rebroadcast, `Start` on the host's own go-ahead, then the host relay
//!   (§15.4) for the duration of the match.
//! - **Join a match** — its own STUN lookup and code, the host's code
//!   pasted in, then `Join`/`Players`/`Start`.
//!
//! The screen state machine those two live inside is §15.0's `S1`–`S10`
//! table, realized as `App` — see that enum's doc comment for the
//! screen-by-screen mapping.
//!
//! `Session` (the networked match) never calls a macroquad API; every
//! `t7::app` step/draw function does. That split is what lets `t7::app`'s
//! `tests` module drive a full host and two joiners over loopback UDP,
//! through lobby and into a running match, with no display server present.
//!
//! Bags are per-player and purely local: `T7.v`'s `Init` takes one
//! independent bag sequence per player, and each peer's `Machine` holds
//! only its own `s6`, so no bag synchronization crosses the wire — every
//! peer runs `make_bags_fn` against its own RNG. What crosses the wire is
//! `T7.v`'s own `Message` set, plus the rendering-only `State` broadcast
//! (§15.3).

use gilrs::Gilrs;
use macroquad::prelude::*;
use std::collections::HashMap;
use t1::misc::{window_conf, LogicalKeys, RepeatTimer};
use t1::model::Params as _;
use t7::app::{
    after_action, draw_gameover_filler_overlay, draw_host_lobby, draw_host_lost, draw_join_lobby,
    draw_mode_select, draw_role_select, draw_waiting_overlay, draw_winner_screen,
    drive_filler_input, fire_single, fresh_single, poll_menu_nav, process_input,
    restart_filler_on_keypress, step_host_lobby, step_host_lost, step_join_lobby, step_mode_select,
    step_playing_gameplay, step_playing_transition, step_role_select, step_waiting_session,
    step_winner, GamepadEdges, HostLobby, HostLobbyOutcome, JoinLobby, JoinLobbyOutcome,
    ModeSelectOutcome, PlayingTransition, RoleSelectOutcome, RunState, SingleInstance,
    WaitingOutcome, Winner, WinnerOutcome,
};
use t7::misc::Action;
use t7::session::{fire, shuffle_bag, Instance, Session};
use t7::text::TextInput;
use t7::view;

const FONT_BYTES: &[u8] = include_bytes!("../../assets/JetBrainsMono-Regular.ttf");

const BANNER_SECS: f64 = 1.2;

/// `S6` — the waiting room. §15.2: a `t6::model::Machine` filler game,
/// driven by *this* file's own input/fall-timer code rather than `t6`'s
/// own `main`.
struct Waiting {
    session: Session,
    filler: t6::model::Machine<SingleInstance>,
}

/// `S7`/`S8` (§15.0) — the real `t7::model::Machine` stays alive headless
/// once `filler` is running.
struct Playing {
    session: Session,
    filler: Option<t6::model::Machine<SingleInstance>>,
    /// Timestamp this peer's own `Machine` went gameover; `None` before
    /// that and once `filler` is running. Gates the `GAMEOVER_FILLER_DELAY_SECS`
    /// banner-then-keypress transition into `S8` (§15.0; see the
    /// `App::Playing` match arm).
    own_gameover_since: Option<f64>,
}

/// spec: §15.0 — ten DOM-free macroquad screens, no widget toolkit, so each
/// screen's actions are keys (or a gamepad button) rather than clicks.
/// Screen-by-screen mapping onto this enum:
///
/// | this enum | §15.0 | notes |
/// |---|---|---|
/// | `ModeSelect` | `S1` | "Single Player" / "Multi Player" |
/// | `RoleSelect` | `S2` | "Host" / "Join" |
/// | `Single` | — | `S1`'s Single Player branch, served by `t6::model::Machine` directly (§1), `t7` never constructed |
/// | `Host` | `S3` | name field, "Add connection", code exchange, joiner list, "Start" |
/// | `Join` | `S4` | name field, own code, "paste host's code", "Connect" |
/// | `Waiting` | `S6` | `t6` filler game + roster + "waiting for host" |
/// | `Playing` | `S7`/`S8` | `S8` is `Playing { filler: Some(_) }`, not a distinct screen |
/// | `Winner` | `S9` | "You win" / "Winner: `<name>`", "Rematch", "Leave" |
/// | `HostLost` | `S10` | "Connection to host lost.", "Return to menu" |
///
/// `S5` has no variant: its only action is automatic (§15.0) —
/// `Session::rejoin`, called on the way from `Winner` to `Waiting`, is
/// never drawn on its own frame.
enum App {
    ModeSelect,
    RoleSelect,
    /// spec: §1 — served by `t6::model::Machine` directly, never by
    /// `t7::model::Machine`.
    Single(t6::model::Machine<SingleInstance>),
    Host(HostLobby),
    Join(JoinLobby),
    Waiting(Waiting),
    Playing(Playing),
    Winner(Winner),
    HostLost,
}

// ── main ────────────────────────────────────────────────────────────────

#[macroquad::main(window_conf)]
async fn main() {
    if t5::model::CHECK_AXIOMS {
        // Reached via t5::model — neither t6::model nor t7::model re-exports
        // it (model.rs's own header comment).
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
    // Mode/Role Select's highlighted item, shared since only one of the two
    // is ever visible at once; reset to 0 on entering Role Select so it
    // starts on "Host" rather than inheriting Mode Select's last choice.
    let mut menu_index: usize = 0;
    // Gamepad edge-debouncing for `poll_menu_nav` — one shared tracker is
    // fine for the same reason `menu_index` is: exactly one menu-style
    // screen reads it per frame.
    let mut menu_pad = GamepadEdges::default();

    loop {
        let now = get_time();
        let escape = is_key_pressed(KeyCode::Escape);

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
                        app = App::Single(fresh_single());
                        run = RunState::fresh(now);
                        key_repeat.clear();
                    }
                    ModeSelectOutcome::EnterRoleSelect => {
                        app = App::RoleSelect;
                        menu_index = 0;
                    }
                    ModeSelectOutcome::Stay => {}
                }
                draw_mode_select(menu_index, "", Some(&font));
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
                        });
                    }
                }
                if let App::Host(lobby) = &app {
                    draw_host_lobby(lobby, "", Some(&font));
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
                        });
                    }
                }
                if let App::Join(lobby) = &app {
                    draw_join_lobby(lobby, "", Some(&font));
                }
            }

            // ── S6 Waiting Room ────────────────────────────────────────
            App::Waiting(waiting) => {
                match step_waiting_session(&mut waiting.session, escape, now) {
                    WaitingOutcome::Left => app = App::ModeSelect,
                    WaitingOutcome::ToPlaying => {
                        // §15.0: START received → S7.
                        run = RunState::fresh(now);
                        key_repeat.clear();
                        let App::Waiting(w) = std::mem::replace(&mut app, App::ModeSelect) else {
                            unreachable!()
                        };
                        app = App::Playing(Playing {
                            session: w.session,
                            filler: None,
                            own_gameover_since: None,
                        });
                    }
                    WaitingOutcome::HostLost => app = App::HostLost,
                    WaitingOutcome::Stay => {
                        logical_keys.update();
                        if let Some(g) = &mut gilrs {
                            while g.next_event().is_some() {}
                        }
                        let pad = gilrs
                            .as_ref()
                            .and_then(|g| g.gamepads().next())
                            .map(|(_, pad)| pad);
                        drive_filler_input(
                            &mut waiting.filler,
                            &mut key_repeat,
                            &logical_keys,
                            pad,
                            &mut run,
                            now,
                            |action, m| fire_single(action, m, |_| {}),
                        );
                        restart_filler_on_keypress(
                            &mut waiting.filler,
                            &mut run,
                            &logical_keys,
                            pad,
                            now,
                        );
                        t6::view::render(
                            &constants,
                            &waiting.filler,
                            t1::instance::piece_color,
                            run.banner.as_ref(),
                            Some(&font),
                        );
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
                    logical_keys.update();
                    if let Some(g) = &mut gilrs {
                        while g.next_event().is_some() {}
                    }
                    let pad = gilrs
                        .as_ref()
                        .and_then(|g| g.gamepads().next())
                        .map(|(_, pad)| pad);
                    let wm = constants.wm;

                    // Real Machine takes input only in S7; in S8 it stays
                    // headless (still pumped/fed above) and the filler
                    // takes the input instead (§15.0).
                    if playing.filler.is_none() {
                        step_playing_gameplay(
                            &mut playing.session,
                            &mut key_repeat,
                            &logical_keys,
                            pad,
                            &mut run,
                            now,
                            wm,
                            |action, machine| fire(action, machine, wm, |_| {}),
                        );
                    }

                    match step_playing_transition(
                        &playing.session,
                        playing.filler.is_none(),
                        &mut playing.own_gameover_since,
                        &logical_keys,
                        pad,
                        now,
                    ) {
                        PlayingTransition::ToWinner { winner } => {
                            let App::Playing(p) = std::mem::replace(&mut app, App::ModeSelect)
                            else {
                                unreachable!()
                            };
                            app = App::Winner(Winner {
                                session: p.session,
                                winner,
                            });
                            // "Rematch" is the default focus, reusing the
                            // same loop-local index as Mode/Role Select
                            // (never concurrently visible with either).
                            menu_index = 0;
                        }
                        PlayingTransition::ToHostLost => app = App::HostLost,
                        PlayingTransition::EnteredFiller => {
                            playing.filler = Some(fresh_single());
                            playing.own_gameover_since = None;
                            run = RunState::fresh(now);
                            key_repeat.clear();
                        }
                        PlayingTransition::GameoverWaitStarted | PlayingTransition::Continue => {}
                    }

                    if let App::Playing(playing) = &mut app {
                        if let Some(filler) = playing.filler.as_mut() {
                            drive_filler_input(
                                filler,
                                &mut key_repeat,
                                &logical_keys,
                                pad,
                                &mut run,
                                now,
                                |action, m| fire_single(action, m, |_| {}),
                            );
                            restart_filler_on_keypress(filler, &mut run, &logical_keys, pad, now);
                        }
                        // S8: own-board half shows the filler; mini-grid
                        // strip and gauge stay live off the headless
                        // Machine (§15.0).
                        if let Some(machine) = &playing.session.machine {
                            let opponents = playing.session.opponent_views();
                            match &playing.filler {
                                None => view::render(
                                    &constants,
                                    machine,
                                    t1::instance::piece_color,
                                    run.banner.as_ref(),
                                    &opponents,
                                    Some(&font),
                                ),
                                Some(filler) => {
                                    t6::view::render(
                                        &constants,
                                        filler,
                                        t1::instance::piece_color,
                                        run.banner.as_ref(),
                                        Some(&font),
                                    );
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
                        let session = w.session;
                        run = RunState::fresh(now);
                        key_repeat.clear();
                        app = App::Waiting(Waiting {
                            session,
                            filler: fresh_single(),
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

            // spec: §1 — plain t6::model::Machine, no garbage/target/
            // network; rendered via t6::view::render, so no garbage gauge
            // or opponent strip (nothing for them to show).
            App::Single(machine) => {
                if escape {
                    app = App::ModeSelect;
                } else {
                    logical_keys.update();
                    if let Some(g) = &mut gilrs {
                        while g.next_event().is_some() {}
                    }
                    let pad = gilrs
                        .as_ref()
                        .and_then(|g| g.gamepads().next())
                        .map(|(_, pad)| pad);

                    process_input(
                        machine.s4.s3.s2.s1.gameover,
                        &mut key_repeat,
                        &logical_keys,
                        pad,
                        now,
                        |action| fire_single(action, machine, |_| {}),
                    );

                    if machine.s4.s3.s2.s1.gameover {
                        if t1::misc::any_action_just_pressed(&logical_keys, pad) {
                            *machine = fresh_single();
                            run = RunState::fresh(now);
                        }
                    } else if now - run.last_fall >= run.current_gravity_period {
                        run.last_fall = now;
                        machine.fall_step(&shuffle_bag::<SingleInstance>()); // req-piece-fall
                    }
                    after_action(&machine.s4.s3.s2, now, &mut run);
                    t6::view::render(
                        &constants,
                        machine,
                        t1::instance::piece_color,
                        run.banner.as_ref(),
                        Some(&font),
                    );
                }
            }
        }

        if let Some(b) = &run.banner {
            if now - b.t > BANNER_SECS {
                run.banner = None;
            }
        }

        next_frame().await;
    }
}
