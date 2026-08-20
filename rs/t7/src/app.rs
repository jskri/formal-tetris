//! The screen/menu/lobby machinery shared by every binary built on top of
//! `t7`: the level→fall-speed schedule, single-player dispatch (also reused
//! as the S6/S8 filler engine), the generic DAS/ARR input engine, menu
//! navigation, and each multiplayer lobby screen's state and rendering.
//!
//! Screen-by-screen mapping to `implementation.md` §15.0's own `S1`–`S10`
//! table:
//!
//! | screen | §15.0 | notes |
//! |---|---|---|
//! | Mode Select | `S1` | "Single Player" / "Multi Player" — `step_mode_select`/`draw_mode_select` |
//! | Role Select | `S2` | "Host" / "Join" — `step_role_select`/`draw_role_select` |
//! | Single Player | — | served by `t6::model::Machine` directly (§0.2), `t7::model::Machine` never constructed; stays a caller-owned screen, not a step function here |
//! | Host Lobby | `S3` | name field, "Add connection", code exchange, joiner list, "Start" — `step_host_lobby`/`draw_host_lobby` |
//! | Join Lobby | `S4` | name field, own code, "paste host's code", "Connect" — `step_join_lobby`/`draw_join_lobby` |
//! | Waiting Room | `S6` | `t6` filler game + roster + "waiting for host" — `step_waiting_session`/`draw_waiting_overlay` |
//! | Playing | `S7`/`S8` | `S8` is mid-match filler, not a distinct screen — `step_playing_gameplay`/`step_playing_transition` |
//! | Winner | `S9` | "You win" / "Winner: `<name>`", "Rematch", "Leave" — `step_winner`/`draw_winner_screen` |
//! | Host Lost | `S10` | "Connection to host lost.", "Return to menu" — `step_host_lost`/`draw_host_lost` |
//!
//! `S5` (Rejoin) has no step function either: §15.0 marks its only action
//! "automatic", so it is `Session::rejoin` called on the way from Winner to
//! Waiting — there is no frame on which it would be drawn.
//!
//! A step function mutates the shared state it's given in place and returns
//! a small outcome enum naming which transition happened; constructing the
//! caller's own next screen value — including any caller-specific extra
//! fields — always stays in the caller's own glue, since that's the one
//! place different binaries built on this module are meant to differ.

use crate::misc::Action;
use crate::net::{ConnectionCode, NetWorkerHandle};
use crate::session::{
    connect_to, endpoint_discovered, find_winner, fresh_holes, make_bags_fn, shuffle_bag, Endpoint,
    Instance, PendingEndpoint, Role, Session,
};
// Test-only: production always discovers an `Endpoint` via `PendingEndpoint`
// on a background thread; `mint_endpoint` stays synchronous for the one test
// needing a second, independent endpoint minted inline, standing in for a
// separate process's own joiner.
#[cfg(test)]
use crate::session::mint_endpoint;
use crate::text::{
    copy_to_clipboard, drive_backspace_repeat, poll_text_edit, TextInput, NAME_FIELD_MAX_LEN,
};
use crate::view;
use gilrs::{Button, Gamepad};
use macroquad::prelude::*;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use t1::misc::{random_piece, LogicalKeys, RepeatTimer, ARR, DAS_DELAY};
use t1::model::Params as T1Params;
use t6::model::T6MachineExt as _;

/// Single-player runs directly on `t6::model::Machine` (`t7::model::Machine::new`
/// asserts `player_count > 1`, so one is never constructed here); the filler
/// game reuses this same engine, hence `t1::instance::Tetris` rather than
/// `t7::instance::Tetris`.
pub type SingleInstance = t1::instance::Tetris;

const BASE_PERIOD_SECS: f64 = 1.0;
const MIN_PERIOD_SECS: f64 = 0.016;
const EPS: f64 = 1e-6;

/// spec: §15.0 (S7→S8 gating) — how long a player's own "GAME OVER" stays on
/// screen before the S8 filler becomes reachable.
pub const GAMEOVER_FILLER_DELAY_SECS: f64 = 1.0;

pub fn fall_period(level: u64) -> f64 {
    let base = (0.8 - (level as f64 - 1.0) * 0.007).max(EPS);
    let secs = base.powf(level as f64 - 1.0);
    (BASE_PERIOD_SECS * secs).max(MIN_PERIOD_SECS)
}

/// spec: §15.7 — level→fall-speed schedule and transient banner, unchanged
/// in shape from earlier layers.
pub struct RunState {
    pub prev_level: u64,
    pub current_gravity_period: f64,
    pub last_fall: f64,
    pub prev_total_cleared_lines: u64,
    pub banner: Option<view::Banner>,
}

impl RunState {
    pub fn fresh(now: f64) -> Self {
        RunState {
            prev_level: 1,
            current_gravity_period: fall_period(1),
            last_fall: now,
            prev_total_cleared_lines: 0,
            banner: None,
        }
    }
}

/// A level-up or line-clear observed by `after_action`, for a caller that
/// wants to react to it (e.g. play a sound) without duplicating the
/// detection logic itself.
pub struct AfterActionEvents {
    pub level_up: Option<u64>,
    pub clear: Option<ClearEvent>,
}

pub struct ClearEvent {
    pub lines: u64,
    pub perfect_clear: bool,
    pub combo: u64,
}

/// spec: §15.7 — generic over the instance so both engines share this one
/// copy of the level/banner logic; T7's own machine reaches its `t2`-level
/// state as `machine.s6.s4.s3.s2`, single-player one hop shallower as
/// `machine.s4.s3.s2`, so this takes the `t2` state directly.
pub fn after_action<P: T1Params>(
    s2: &t2::model::Machine<P>,
    now: f64,
    run: &mut RunState,
) -> AfterActionEvents {
    let mut events = AfterActionEvents {
        level_up: None,
        clear: None,
    };
    if s2.level != run.prev_level {
        events.level_up = Some(s2.level);
        run.current_gravity_period = fall_period(s2.level);
        run.prev_level = s2.level;
        run.last_fall = now;
    }
    if s2.total_cleared_lines > run.prev_total_cleared_lines {
        events.clear = Some(ClearEvent {
            lines: s2.total_cleared_lines - run.prev_total_cleared_lines,
            perfect_clear: s2.perfect_clear,
            combo: s2.combo,
        });
        run.banner = Some(view::Banner {
            combo: s2.combo,
            perfect_clear: s2.perfect_clear,
            t: now,
        });
    }
    run.prev_total_cleared_lines = s2.total_cleared_lines;
    events
}

// ── App state: the multiplayer lobby screens ────────────────────────────

/// spec: §15.1a′ — S3's four-phase connection sub-flow: Idle → EnteringCode
/// (paste box, nothing minted) → Discovering (background STUN) → Connecting
/// (host's code for that pairing appears). A fresh endpoint per joiner is
/// required by the star topology.
///
/// The states keep "what socket is minted" and "what code is on screen" as
/// one thing, on purpose: `Connecting`'s `code` is captured from the *same*
/// `Endpoint` `poll_add_discovery` goes on to call `connect_to` with, before
/// it is consumed, so there is no second endpoint for the display to drift
/// from.
enum AddConnection {
    Idle,
    /// The paste box is open; nothing has been minted yet.
    EnteringCode(TextInput),
    /// `try_add` validated the typed code and kicked off this pairing's own
    /// STUN lookup on a background thread, so entering this state never
    /// blocks the frame loop. `poll_add_discovery` polls `pending` each
    /// frame and, once resolved, connects using `joiner_code`.
    Discovering {
        pending: PendingEndpoint,
        joiner_code: ConnectionCode,
    },
    /// `poll_add_discovery` succeeded: `code` is this pairing's own code,
    /// already connected; `peer_id` is this joiner's stable `Peer::id` (not
    /// a `Vec` position, which a `Leave` elsewhere in the lobby can shift —
    /// `Peer::id`'s own doc comment), polled each frame (`poll_add_completion`)
    /// for "has this one actually joined" — the auto-clear back to `Idle`.
    Connecting {
        code: String,
        peer_id: u64,
    },
}

/// `S3`. spec: §15.1a — `focus` is a clamped index into 3 stops: `0` name,
/// `1` the "Add player" button (or the joiner's-code field/display,
/// depending on `add`'s state), `2` "Start game" (`move_focus`).
/// Typing/backspace-repeat only ever reach field 1 while `add` is
/// `EnteringCode`.
pub struct HostLobby {
    /// A rematch-as-host transition (`step_winner`'s `RematchAsHost`) and a
    /// successful "Start game" (`HostLobbyOutcome::Started`) both need the
    /// caller to move this session on into the next screen, so it is `pub`
    /// unlike this struct's other fields — every other field is read only
    /// from within this module.
    pub session: Session,
    add: AddConnection,
    name: TextInput,
    focus: usize,
    status: String,
    backspace_repeat: Option<RepeatTimer>,
}

impl HostLobby {
    /// A fresh lobby around an already-existing `session` — the shape
    /// `step_winner`'s `RematchAsHost` transition needs (a caller cannot
    /// otherwise construct a `HostLobby` itself, since every field but
    /// `session` is private to this module).
    pub fn new(session: Session, name: TextInput) -> HostLobby {
        HostLobby {
            session,
            add: AddConnection::Idle,
            name,
            focus: 1,
            status: String::new(),
            backspace_repeat: None,
        }
    }

    /// spec: §15.1a′ — `[Ctrl+N]` "Add connection"; a no-op unless currently
    /// `Idle` (one connection in flight at a time).
    fn begin_add(&mut self) {
        if matches!(self.add, AddConnection::Idle) {
            self.add = AddConnection::EnteringCode(TextInput::default());
            self.focus = 1;
        }
    }

    /// spec: §15.1a′ — `[Esc]` while the paste box is open cancels *that*,
    /// not the whole lobby. A no-op once minting has actually started
    /// (`Connecting`): the ordinary `Esc` path (leave the lobby) applies
    /// there instead. Focus stays at `1` — `draw_host_lobby` still renders
    /// the "Add player" button there once back to `Idle`.
    fn cancel_add(&mut self) {
        if matches!(self.add, AddConnection::EnteringCode(_)) {
            self.add = AddConnection::Idle;
        }
    }

    /// `[Enter]` "Add" — only meaningful from `EnteringCode`. Validates and
    /// parses the typed code (local, so still synchronous) and, on success,
    /// kicks off that pairing's own STUN lookup in the background
    /// (`poll_add_discovery` picks up the result). On a parse failure,
    /// mutates only `self.status` — this method never sees the paste box's
    /// own text, so it can't wipe it; the caller only clears/replaces that
    /// on an actual transition.
    fn try_add(&mut self, typed: &str) {
        if !matches!(self.add, AddConnection::EnteringCode(_)) {
            return;
        }
        let Ok(joiner_code) = typed.trim().parse::<ConnectionCode>() else {
            self.status = "That doesn't look like a connection code.".into();
            return; // stay in EnteringCode — the paste box's own text is untouched
        };
        self.status = "Discovering your address…".into();
        self.add = AddConnection::Discovering {
            pending: PendingEndpoint::spawn(),
            joiner_code,
        };
        // Focus stays at 1: `draw_host_lobby`'s `match &self.add` always
        // renders something at that stop for every state from here on, so
        // there is never a moment with nothing there to focus.
    }

    /// Called once a frame: once `Discovering`'s background STUN lookup has
    /// resolved, mints the endpoint and connects, without blocking the
    /// caller.
    fn poll_add_discovery(&mut self) {
        let AddConnection::Discovering {
            pending,
            joiner_code,
        } = &self.add
        else {
            return;
        };
        let Some(result) = pending.poll() else { return }; // still discovering
        let joiner_code = *joiner_code;
        let Some(ep) = endpoint_discovered(result, &mut self.status) else {
            self.add = AddConnection::Idle;
            return;
        };
        // Captured before `connect_to` consumes `ep` — the code shown from
        // here on is always the socket actually wired into the connection.
        let code = ep.code().to_string();
        match connect_to(&self.session.net, ep, joiner_code) {
            Ok(conn) => {
                let peer_id = self.session.add_peer(conn);
                self.status = "Connecting… send this code to that player.".into();
                self.add = AddConnection::Connecting { code, peer_id };
            }
            Err(e) => {
                self.status = format!("Could not connect: {e}");
                self.add = AddConnection::Idle;
            }
        }
    }

    /// Called once a frame: once the pairing in `Connecting` has actually
    /// joined — the roster line is now the visible confirmation of success
    /// — the code display auto-clears.
    ///
    /// Resolves `peer_id` via its *current* slot (`Peer::id`), not a
    /// remembered `Vec` position: a `Leave` elsewhere in the lobby can shift
    /// positions while this pairing is still `Connecting`. If the peer is
    /// gone entirely, reset to `Idle` instead of staying stuck in
    /// "Connecting…" forever.
    fn poll_add_completion(&mut self) {
        let AddConnection::Connecting { peer_id, .. } = &self.add else {
            return;
        };
        match self.session.peers.iter().find(|p| p.id == *peer_id) {
            Some(p) if p.index.is_some() => {
                let name = p.name.clone();
                self.status = format!("{name} joined.");
                self.add = AddConnection::Idle;
                // Focus stays at 1 — same reasoning as `try_add` above.
            }
            Some(_) => {} // still connected, not yet joined
            None => {
                self.status = "Connection lost before that player joined.".into();
                self.add = AddConnection::Idle;
            }
        }
    }
}

/// `S4`. Both fields are always reachable: the host's code for this pairing
/// does not exist at all until the host has already processed this joiner's
/// own code, so there is no invalid code to paste even before one exists.
pub struct JoinLobby {
    endpoint: EndpointState,
    name: TextInput,
    entry: TextInput,
    focus: usize, // 0 = name, 1 = your code (read-only), 2 = host's code, 3 = Connect
    status: String,
    backspace_repeat: Option<RepeatTimer>,
}

/// This peer's own `Endpoint`, discovered on a background thread
/// (`PendingEndpoint`) so the STUN round trip never blocks the frame loop.
enum EndpointState {
    Discovering(PendingEndpoint),
    Ready(Endpoint),
    Failed,
}

/// `S9`. `winner` is the roster index `find_winner` resolved, kept so the
/// screen names the same player for as long as it is shown. Both fields are
/// `pub`: a caller constructs one directly (from `PlayingTransition::ToWinner`)
/// and, on rematch, extracts `.session` back out.
pub struct Winner {
    pub session: Session,
    pub winner: Option<usize>,
}

pub fn fresh_single() -> t6::model::Machine<SingleInstance> {
    t6::model::Machine::new(
        make_bags_fn::<SingleInstance>(),
        random_piece::<SingleInstance>,
    )
}

/// spec: §15.1a — falls back to `fallback` (the literal the field was
/// seeded with) when blank, so `Join` never carries an empty string.
fn entered_name(field: &TextInput, fallback: &str) -> String {
    let t = field.text.trim();
    if t.is_empty() {
        fallback.to_owned()
    } else {
        t.to_owned()
    }
}

// ── Rendering: lobby screens ────────────────────────────────────────────

pub const TITLE_COLOR: Color = Color::new(0.95, 0.95, 0.95, 1.0);
pub const BODY_COLOR: Color = Color::new(0.75, 0.75, 0.75, 1.0);
pub const CODE_COLOR: Color = Color::new(0.4, 0.95, 0.6, 1.0);
pub const HINT_COLOR: Color = Color::new(0.55, 0.55, 0.55, 1.0);
pub const DISABLED_COLOR: Color = Color::new(0.38, 0.38, 0.38, 1.0);

const HOST_STOPS: usize = 3; // name, add-player, start-game
const JOIN_STOPS: usize = 4; // name, your-code, host's-code, connect

pub struct TextCursor {
    x: f32,
    y: f32,
    size: u16,
}

impl Default for TextCursor {
    fn default() -> Self {
        Self::new()
    }
}

impl TextCursor {
    pub fn new() -> TextCursor {
        let size = (screen_height() * 0.028).max(14.0) as u16;
        TextCursor {
            x: screen_width() * 0.08,
            y: screen_height() * 0.12,
            size,
        }
    }

    pub fn line(&mut self, text: &str, color: Color, font: Option<&Font>) {
        t2::view::draw_text_label(text, self.x, self.y, self.size, color, font);
        self.y += self.size as f32 * 1.6;
    }

    pub fn big(&mut self, text: &str, color: Color, font: Option<&Font>) {
        let size = self.size * 2;
        t2::view::draw_text_label(text, self.x, self.y, size, color, font);
        self.y += size as f32 * 1.5;
    }

    pub fn gap(&mut self) {
        self.y += self.size as f32 * 0.9;
    }

    /// spec: §15.1a — one labelled text field, focused stop highlighted in
    /// `CODE_COLOR`, others dim. `editable` is a rendering-only signal (no
    /// caret when false) — a read-only-but-focusable field like "Your code"
    /// is still highlighted and copyable; actual input gating is the
    /// caller's own dispatch, not this flag.
    pub fn field(
        &mut self,
        label: &str,
        value: &str,
        focused: bool,
        enabled: bool,
        editable: bool,
        font: Option<&Font>,
    ) {
        let color = if !enabled {
            DISABLED_COLOR
        } else if focused {
            CODE_COLOR
        } else {
            BODY_COLOR
        };
        let caret = if focused && enabled && editable {
            "_"
        } else {
            ""
        };
        let marker = if focused && enabled { ">" } else { " " };
        self.line(&format!("{marker} {label}: {value}{caret}"), color, font);
    }

    /// One line of action text ("Add player", "Start game", "Connect") —
    /// same focus/enabled visual language as `field()`, minus the
    /// `label: value` shape and caret, since there's nothing to type.
    pub fn button(&mut self, text: &str, focused: bool, enabled: bool, font: Option<&Font>) {
        let color = if !enabled {
            DISABLED_COLOR
        } else if focused {
            CODE_COLOR
        } else {
            BODY_COLOR
        };
        let marker = if focused && enabled { ">" } else { " " };
        self.line(&format!("{marker} {text}"), color, font);
    }
}

/// `S1` Mode Select — "Single Player" / "Multi Player", §15.0's own two
/// labels and nothing else. `hint_suffix` is appended verbatim to the hint
/// line, letting a caller add its own key hints (e.g. a mute toggle)
/// without forking this function.
pub fn draw_mode_select(selected: usize, hint_suffix: &str, font: Option<&Font>) {
    clear_background(t2::view::BG_COLOR);
    let mut c = TextCursor::new();
    c.big("TETRIS", TITLE_COLOR, font);
    c.gap();
    c.button("Single Player", selected == 0, true, font);
    c.button("Multi Player", selected == 1, true, font);
    c.gap();
    c.line(&format!("[Esc] quit{hint_suffix}"), HINT_COLOR, font);
}

/// `S2` Role Select — "Host" / "Join".
pub fn draw_role_select(selected: usize, font: Option<&Font>) {
    clear_background(t2::view::BG_COLOR);
    let mut c = TextCursor::new();
    c.big("MULTI PLAYER", TITLE_COLOR, font);
    c.gap();
    c.button("Host", selected == 0, true, font);
    c.button("Join", selected == 1, true, font);
    c.gap();
    c.line("[Esc] back", HINT_COLOR, font);
}

/// `S3` Host Lobby — name field; "Add connection"; per pending connection
/// the generated code (read-only, copy) plus a paste box for the joiner's
/// own; the joiner list; "Start", enabled once the list has at least one
/// entry.
pub fn draw_host_lobby(lobby: &HostLobby, hint_suffix: &str, font: Option<&Font>) {
    clear_background(t2::view::BG_COLOR);
    let mut c = TextCursor::new();
    c.big("HOSTING", TITLE_COLOR, font);
    // Always drawn, even when empty, so a status message appearing/
    // disappearing never shifts every element below it.
    c.line(&lobby.status, HINT_COLOR, font);
    c.gap();

    c.field(
        "Your name",
        &lobby.name.text,
        lobby.focus == 0,
        true,
        true,
        font,
    );
    c.gap();

    // spec: §15.1a′ — the S3 sub-flow: Idle, then a paste box, then (once
    // connected) the host's own code for that pairing.
    match &lobby.add {
        AddConnection::Idle => c.button("Add player", lobby.focus == 1, true, font),
        AddConnection::EnteringCode(entry) => {
            c.field(
                "Joiner's code",
                &entry.text,
                lobby.focus == 1,
                true,
                true,
                font,
            );
            c.line(
                "Paste the joiner's code here (Enter to add, Esc to cancel).",
                HINT_COLOR,
                font,
            );
        }
        AddConnection::Discovering { .. } => {
            c.field("Host's code", "…", lobby.focus == 1, true, false, font);
            c.line("Discovering your address…", HINT_COLOR, font);
        }
        AddConnection::Connecting { code, .. } => {
            c.field("Host's code", code, lobby.focus == 1, true, false, font);
            c.line("Send this code to that player.", HINT_COLOR, font);
        }
    }
    c.gap();

    let roster = lobby.session.roster_names();
    let can_start = roster.len() >= 2;
    c.button("Start game", lobby.focus == 2, can_start, font);
    if !can_start {
        c.line("Not enough players.", HINT_COLOR, font);
    }
    c.gap();

    c.line("Players:", BODY_COLOR, font);
    for (i, name) in roster.iter().enumerate() {
        let who = if i == 0 { " (you)" } else { "" };
        c.line(&format!("  {}. {name}{who}", i + 1), BODY_COLOR, font);
    }
    c.gap();

    c.line(
        &format!("[Ctrl-C] copy   [Ctrl-V] paste   [Esc] back{hint_suffix}"),
        HINT_COLOR,
        font,
    );
}

/// `S4` Join Screen — name field; own generated code (read-only, copy); the
/// "paste host's code" box; "Connect".
pub fn draw_join_lobby(lobby: &JoinLobby, hint_suffix: &str, font: Option<&Font>) {
    clear_background(t2::view::BG_COLOR);
    let mut c = TextCursor::new();
    c.big("JOINING", TITLE_COLOR, font);
    // Always drawn, even when empty, so a status message appearing/
    // disappearing never shifts every element below it.
    c.line(&lobby.status, HINT_COLOR, font);
    c.gap();

    c.field(
        "Your name",
        &lobby.name.text,
        lobby.focus == 0,
        true,
        true,
        font,
    );
    c.gap();

    let ep = match &lobby.endpoint {
        EndpointState::Ready(ep) => ep,
        EndpointState::Discovering(_) => {
            c.line("Discovering your address…", BODY_COLOR, font);
            return;
        }
        EndpointState::Failed => {
            c.line(
                "No local socket — [Esc] back, then retry.",
                BODY_COLOR,
                font,
            );
            return;
        }
    };

    c.field(
        "Your code",
        &ep.code().to_string(),
        lobby.focus == 1,
        true,
        false,
        font,
    );
    c.line(
        "Send this code to the host (Ctrl-C to copy).",
        HINT_COLOR,
        font,
    );
    c.gap();

    c.field(
        "Host's code",
        &lobby.entry.text,
        lobby.focus == 2,
        true,
        true,
        font,
    );
    c.line(
        "Paste the host's code here (Ctrl-V to paste).",
        HINT_COLOR,
        font,
    );
    c.gap();

    let can_connect = !lobby.entry.text.trim().is_empty();
    c.button("Connect", lobby.focus == 3, can_connect, font);
    if !can_connect {
        c.line("Host code is missing.", HINT_COLOR, font);
    }
    c.gap();

    c.line(
        &format!("[Ctrl-C] copy   [Ctrl-V] paste   [Esc] back{hint_suffix}"),
        HINT_COLOR,
        font,
    );
}

/// `S6` Waiting Room — the filler game is drawn by `t6::view::render`
/// underneath; this is the roster and the "waiting for host" text §15.0
/// asks for, over the top of it.
pub fn draw_waiting_overlay(session: &Session, font: Option<&Font>) {
    let size = (screen_height() * 0.028).max(14.0) as u16;
    let mut y = screen_height() * 0.04;
    let x = screen_width() * 0.02;
    t2::view::draw_text_label("Waiting for host…", x, y, size, TITLE_COLOR, font);
    y += size as f32 * 1.6;
    for (i, name) in session.roster.iter().enumerate() {
        t2::view::draw_text_label(&format!("{}. {name}", i + 1), x, y, size, BODY_COLOR, font);
        y += size as f32 * 1.4;
    }
}

/// spec: §15.0 (S8) — the filler game is drawn by `t6::view::render`
/// underneath; this names *why* it's running, since the player already saw
/// their own "GAME OVER" and could otherwise mistake the filler for a fresh
/// single-player game.
pub fn draw_gameover_filler_overlay(font: Option<&Font>) {
    let size = (screen_height() * 0.028).max(14.0) as u16;
    let y = screen_height() * 0.04;
    let x = screen_width() * 0.02;
    t2::view::draw_text_label(
        "Game over. Waiting for the game to finish.",
        x,
        y,
        size,
        TITLE_COLOR,
        font,
    );
}

/// `S9` Winner Screen — "You win" when this peer is the winner, "Winner:
/// `<name>`" otherwise; "Rematch" and "Leave".
pub fn draw_winner_screen(w: &Winner, selected: usize, font: Option<&Font>) {
    clear_background(t2::view::BG_COLOR);
    let mut c = TextCursor::new();
    let me = w.session.my_index;
    let headline = match w.winner {
        Some(pl) if Some(pl) == me => "You win".to_owned(),
        Some(pl) => {
            let name = w
                .session
                .roster
                .get(pl)
                .cloned()
                .unwrap_or_else(|| format!("P{}", pl + 1));
            format!("Winner: {name}")
        }
        None => "Match over".to_owned(),
    };
    c.big(&headline, TITLE_COLOR, font);
    c.gap();
    c.button("Rematch", selected == 0, true, font);
    c.button("Leave", selected == 1, true, font);
}

/// `S10` Host Lost — "Connection to host lost."; "Return to menu".
pub fn draw_host_lost(font: Option<&Font>) {
    clear_background(t2::view::BG_COLOR);
    let mut c = TextCursor::new();
    c.big("Connection to host lost.", TITLE_COLOR, font);
    c.gap();
    c.button("Return to menu", true, true, font);
}

// ── Input ───────────────────────────────────────────────────────────────

/// spec: §15.7 — shared DAS/ARR engine, unchanged in shape from earlier
/// layers. Dispatch is a caller-supplied closure so multiplayer and
/// single-player share one copy of the timing logic despite differing
/// method signatures (`fix`-family calls take a `holes` closure on T7's
/// machine and not on T6's). Returns whether any action that could have
/// fixed a piece actually ran, so the caller knows to inspect the model's
/// own outgoing state.
pub fn process_input(
    gameover: bool,
    repeat: &mut HashMap<Action, RepeatTimer>,
    logical: &LogicalKeys,
    pad: Option<Gamepad<'_>>,
    now: f64,
    mut dispatch: impl FnMut(Action) -> bool,
) -> bool {
    if gameover {
        repeat.clear();
        return false;
    }
    let mut may_have_fixed = false;
    for action in Action::ALL {
        let is_held = action.is_held(logical, pad);
        match repeat.entry(action) {
            Entry::Vacant(e) => {
                if is_held {
                    may_have_fixed |= dispatch(action);
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
                    may_have_fixed |= dispatch(action);
                    e.get_mut().last_fire = now;
                }
            }
        }
    }
    may_have_fixed
}

/// The filler game's own input-dispatch-and-gravity step, shared by the
/// waiting room (`S6`) and the mid-match wait (`S8`). `logical_keys`/`pad`
/// are the caller's own already-current per-frame poll — polling happens
/// once per frame at the caller, not inside every function that needs it
/// (see `restart_filler_on_keypress` for the other half of this input
/// handling).
pub fn drive_filler_input(
    filler: &mut t6::model::Machine<SingleInstance>,
    key_repeat: &mut HashMap<Action, RepeatTimer>,
    logical_keys: &LogicalKeys,
    pad: Option<Gamepad<'_>>,
    run: &mut RunState,
    now: f64,
    mut dispatch: impl FnMut(Action, &mut t6::model::Machine<SingleInstance>) -> bool,
) -> AfterActionEvents {
    process_input(
        filler.s4.s3.s2.s1.gameover,
        key_repeat,
        logical_keys,
        pad,
        now,
        |action| dispatch(action, filler),
    );

    if !filler.s4.s3.s2.s1.gameover && now - run.last_fall >= run.current_gravity_period {
        run.last_fall = now;
        filler.fall_step(&shuffle_bag::<SingleInstance>()); // req-piece-fall
    }
    after_action(&filler.s4.s3.s2, now, run)
}

/// Tops the filler out onto the next keypress — not an outcome anyone is
/// waiting on, so it simply restarts, as single-player does. `true` iff it
/// restarted on this call, so the caller can act on the transition (e.g.
/// resetting its own per-match decoration state).
pub fn restart_filler_on_keypress(
    filler: &mut t6::model::Machine<SingleInstance>,
    run: &mut RunState,
    logical_keys: &LogicalKeys,
    pad: Option<Gamepad<'_>>,
    now: f64,
) -> bool {
    if filler.s4.s3.s2.s1.gameover && t1::misc::any_action_just_pressed(logical_keys, pad) {
        *filler = fresh_single();
        *run = RunState::fresh(now);
        true
    } else {
        false
    }
}

/// spec: §15.2 (`t6/implementation.md`) — try a plain rotation first, then
/// a wall kick on failure. Same shape as `t7::session::rotate`, over the T6
/// engine instead of T7's.
fn rotate_single(machine: &mut t6::model::Machine<SingleInstance>, cw: bool) -> bool {
    machine.rotate_piece(cw) || machine.rotate_kick_piece(cw)
}

/// Single-player dispatch, on a `t6::model::Machine`: same action set as
/// multiplayer dispatch, minus every garbage concern (`T6.v`'s
/// `FixPiece`/`FallStep`/`DropPiece` take no `holes`). The return value is
/// `process_input`'s one contract (whether this action could have fixed a
/// piece), not whether the underlying model call actually did anything — a
/// caller that wants that reads it from `on_result`.
pub fn fire_single(
    action: Action,
    machine: &mut t6::model::Machine<SingleInstance>,
    mut on_result: impl FnMut(bool),
) -> bool {
    match action {
        Action::Left => {
            on_result(machine.move_piece(0, -1));
            false
        }
        Action::Right => {
            on_result(machine.move_piece(0, 1));
            false
        }
        Action::Cw => {
            on_result(rotate_single(machine, true));
            false
        }
        Action::Ccw => {
            on_result(rotate_single(machine, false));
            false
        }
        Action::Hold => {
            on_result(machine.hold_piece(&shuffle_bag::<SingleInstance>()));
            false
        }
        Action::Down => {
            on_result(machine.fall_step(&shuffle_bag::<SingleInstance>()));
            true
        }
        Action::Drop => {
            on_result(machine.drop_piece(&shuffle_bag::<SingleInstance>()));
            true
        }
    }
}

/// spec: §15.1a — up/down navigation for menu-style screens (Mode/Role
/// Select, the Host/Join lobby stops); `count` is the number of focusable
/// stops, `current` the presently focused one. Clamps at both ends rather
/// than wrapping. `up` wins a same-frame `up && down` tie.
///
/// Clamps unconditionally, including the neither-pressed branch — `count`
/// can shrink between calls (e.g. `HostLobby`'s own "Start game" stop
/// becoming unreachable when a disconnect drops the roster back below 2
/// players), and `move_focus` is already called once per frame regardless
/// of input, so this is what makes a stale `current` self-heal on the very
/// next frame rather than sitting on a now-unreachable stop.
pub fn move_focus(current: usize, count: usize, up: bool, down: bool) -> usize {
    if count == 0 {
        return 0;
    }
    let next = if up {
        current.saturating_sub(1)
    } else if down {
        current + 1
    } else {
        current
    };
    next.min(count - 1)
}

/// Debounces the gamepad half of `poll_menu_nav`: `Gamepad::is_pressed` is
/// level state, not an edge — without this, holding a D-pad direction or
/// the confirm button would move/confirm every frame instead of once per
/// press. One lives per screen family (menu vs. lobby) in the caller's own
/// loop-local state, alongside `menu_index`/`lobby.focus`.
#[derive(Default)]
pub struct GamepadEdges {
    up: bool,
    down: bool,
    confirm: bool,
}

pub struct MenuNav {
    pub up: bool,
    pub down: bool,
    pub confirm: bool,
}

/// One frame's up/down/confirm reading for menu-style navigation — the menu
/// analogue of `poll_text_edit`. Keyboard is already edge-triggered
/// (`is_key_pressed`); gamepad D-pad up/down and button 0 (South) are
/// debounced against `prev`.
pub fn poll_menu_nav(pad: Option<Gamepad<'_>>, prev: &mut GamepadEdges) -> MenuNav {
    let pad_up = pad.is_some_and(|p| p.is_pressed(Button::DPadUp));
    let pad_down = pad.is_some_and(|p| p.is_pressed(Button::DPadDown));
    let pad_confirm = pad.is_some_and(|p| p.is_pressed(Button::South));
    let nav = MenuNav {
        up: is_key_pressed(KeyCode::Up) || (pad_up && !prev.up),
        down: is_key_pressed(KeyCode::Down) || (pad_down && !prev.down),
        confirm: is_key_pressed(KeyCode::Enter) || (pad_confirm && !prev.confirm),
    };
    prev.up = pad_up;
    prev.down = pad_down;
    prev.confirm = pad_confirm;
    nav
}

// ── Step functions: one per screen, mutate in place, return an outcome ──

pub enum ModeSelectOutcome {
    Stay,
    Quit,
    EnterSingle,
    EnterRoleSelect,
}

pub fn step_mode_select(escape: bool, nav: MenuNav, menu_index: &mut usize) -> ModeSelectOutcome {
    if escape {
        return ModeSelectOutcome::Quit;
    }
    *menu_index = move_focus(*menu_index, 2, nav.up, nav.down);
    match if nav.confirm { Some(*menu_index) } else { None } {
        Some(0) => ModeSelectOutcome::EnterSingle,
        Some(1) => ModeSelectOutcome::EnterRoleSelect,
        _ => ModeSelectOutcome::Stay,
    }
}

pub enum RoleSelectOutcome {
    Stay,
    Back,
    Host(Box<HostLobby>),
    Join(JoinLobby),
}

pub fn step_role_select(escape: bool, nav: MenuNav, menu_index: &mut usize) -> RoleSelectOutcome {
    if escape {
        return RoleSelectOutcome::Back;
    }
    *menu_index = move_focus(*menu_index, 2, nav.up, nav.down);
    match if nav.confirm { Some(*menu_index) } else { None } {
        Some(0) => {
            // spec: §15.1a′ — S3 opens Idle, no STUN lookup until a joiner's
            // code is in hand.
            RoleSelectOutcome::Host(Box::new(HostLobby::new(
                Session::new_host("Host".to_owned()),
                TextInput::with("Host".to_owned()),
            )))
        }
        Some(1) => {
            // Discovered in the background (`EndpointState`) — entering
            // this screen must not block on STUN.
            RoleSelectOutcome::Join(JoinLobby {
                endpoint: EndpointState::Discovering(PendingEndpoint::spawn()),
                name: TextInput::with("Player".to_owned()),
                entry: TextInput::default(),
                focus: 1,
                status: "Discovering your address…".into(),
                backspace_repeat: None,
            })
        }
        _ => RoleSelectOutcome::Stay,
    }
}

pub enum HostLobbyOutcome {
    Stay,
    Back,
    Started,
}

pub fn step_host_lobby(
    lobby: &mut HostLobby,
    escape: bool,
    pad: Option<Gamepad<'_>>,
    menu_pad: &mut GamepadEdges,
    run: &mut RunState,
    key_repeat: &mut HashMap<Action, RepeatTimer>,
    now: f64,
) -> HostLobbyOutcome {
    // [Esc] inside the paste sub-dialog cancels that (`HostLobby::cancel_add`),
    // not the whole lobby.
    let entering_code = matches!(lobby.add, AddConnection::EnteringCode(_));
    if escape && entering_code {
        lobby.cancel_add();
        return HostLobbyOutcome::Stay;
    } else if escape {
        return HostLobbyOutcome::Back;
    }

    lobby.session.pump(now);
    lobby.poll_add_discovery();
    lobby.poll_add_completion();

    let ctrl = is_key_down(KeyCode::LeftControl) || is_key_down(KeyCode::RightControl);
    let nav = poll_menu_nav(pad, menu_pad);
    // "Start game" (stop 2) is disabled below < 2 players — a disabled
    // stop renders with no focus marker at all (`TextCursor::button`), so
    // navigation must not be able to land there while it's unreachable.
    let can_start = lobby.session.roster_names().len() >= 2;
    let host_reachable_stops = if can_start {
        HOST_STOPS
    } else {
        HOST_STOPS - 1
    };
    lobby.focus = move_focus(lobby.focus, host_reachable_stops, nav.up, nav.down);
    if is_key_pressed(KeyCode::Tab) {
        lobby.focus = move_focus(lobby.focus, host_reachable_stops, false, true);
    }

    let edit = poll_text_edit();
    if lobby.focus == 0 {
        lobby.name.apply(&edit, NAME_FIELD_MAX_LEN);
        // The name only matters at Start (the host's own roster slot is
        // read from it then), so it is free to keep changing until that
        // moment.
        lobby.session.my_name = entered_name(&lobby.name, "Host");
        drive_backspace_repeat(&mut lobby.name, &mut lobby.backspace_repeat, now);
    } else if lobby.focus == 1 {
        if let AddConnection::EnteringCode(entry) = &mut lobby.add {
            entry.apply(&edit, NAME_FIELD_MAX_LEN);
            drive_backspace_repeat(entry, &mut lobby.backspace_repeat, now);
        } else {
            lobby.backspace_repeat = None;
        }
    } else {
        lobby.backspace_repeat = None;
    }
    if edit.copy {
        match lobby.focus {
            0 => copy_to_clipboard("Your name", &lobby.name.text, &mut lobby.status),
            1 => match &lobby.add {
                AddConnection::EnteringCode(entry) => {
                    copy_to_clipboard("Joiner's code", &entry.text, &mut lobby.status)
                }
                AddConnection::Connecting { code, .. } => {
                    copy_to_clipboard("Host's code", code, &mut lobby.status)
                }
                _ => lobby.status = "No code to copy yet.".into(),
            },
            _ => lobby.status = "Nothing to copy from this field.".into(),
        }
    }

    // §15.0's "Add connection". Ctrl-modified, not a bare N: this screen
    // has live text fields, and `N` is in the connection code's own
    // Crockford alphabet. Kept as a power-user alias alongside Enter/
    // gamepad-confirm on the focused "Add player" stop below.
    if ctrl && is_key_pressed(KeyCode::N) {
        lobby.begin_add();
    }
    if nav.confirm && lobby.focus == 1 {
        if matches!(lobby.add, AddConnection::Idle) {
            lobby.begin_add();
        } else if let AddConnection::EnteringCode(entry) = &lobby.add {
            // Read without mutating: on a parse failure `try_add` stays in
            // `EnteringCode` and the field must still hold what was typed,
            // so a typo can be corrected instead of losing everything.
            if !entry.text.trim().is_empty() {
                let typed = entry.text.trim().to_owned();
                lobby.try_add(&typed);
            }
        }
    }

    // §15.0's "Start": freeze the roster, send Start to all, own transition
    // to S7. `[Ctrl+S]` stays as a power-user alias alongside Enter/
    // gamepad-confirm on the focused "Start game" stop.
    let start_requested = (ctrl && is_key_pressed(KeyCode::S)) || (nav.confirm && lobby.focus == 2);
    if start_requested && lobby.session.start_match() {
        *run = RunState::fresh(now);
        key_repeat.clear();
        return HostLobbyOutcome::Started;
    }
    HostLobbyOutcome::Stay
}

pub enum JoinLobbyOutcome {
    Stay,
    Back,
    Connected(Box<Session>),
}

pub fn step_join_lobby(
    lobby: &mut JoinLobby,
    escape: bool,
    pad: Option<Gamepad<'_>>,
    menu_pad: &mut GamepadEdges,
    run: &mut RunState,
    key_repeat: &mut HashMap<Action, RepeatTimer>,
    now: f64,
) -> JoinLobbyOutcome {
    if escape {
        return JoinLobbyOutcome::Back;
    }
    if let EndpointState::Discovering(pending) = &lobby.endpoint {
        if let Some(result) = pending.poll() {
            lobby.endpoint = match endpoint_discovered(result, &mut lobby.status) {
                Some(ep) => EndpointState::Ready(ep),
                None => EndpointState::Failed,
            };
        }
    }
    let nav = poll_menu_nav(pad, menu_pad);
    // "Connect" (stop 3) is disabled until "Host's code" has text — same
    // reasoning as Host Lobby's "Start game": a disabled stop renders with
    // no focus marker, so navigation must not be able to land there.
    let can_connect = !lobby.entry.text.trim().is_empty();
    let join_reachable_stops = if can_connect {
        JOIN_STOPS
    } else {
        JOIN_STOPS - 1
    };
    lobby.focus = move_focus(lobby.focus, join_reachable_stops, nav.up, nav.down);
    if is_key_pressed(KeyCode::Tab) {
        lobby.focus = move_focus(lobby.focus, join_reachable_stops, false, true);
    }

    let edit = poll_text_edit();
    match lobby.focus {
        0 => {
            lobby.name.apply(&edit, NAME_FIELD_MAX_LEN);
            drive_backspace_repeat(&mut lobby.name, &mut lobby.backspace_repeat, now);
        }
        2 => {
            lobby.entry.apply(&edit, NAME_FIELD_MAX_LEN);
            drive_backspace_repeat(&mut lobby.entry, &mut lobby.backspace_repeat, now);
        }
        _ => lobby.backspace_repeat = None,
    }
    if edit.copy {
        match lobby.focus {
            0 => copy_to_clipboard("Your name", &lobby.name.text, &mut lobby.status),
            1 => match &lobby.endpoint {
                EndpointState::Ready(ep) => {
                    copy_to_clipboard("Your code", &ep.code().to_string(), &mut lobby.status)
                }
                EndpointState::Discovering(_) => {
                    lobby.status = "Still discovering your address…".into()
                }
                EndpointState::Failed => lobby.status = "No local socket — nothing to copy.".into(),
            },
            2 => copy_to_clipboard("Host's code", &lobby.entry.text, &mut lobby.status),
            _ => lobby.status = "Nothing to copy from this field.".into(),
        }
    }

    // §15.0's "Connect" — activates only when the Connect button itself is
    // focused, matching the disabled-until-non-empty gating above (Enter
    // on the "Host's code" field is otherwise a no-op, not a submit).
    let connect_requested = nav.confirm && lobby.focus == 3;
    if connect_requested && !lobby.entry.text.trim().is_empty() {
        // Read without mutating — a parse failure must leave the typed text
        // in place for the player to fix, the same fix `step_host_lobby`'s
        // own connect handling gets.
        let parsed = lobby.entry.text.trim().parse::<ConnectionCode>();
        match parsed {
            Err(()) => lobby.status = "That doesn't look like a connection code.".into(),
            Ok(code) => match std::mem::replace(&mut lobby.endpoint, EndpointState::Failed) {
                EndpointState::Ready(ep) => {
                    lobby.entry.take();
                    let net = NetWorkerHandle::spawn();
                    match connect_to(&net, ep, code) {
                        Ok(conn) => {
                            let session =
                                Session::new_joiner(net, conn, entered_name(&lobby.name, "Player"));
                            *run = RunState::fresh(now);
                            key_repeat.clear();
                            return JoinLobbyOutcome::Connected(Box::new(session));
                        }
                        Err(e) => lobby.status = format!("Could not connect: {e}"),
                    }
                }
                EndpointState::Discovering(pending) => {
                    lobby.status = "Still discovering your address — one moment.".into();
                    lobby.endpoint = EndpointState::Discovering(pending); // still legitimately in flight
                }
                EndpointState::Failed => {
                    lobby.status = "No local socket — [Esc] back and retry.".into()
                }
            },
        }
    }
    JoinLobbyOutcome::Stay
}

pub enum WaitingOutcome {
    Stay,
    Left,
    ToPlaying,
    HostLost,
}

/// Only the roster/handshake half of the waiting room — driving the filler
/// game and rendering both stay with the caller (`WaitingOutcome::Stay`),
/// since they need loop-local state (`RunState`, `key_repeat`, the current
/// `LogicalKeys`/gamepad poll, the font) this function has no reason to
/// take.
pub fn step_waiting_session(session: &mut Session, escape: bool, now: f64) -> WaitingOutcome {
    if escape {
        session.leave();
        return WaitingOutcome::Left;
    }
    session.pump(now);
    if session.started() {
        // §15.0: START received → S7.
        WaitingOutcome::ToPlaying
    } else if session.noticed_disconnect {
        // spec: §15.0 (S10) — in the waiting room there is no Machine to
        // resolve a winner, so a dropped link always goes here.
        WaitingOutcome::HostLost
    } else {
        WaitingOutcome::Stay
    }
}

pub enum PlayingTransition {
    Continue,
    ToWinner {
        winner: Option<usize>,
    },
    ToHostLost,
    /// Still waiting out `GAMEOVER_FILLER_DELAY_SECS`/for a keypress before
    /// entering the filler — informational only, the caller has nothing
    /// further to do (the wait's own start time is already recorded in
    /// `own_gameover_since`, mutated in place by this call).
    GameoverWaitStarted,
    EnteredFiller,
}

/// spec: §15.0 — transitions out of S7/S8: a resolved winner takes S9 even
/// if the link drops immediately after, so `find_winner` is consulted
/// before `noticed_disconnect`. `EnteredFiller` is signaled, not executed —
/// the caller still owns `filler`/`run`/`key_repeat` (and whatever else it
/// wants to reset on this exact transition).
pub fn step_playing_transition(
    session: &Session,
    filler_is_none: bool,
    own_gameover_since: &mut Option<f64>,
    logical_keys: &LogicalKeys,
    pad: Option<Gamepad<'_>>,
    now: f64,
) -> PlayingTransition {
    let outcome = session.machine.as_ref().map(|m| {
        (
            find_winner(m),
            m.gameover_view[m.my_index],
            session.noticed_disconnect,
        )
    });
    match outcome {
        Some((Some(w), _, _)) => PlayingTransition::ToWinner { winner: Some(w) },
        Some((None, _, true)) => PlayingTransition::ToHostLost,
        Some((None, true, false)) if filler_is_none => {
            // spec: §15.0 (S7→S8 gating) — the real Machine keeps rendering
            // for GAMEOVER_FILLER_DELAY_SECS, then any key/gamepad press
            // swaps in the filler.
            let since = *own_gameover_since.get_or_insert(now);
            if now - since >= GAMEOVER_FILLER_DELAY_SECS
                && t1::misc::any_action_just_pressed(logical_keys, pad)
            {
                PlayingTransition::EnteredFiller
            } else {
                PlayingTransition::GameoverWaitStarted
            }
        }
        _ => PlayingTransition::Continue,
    }
}

/// The input+gravity+`after_action` block for S7's real match — call only
/// once the caller has checked `playing.filler.is_none()` (S8 runs the
/// filler instead, via `drive_filler_input`). `dispatch` is the caller's
/// own per-action broadcast (`Session::fire_and_broadcast` wrapping
/// `t7::session::fire`, or a decorated version of the same); the periodic
/// gravity tick bypasses it and calls `fall_step` directly — gravity is not
/// itself an `Action`.
#[allow(clippy::too_many_arguments)]
pub fn step_playing_gameplay(
    session: &mut Session,
    key_repeat: &mut HashMap<Action, RepeatTimer>,
    logical_keys: &LogicalKeys,
    pad: Option<Gamepad<'_>>,
    run: &mut RunState,
    now: f64,
    wm: i64,
    mut dispatch: impl FnMut(Action, &mut crate::model::Machine<Instance>) -> bool,
) -> Option<AfterActionEvents> {
    let gameover = session
        .machine
        .as_ref()
        .map(|m| m.s6.s4.s3.s2.s1.gameover)?;
    // `fire_and_broadcast` samples `was_gameover`/`pre_target` and
    // broadcasts immediately around each individual fixing call — not
    // aggregated across the frame — since `Down`'s own ARR repeat and a
    // fresh `Drop` press can both fire in the same `process_input` call
    // below (see `fire_and_broadcast`'s own doc comment).
    process_input(gameover, key_repeat, logical_keys, pad, now, |action| {
        session.fire_and_broadcast(|machine| dispatch(action, machine))
    });

    let gameover_now = session
        .machine
        .as_ref()
        .is_some_and(|m| m.s6.s4.s3.s2.s1.gameover);
    if !gameover_now && now - run.last_fall >= run.current_gravity_period {
        run.last_fall = now;
        session.fire_and_broadcast(|machine| {
            machine.fall_step(&shuffle_bag::<Instance>(), fresh_holes(wm))
        }); // req-piece-fall
    }
    session
        .machine
        .as_ref()
        .map(|m| after_action(&m.s6.s4.s3.s2, now, run))
}

pub enum WinnerOutcome {
    Stay,
    Leave,
    RematchAsHost,
    RematchAsJoiner,
}

/// The rematch-as-host `reset_for_rematch`/rematch-as-joiner `rejoin` call
/// happens here, in place on `winner.session` — the caller only needs to
/// extract `.session` back out afterward to build the next screen's value,
/// the same ownership pattern `HostLobbyOutcome::Started` and
/// `JoinLobbyOutcome::Connected` already use.
pub fn step_winner(
    winner: &mut Winner,
    pad: Option<Gamepad<'_>>,
    menu_pad: &mut GamepadEdges,
    menu_index: &mut usize,
    now: f64,
) -> WinnerOutcome {
    winner.session.pump(now);
    let nav = poll_menu_nav(pad, menu_pad);
    *menu_index = move_focus(*menu_index, 2, nav.up, nav.down);
    if !nav.confirm {
        return WinnerOutcome::Stay;
    }
    match *menu_index {
        0 => {
            // §15.0: host → S3 (fresh lobby, connections reused); joiner →
            // S5, which is automatic and so lands straight in S6.
            match winner.session.role {
                Role::Host => {
                    winner.session.reset_for_rematch();
                    WinnerOutcome::RematchAsHost
                }
                Role::Joiner => {
                    winner.session.rejoin(); // S5
                    WinnerOutcome::RematchAsJoiner
                }
            }
        }
        1 => {
            // §15.0: a joiner's Leave tells the host; the host's own Leave
            // sends nothing at all.
            winner.session.leave();
            WinnerOutcome::Leave
        }
        _ => unreachable!("only 2 stops"),
    }
}

pub fn step_host_lost(escape: bool, pad: Option<Gamepad<'_>>, menu_pad: &mut GamepadEdges) -> bool {
    let nav = poll_menu_nav(pad, menu_pad);
    escape || nav.confirm
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::net::NetWorkerHandle;
    use std::time::{Duration, Instant};

    /// Drives a `Session` with no display server and no macroquad context —
    /// used here only by `try_add_shows_the_code_of_the_endpoint_it_actually_connected`,
    /// which exercises `HostLobby::try_add` (private to this module) and so
    /// cannot live in the `t7::session` integration suite alongside the
    /// rest of the `Session`-level coverage (`tests/session_integration_test.rs`).
    fn pump_until(
        sessions: &mut [&mut Session],
        label: &str,
        mut done: impl FnMut(&[&mut Session]) -> bool,
    ) {
        let start = Instant::now();
        let mut t = 0.0f64;
        while start.elapsed() < Duration::from_secs(10) {
            for s in sessions.iter_mut() {
                s.pump(t);
            }
            if done(sessions) {
                return;
            }
            t += 0.05;
            std::thread::sleep(Duration::from_millis(5));
        }
        panic!("timed out waiting for: {label}");
    }

    /// Single-player runs the T6 engine directly (§15/§0.2), so a garbage
    /// cell is not merely absent but *unrepresentable*: `SingleInstance`'s
    /// `CellExtra` is `Infallible`. This is really a compile-time claim —
    /// the assertion below just pins it against an accidental switch to
    /// `t7::instance::Tetris`, which would silently make garbage
    /// constructible in single-player.
    #[test]
    fn single_player_board_cannot_represent_a_garbage_cell() {
        assert_eq!(
            std::any::type_name::<<SingleInstance as T1Params>::CellExtra>(),
            std::any::type_name::<std::convert::Infallible>(),
        );
        let m = fresh_single();
        assert!(
            !m.s4.s3.s2.s1.gameover,
            "a fresh single-player board is playable"
        );
        t5::model::check_invariants(&m);
    }

    /// The same `fire` contract as multiplayer, over the T6 engine: only
    /// `Down`/`Drop` reach a `fix_piece`.
    #[test]
    fn single_player_only_fixing_actions_report_that_they_may_have_fixed() {
        let mut m = fresh_single();
        for action in [
            Action::Left,
            Action::Right,
            Action::Cw,
            Action::Ccw,
            Action::Hold,
        ] {
            assert!(
                !fire_single(action, &mut m, |_| {}),
                "{action:?} cannot fix a piece"
            );
        }
        for action in [Action::Down, Action::Drop] {
            assert!(
                fire_single(action, &mut m, |_| {}),
                "{action:?} may fix a piece"
            );
        }
    }

    /// A single-player game actually plays: repeated hard drops fix pieces,
    /// advance the model, and keep `T6.Correct` holding at every step,
    /// eventually topping out — with no `t7::model::Machine` anywhere.
    #[test]
    fn single_player_plays_a_whole_game_without_a_t7_machine() {
        let mut m = fresh_single();
        let mut drops = 0;
        while !m.s4.s3.s2.s1.gameover && drops < 500 {
            fire_single(Action::Drop, &mut m, |_| {});
            t5::model::check_invariants(&m);
            drops += 1;
        }
        assert!(
            m.s4.s3.s2.s1.gameover,
            "hard-dropping in place must eventually top out"
        );
        assert!(drops > 1, "the game ran for more than a single piece");
    }

    /// spec: the code `try_add` puts on screen must be the code of the
    /// *same* socket it just connected — never a second, unrelated one.
    /// Proven over real loopback UDP, not just the `Session`-level roster
    /// machinery (already covered by `t7::session`'s own integration
    /// suite).
    #[test]
    fn try_add_shows_the_code_of_the_endpoint_it_actually_connected() {
        // A real Endpoint, minted synchronously via `mint_endpoint` — stands
        // in for a second process's own joiner on the same machine, so it
        // deliberately skips `PendingEndpoint`'s background-thread path.
        // Uses real `Endpoint::discover` rather than a hand-built loopback
        // one: a hand-built loopback joiner can only ever match the local
        // case, not the public one, leaving `best_target`'s choice untested
        // on a machine with internet access. Real discovery on both sides is
        // correct either way — same machine implies same public IP (or the
        // same `local_ipv4` fallback) on both sides, so `best_target`
        // resolves to a genuinely reachable address regardless of branch.
        let joiner_ep = mint_endpoint(&mut String::new())
            .expect("binding a local UDP socket must not fail in a test environment");
        let joiner_code = joiner_ep.code().to_string();

        let mut lobby = HostLobby {
            session: Session::new_host("Host".into()),
            add: AddConnection::Idle,
            name: TextInput::with("Host".into()),
            focus: 0,
            status: String::new(),
            backspace_repeat: None,
        };
        lobby.begin_add();
        lobby.try_add(&joiner_code);

        // `try_add` only kicks off the STUN lookup in the background —
        // poll until it resolves.
        let discover_start = Instant::now();
        while !matches!(lobby.add, AddConnection::Connecting { .. })
            && discover_start.elapsed() < Duration::from_secs(10)
        {
            lobby.poll_add_discovery();
            std::thread::sleep(Duration::from_millis(5));
        }

        let AddConnection::Connecting {
            code: host_code,
            peer_id,
        } = &lobby.add
        else {
            panic!("try_add with a well-formed code must reach Connecting, got a different state. status={}", lobby.status);
        };
        assert_eq!(
            *peer_id, 1,
            "the first Add is the host's first allocated peer id"
        );

        // Drive a *real* joiner Session against exactly the string just
        // shown on screen, and confirm the handshake actually completes —
        // the guarantee `try_add`'s own doc comment states: the shown code
        // always names the socket actually wired into the connection.
        let joiner_net = NetWorkerHandle::spawn();
        let mut joiner_session = Session::new_joiner(
            joiner_net.clone(),
            connect_to(
                &joiner_net,
                joiner_ep,
                host_code
                    .parse()
                    .expect("HostLobby must show a well-formed code"),
            )
            .unwrap(),
            "Joiner".into(),
        );
        let mut refs: Vec<&mut Session> = vec![&mut lobby.session, &mut joiner_session];
        pump_until(
            &mut refs,
            "the joiner's Join reaches the host's roster",
            |s| s[0].peers.first().is_some_and(|p| p.index.is_some()),
        );
        assert_eq!(
            lobby.session.roster_names().len(),
            2,
            "host plus the one real joiner"
        );

        lobby.poll_add_completion();
        assert!(
            matches!(lobby.add, AddConnection::Idle),
            "the display must auto-clear once that joiner has actually joined"
        );
        assert_eq!(
            lobby.focus, 1,
            "focus must stay on the Add-player stop, not jump back to the name field"
        );
    }

    /// `begin_add` must not mint a second connection out from under one
    /// already in progress — `Ctrl+N` is only offered while `Idle`.
    #[test]
    fn begin_add_is_a_no_op_once_a_connection_is_already_in_flight() {
        let mut lobby = HostLobby {
            session: Session::new_host("Host".into()),
            add: AddConnection::EnteringCode(TextInput::with("stale text".into())),
            name: TextInput::default(),
            focus: 1,
            status: String::new(),
            backspace_repeat: None,
        };
        lobby.begin_add();
        match &lobby.add {
            AddConnection::EnteringCode(entry) => assert_eq!(entry.text, "stale text", "must not reset an in-progress paste"),
            other => panic!("begin_add must not touch an in-flight EnteringCode, got a different state instead: not EnteringCode({other:?})", other = std::mem::discriminant(other)),
        }
    }

    /// `[Esc]` while pasting cancels just that, back to `Idle` — and mints
    /// nothing in the process, unlike `try_add`.
    #[test]
    fn cancel_add_returns_to_idle_without_minting_anything() {
        let mut lobby = HostLobby {
            session: Session::new_host("Host".into()),
            add: AddConnection::Idle,
            name: TextInput::default(),
            focus: 0,
            status: String::new(),
            backspace_repeat: None,
        };
        lobby.begin_add();
        assert!(matches!(lobby.add, AddConnection::EnteringCode(_)));
        assert_eq!(lobby.focus, 1);

        lobby.cancel_add();
        assert!(
            matches!(lobby.add, AddConnection::Idle),
            "cancel must return to Idle"
        );
        assert_eq!(
            lobby.focus, 1,
            "focus stays on the Add-player stop, not the name field"
        );
        assert!(
            lobby.session.peers.is_empty(),
            "cancelling before Add must never have touched the roster"
        );
    }

    /// A malformed code must not consume the paste box or leave `Idle` —
    /// the player can fix the typo without re-pressing `[Ctrl+N]`.
    #[test]
    fn try_add_with_a_malformed_code_stays_in_entering_code() {
        let mut lobby = HostLobby {
            session: Session::new_host("Host".into()),
            add: AddConnection::Idle,
            name: TextInput::default(),
            focus: 0,
            status: String::new(),
            backspace_repeat: None,
        };
        lobby.begin_add();
        lobby.try_add("not a connection code");
        assert!(
            matches!(lobby.add, AddConnection::EnteringCode(_)),
            "a parse failure must not leave EnteringCode"
        );
        assert!(
            lobby.session.peers.is_empty(),
            "nothing was ever minted, so nothing was ever connected"
        );
    }

    /// The real input path (`step_host_lobby`'s own connect handling) reads
    /// the typed text without mutating it, then only calls `try_add`, so a
    /// mistyped code stays intact for the player to correct rather than
    /// being silently wiped. `try_add` itself never touches the field, so
    /// this test pins that the field is only ever read, never taken.
    #[test]
    fn a_malformed_code_does_not_clear_the_paste_box() {
        let mut lobby = HostLobby {
            session: Session::new_host("Host".into()),
            add: AddConnection::EnteringCode(TextInput::with("not a connection code".into())),
            name: TextInput::default(),
            focus: 1,
            status: String::new(),
            backspace_repeat: None,
        };
        let AddConnection::EnteringCode(entry) = &lobby.add else {
            unreachable!()
        };
        let typed = entry.text.trim().to_owned();
        lobby.try_add(&typed);

        match &lobby.add {
            AddConnection::EnteringCode(entry) => {
                assert_eq!(entry.text, "not a connection code", "the typed text must survive a parse failure for the player to fix");
            }
            other => panic!("a parse failure must not leave EnteringCode, got a different state instead: not EnteringCode({other:?})", other = std::mem::discriminant(other)),
        }
    }

    /// spec: `Connecting` resolves its peer by the stable `peer_id`, not a
    /// raw `Vec` position — a `Leave` elsewhere in the lobby (§15.1b) can
    /// shift positions while this add is still in flight. A peer that's
    /// gone entirely must recover to `Idle`, not sit stuck forever.
    #[test]
    fn poll_add_completion_recovers_when_the_connecting_peer_is_gone() {
        let mut lobby = HostLobby {
            session: Session::new_host("Host".into()),
            add: AddConnection::Connecting {
                code: "AAAAAAAA-AAAAAAAA-AAAAAAAA-AAAAAAAA".into(),
                peer_id: 999,
            },
            name: TextInput::default(),
            focus: 1,
            status: String::new(),
            backspace_repeat: None,
        };
        assert!(
            lobby.session.peers.is_empty(),
            "no peer with id 999 (or any id) exists"
        );

        lobby.poll_add_completion();

        assert!(
            matches!(lobby.add, AddConnection::Idle),
            "a Connecting add whose peer no longer exists must recover to Idle, not stay stuck"
        );
        assert!(
            lobby.status.contains("lost"),
            "the status should say why, not silently reset: {}",
            lobby.status
        );
    }

    /// `move_focus` is plain `usize`/`bool` arithmetic with no macroquad
    /// dependency — unlike the rest of the lobby UI, this piece is cleanly
    /// unit-testable without a rendering/input runtime.
    #[test]
    fn move_focus_clamps_at_both_ends() {
        assert_eq!(move_focus(0, 3, true, false), 0, "up at the top stays put");
        assert_eq!(
            move_focus(2, 3, false, true),
            2,
            "down at the bottom stays put"
        );
    }

    #[test]
    fn move_focus_steps_one_at_a_time() {
        assert_eq!(move_focus(0, 3, false, true), 1);
        assert_eq!(move_focus(1, 3, false, true), 2);
        assert_eq!(move_focus(2, 3, true, false), 1);
        assert_eq!(move_focus(1, 3, true, false), 0);
    }

    #[test]
    fn move_focus_neither_direction_is_a_no_op() {
        assert_eq!(move_focus(1, 3, false, false), 1);
    }

    #[test]
    fn move_focus_up_wins_a_same_frame_tie() {
        assert_eq!(move_focus(1, 3, true, true), 0);
    }

    #[test]
    fn move_focus_with_zero_stops_stays_at_zero() {
        assert_eq!(move_focus(0, 0, true, false), 0);
        assert_eq!(move_focus(0, 0, false, true), 0);
    }

    /// A disconnect can shrink `count` (e.g. `HostLobby`'s reachable-stops
    /// count dropping below 3 when the roster falls under 2 players) between
    /// one frame and the next, with no nav key pressed on the frame the drop
    /// happens. `current` must not be left pointing past the new `count`.
    #[test]
    fn move_focus_clamps_a_stale_current_even_with_no_input() {
        assert_eq!(move_focus(2, 2, false, false), 1);
    }
}
