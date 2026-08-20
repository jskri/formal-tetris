//! spec: `implementation.md` §9, §0.4 — `session.rs`'s lobby/relay state
//! machine end to end: a full host + joiners over real loopback UDP, with no
//! display server, since `Session` never calls a macroquad API.

use std::net::{SocketAddr, UdpSocket};
use std::time::{Duration, Instant};
use t1::misc::random_piece;
use t1::model::Params;
use t7::misc::Action;
use t7::model::Machine;
use t7::net::{Destination, Message, NetWorkerHandle, Payload, Reliability, WireMessage};
use t7::session::{
    find_winner, fire, fresh_holes, make_bags_fn, take_rem_gen_garbage, Instance, Session,
};

/// Pumps every session in a tight loop until `done` holds or the deadline
/// passes.
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

fn loopback_pair() -> (UdpSocket, SocketAddr, UdpSocket, SocketAddr) {
    let a = UdpSocket::bind("127.0.0.1:0").expect("bind a");
    let b = UdpSocket::bind("127.0.0.1:0").expect("bind b");
    let (aa, ba) = (a.local_addr().unwrap(), b.local_addr().unwrap());
    (a, aa, b, ba)
}

/// Builds a host with `joiners` connected joiner sessions over real loopback
/// UDP, and runs the lobby to the point where every joiner has a roster
/// index.
fn lobby(joiners: usize) -> (Session, Vec<Session>) {
    let mut host = Session::new_host("Host".into());
    let mut js = Vec::new();
    for i in 0..joiners {
        let (hs, ha, jsock, ja) = loopback_pair();
        host.add_peer(
            host.net
                .register(
                    hs,
                    ja,
                    100 + i as u64,
                    t7::session::max_decoded_message_bytes(),
                )
                .expect("host conn"),
        );
        let net = NetWorkerHandle::spawn();
        let conn = net
            .register(
                jsock,
                ha,
                200 + i as u64,
                t7::session::max_decoded_message_bytes(),
            )
            .expect("joiner conn");
        js.push(Session::new_joiner(net, conn, format!("J{}", i + 1)));
    }
    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(&mut refs, "every joiner assigned a roster index", |s| {
            s[0].peers.iter().all(|p| p.index.is_some()) && s[0].peers.len() == joiners
        });
    }
    (host, js)
}

/// spec: `implementation.md` §15.1 — two joiners handshake and `Join`, get
/// roster indices 1 and 2, and every peer builds its own `Machine` on
/// `Start` with the index the host assigned it.
#[test]
fn lobby_assigns_roster_and_starts_a_match() {
    let (mut host, mut js) = lobby(2);
    assert_eq!(host.roster_names().len(), 3, "host + two joiners");

    assert!(host.start_match(), "start must fire with 3 players");
    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(&mut refs, "every joiner receives Start", |s| {
            s.iter().all(|x| x.started())
        });
    }

    assert_eq!(
        host.machine.as_ref().unwrap().my_index,
        0,
        "host is always roster index 0"
    );
    let mut indices: Vec<usize> = js
        .iter()
        .map(|j| j.machine.as_ref().unwrap().my_index)
        .collect();
    indices.sort();
    assert_eq!(indices, vec![1, 2], "joiners get distinct non-zero indices");
    for s in std::iter::once(&host).chain(js.iter()) {
        assert_eq!(
            s.machine.as_ref().unwrap().gameover_view.len(),
            3,
            "player_count agreed by everyone"
        );
    }
}

/// spec: `implementation.md` §15.4 — the host relays joiner-to-joiner
/// traffic down the recipient's own connection. Joiner 1 addresses garbage
/// to joiner 2, which has no direct channel to it, and it must land via
/// `receive_garbage`.
#[test]
fn garbage_is_relayed_between_two_joiners_through_the_host() {
    let (mut host, mut js) = lobby(2);
    host.start_match();
    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(&mut refs, "every joiner receives Start", |s| {
            s.iter().all(|x| x.started())
        });
    }
    let (a, b) = (js[0].my_index.unwrap(), js[1].my_index.unwrap());
    assert_ne!(a, b);

    js[0].send_routed(Destination::Single(b), Payload::Garbage { amount: 4 });
    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(&mut refs, "joiner 2 receives the relayed garbage", |s| {
            s.iter()
                .any(|x| x.my_index == Some(b) && x.machine.as_ref().unwrap().garbage == 4)
        });
    }
    let other = js.iter().find(|j| j.my_index == Some(a)).unwrap();
    assert_eq!(
        other.machine.as_ref().unwrap().garbage,
        0,
        "garbage went to the addressee only"
    );
    assert_eq!(
        host.machine.as_ref().unwrap().garbage,
        0,
        "the relay does not consume or duplicate it"
    );
}

/// Hardening: a peer-supplied `Garbage.amount` is unvalidated — negative
/// would break `check_invariants`'s `>= 0`, and a huge value risks
/// overflowing the `+=` in `receive_garbage`. Clamped to `[0, hm]`, `hm`
/// being materialization's own ceiling.
#[test]
fn garbage_amount_is_clamped_to_the_board_height() {
    let m = Machine::<Instance>::new(0, 2, make_bags_fn::<Instance>(), random_piece::<Instance>);
    let hm = m.s6.s4.s3.s2.s1.mg.len() as i64;
    let mut host = Session::new_host("Host".into());
    host.machine = Some(m);

    host.apply_local(1, Payload::Garbage { amount: -5 });
    assert_eq!(
        host.machine.as_ref().unwrap().garbage,
        0,
        "negative amount floors at 0"
    );

    host.apply_local(1, Payload::Garbage { amount: i64::MAX });
    assert_eq!(
        host.machine.as_ref().unwrap().garbage,
        hm,
        "huge amount ceilings at board height"
    );
}

/// `Machine::fix_piece` advances `target` to the next candidate in the same
/// call that produces this clear's garbage, so `broadcast_after_fix` needs
/// the pre-fix target rather than reading `m.target` afterward. Sets
/// `m.target` to a different player than `pre_target` and confirms the
/// garbage reaches `pre_target`, not wherever `m.target` moved on to.
#[test]
fn garbage_goes_to_the_pre_fix_target_not_the_post_fix_one() {
    let (mut host, mut js) = lobby(2);
    host.start_match();
    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(&mut refs, "every joiner receives Start", |s| {
            s.iter().all(|x| x.started())
        });
    }
    let (a, b) = (js[0].my_index.unwrap(), js[1].my_index.unwrap());
    let sender = js.iter_mut().find(|j| j.my_index == Some(a)).unwrap();
    let pre_target = 0; // the host — this clear's real, intended recipient
    {
        let m = sender.machine.as_mut().unwrap();
        m.rem_gen_garbage = 4;
        m.target = b; // already advanced past pre_target, as fix_piece would leave it
    }
    sender.broadcast_after_fix(false, pre_target);

    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(
            &mut refs,
            "the host receives the garbage credited before the advance",
            |s| s[0].machine.as_ref().unwrap().garbage == 4,
        );
    }
    assert_eq!(
        host.machine.as_ref().unwrap().garbage,
        4,
        "went to pre_target (the host), not m.target"
    );
    let other = js.iter().find(|j| j.my_index == Some(b)).unwrap();
    assert_eq!(
        other.machine.as_ref().unwrap().garbage,
        0,
        "not to m.target's already-advanced value"
    );
}

/// A broadcast (`to: None`) reaches every other player — the host by
/// applying it locally, the other joiner by relay — and lands as
/// `receive_gameover(from)` carrying the original sender's index.
#[test]
fn gameover_broadcast_reaches_host_and_the_other_joiner() {
    let (mut host, mut js) = lobby(2);
    host.start_match();
    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(&mut refs, "every joiner receives Start", |s| {
            s.iter().all(|x| x.started())
        });
    }
    let sender = js[0].my_index.unwrap();

    js[0].send_routed(Destination::Broadcast, Payload::Gameover);
    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(
            &mut refs,
            "gameover observed by host and the other joiner",
            |s| {
                s.iter().all(|x| {
                    x.my_index == Some(sender) || x.machine.as_ref().unwrap().gameover_view[sender]
                })
            },
        );
    }
    assert!(host.machine.as_ref().unwrap().gameover_view[sender]);
    let other = js.iter().find(|j| j.my_index != Some(sender)).unwrap();
    assert!(other.machine.as_ref().unwrap().gameover_view[sender]);
}

/// The host attributes every envelope to the roster index of the channel it
/// arrived on, not the claimed sender (`Routed`'s own doc comment).
#[test]
fn host_overwrites_a_forged_sender_index() {
    let (mut host, mut js) = lobby(2);
    host.start_match();
    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(&mut refs, "every joiner receives Start", |s| {
            s.iter().all(|x| x.started())
        });
    }
    let liar = js[0].my_index.unwrap();
    let victim = js[1].my_index.unwrap();

    // Hand-built envelope claiming to come from the *other* joiner.
    let forged = WireMessage::Routed(Message {
        from: victim,
        to: Destination::Broadcast,
        match_gen: js[0].match_gen,
        body: Payload::Gameover,
    });
    js[0].peers[0]
        .conn
        .outgoing
        .send((Reliability::Reliable, forged))
        .unwrap();

    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(&mut refs, "host observes the forged gameover", |s| {
            s[0].machine.as_ref().unwrap().gameover_view[liar]
        });
    }
    assert!(
        host.machine.as_ref().unwrap().gameover_view[liar],
        "attributed to the real sender"
    );
    assert!(
        !host.machine.as_ref().unwrap().gameover_view[victim],
        "the forged identity is not believed"
    );
}

/// `State` is rendering-only and must never touch the model — it populates
/// `boards`/`opponent_views` and nothing else.
#[test]
fn state_broadcast_populates_opponent_views_without_touching_the_model() {
    let (mut host, mut js) = lobby(1);
    host.start_match();
    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(&mut refs, "joiner receives Start", |s| {
            s.iter().all(|x| x.started())
        });
    }
    let joiner_index = js[0].my_index.unwrap();
    let before = format!("{:?}", host.machine.as_ref().unwrap().s6.s4.s3.s2.s1.mg);

    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(
            &mut refs,
            "host receives a State broadcast from the joiner",
            |s| s[0].boards.get(joiner_index).is_some_and(|b| b.is_some()),
        );
    }

    let views = host.opponent_views();
    assert_eq!(views.len(), 1);
    assert_eq!(views[0].player_index, joiner_index);
    assert!(
        views[0].board.is_some(),
        "the mini has a real board to draw"
    );
    assert_eq!(
        format!("{:?}", host.machine.as_ref().unwrap().s6.s4.s3.s2.s1.mg),
        before,
        "a State broadcast never touches the receiver's own model state"
    );
}

/// Hardening: `mg`'s dimensions aren't otherwise checked against this
/// instance's board size, so a malicious or buggy peer could broadcast an
/// arbitrarily large or ragged grid. Rejected outright instead of stored.
#[test]
fn state_with_wrong_grid_dimensions_is_rejected() {
    let mut host = Session::new_host("Host".into());
    host.boards = vec![None];
    let bad = Payload::State {
        p: t7::net::piece_to_code(t1::instance::Piece::T),
        py: 0,
        px: 0,
        pr: 0,
        mg: vec![vec![None]], // 1x1 — not this instance's real board shape
        gameover: false,
    };
    host.apply_local(0, bad);
    assert!(
        host.boards[0].is_none(),
        "malformed board shape must be dropped, not stored"
    );
}

/// `rem_gen_garbage` is sticky across calls, so the send path must
/// *consume* it — otherwise a later non-fixing frame would re-send the same
/// garbage (`take_rem_gen_garbage`'s own doc comment).
#[test]
fn rem_gen_garbage_is_consumed_not_merely_read() {
    let mut m =
        Machine::<Instance>::new(0, 2, make_bags_fn::<Instance>(), random_piece::<Instance>);
    m.rem_gen_garbage = 7;
    assert_eq!(take_rem_gen_garbage(&mut m), 7);
    assert_eq!(
        take_rem_gen_garbage(&mut m),
        0,
        "a second read must not re-send the same garbage"
    );
    assert_eq!(m.rem_gen_garbage, 0);
}

/// Only `Down`/`Drop` can reach a `fix_piece`, so only they oblige the
/// caller to inspect the model's outgoing state (`fire`'s own contract).
#[test]
fn only_fixing_actions_report_that_they_may_have_fixed() {
    let mut m =
        Machine::<Instance>::new(0, 2, make_bags_fn::<Instance>(), random_piece::<Instance>);
    let wm = Instance::initial_main_grid()[0].len() as i64;
    for action in [
        Action::Left,
        Action::Right,
        Action::Cw,
        Action::Ccw,
        Action::Hold,
    ] {
        assert!(
            !fire(action, &mut m, wm, |_| {}),
            "{action:?} cannot fix a piece"
        );
    }
    for action in [Action::Down, Action::Drop] {
        assert!(
            fire(action, &mut m, wm, |_| {}),
            "{action:?} may fix a piece"
        );
    }
}

/// spec: `implementation.md` §4-T7c′ — each row of one materialization
/// draws its own hole column; a single shared column would leave a clean
/// vertical shaft through the whole delivery.
#[test]
fn fresh_holes_draws_an_independent_column_per_row() {
    let wm = 10;
    let holes = fresh_holes(wm);
    let cols: Vec<i64> = (0..20).map(&holes).collect();
    for (y, &x) in cols.iter().enumerate() {
        assert!(
            (0..wm).contains(&x),
            "ValidHoles: holes({y}) = {x} out of range"
        );
    }
    assert!(
        cols.iter().any(|&x| x != cols[0]),
        "rows must not all share one hole column: {cols:?}"
    );
}

/// The same `y` asked twice inside one call must answer the same column:
/// §4-T7c may evaluate a row more than once, and `holes` is specified as a
/// *function* of `y`, not a generator.
#[test]
fn fresh_holes_is_a_function_of_its_row() {
    let holes = fresh_holes(10);
    let first: Vec<i64> = (0..20).map(&holes).collect();
    let again: Vec<i64> = (0..20).map(&holes).collect();
    assert_eq!(first, again, "holes(y) must be stable within one call site");
}

/// spec: `implementation.md` §15.1b — a message tagged with a match
/// generation this peer has already left is discarded. Built by hand rather
/// than by racing a real rematch: the point is the guard itself, and a
/// forged tag is the only way to test it deterministically.
#[test]
fn stale_generation_traffic_is_discarded() {
    let (mut host, mut js) = lobby(1);
    assert!(host.start_match());
    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(&mut refs, "joiner receives Start", |s| {
            s.iter().all(|x| x.started())
        });
    }
    let joiner_index = js[0].my_index.unwrap();
    let stale = host.match_gen - 1;

    let msg = WireMessage::Routed(Message {
        from: joiner_index,
        to: Destination::Broadcast,
        match_gen: stale,
        body: Payload::Gameover,
    });
    js[0].peers[0]
        .conn
        .outgoing
        .send((Reliability::Reliable, msg))
        .unwrap();

    // Nothing to wait *for* — so pump long enough that the message has
    // certainly arrived, then assert it changed nothing.
    let mut t = 0.0;
    for _ in 0..200 {
        host.pump(t);
        js[0].pump(t);
        t += 0.01;
        std::thread::sleep(Duration::from_millis(1));
    }
    assert!(
        !host.machine.as_ref().unwrap().gameover_view[joiner_index],
        "a message from a previous match generation must not reach the model"
    );

    // Control: the identical message, correctly tagged, does land — so the
    // assertion above is about the tag and not about delivery.
    let fresh = WireMessage::Routed(Message {
        from: joiner_index,
        to: Destination::Broadcast,
        match_gen: host.match_gen,
        body: Payload::Gameover,
    });
    js[0].peers[0]
        .conn
        .outgoing
        .send((Reliability::Reliable, fresh))
        .unwrap();
    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(&mut refs, "correctly tagged gameover lands", |s| {
            s[0].machine.as_ref().unwrap().gameover_view[joiner_index]
        });
    }
}

/// spec: `implementation.md` §15.1b — the host
/// evicts the sender's slot outright and every later slot shifts down,
/// unlike a mid-match disconnect which keeps a phantom.
#[test]
fn leave_evicts_the_sender_and_reindexes_the_rest() {
    let (mut host, mut js) = lobby(2);
    assert_eq!(host.roster_names().len(), 3);
    let leaver = js[0].my_index.unwrap_or(1);
    let stayer_before = js[1].my_index;

    js[0].leave();
    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(&mut refs, "host evicts the leaver", |s| {
            s[0].peers.len() == 1
        });
    }
    assert_eq!(
        host.roster_names().len(),
        2,
        "host plus the one remaining joiner"
    );
    assert_eq!(
        host.peers[0].index,
        Some(1),
        "the slot after an evicted one shifts down to fill the gap (was {stayer_before:?}, leaver was {leaver})"
    );
}

/// Hardening: `pump()` batches incoming events by peer id, then re-resolves
/// each to a live slot in `self.peers` right before dispatch — not by
/// snapshotting `(slot, msg)` positions up front, since `Leave`'s handler
/// removes its sender's slot and shifts every later position down, which
/// would misdirect or run past the end of `self.peers` off a stale
/// position. Both joiners leave at once, given real time to land in the
/// host's per-peer queues over the background connection threads before the
/// host's own `pump()` runs even once, forcing both `Leave`s into the same
/// dispatch batch.
#[test]
fn leaving_together_does_not_panic_on_a_stale_slot() {
    let (mut host, mut js) = lobby(2);
    js[0].leave();
    js[1].leave();
    std::thread::sleep(Duration::from_millis(200));
    host.pump(0.0); // must not panic — this is the regression itself
    assert_eq!(host.peers.len(), 0, "both leavers evicted");
    assert_eq!(host.roster_names().len(), 1, "host alone remains");
}

/// spec: `implementation.md` §15.1b — a rematch reuses the connections
/// and rebuilds the roster from the `Join`s that follow.
#[test]
fn rematch_reuses_connections_and_rebuilds_the_roster() {
    let (mut host, mut js) = lobby(1);
    assert!(host.start_match());
    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(&mut refs, "joiner receives Start", |s| {
            s.iter().all(|x| x.started())
        });
    }
    let gen_before = host.match_gen;

    host.reset_for_rematch(); // S9 → S3
    js[0].rejoin(); // S9 → S5 → S6
    assert!(
        !host.started() && !js[0].started(),
        "both peers leave the finished match"
    );
    assert_eq!(
        host.peers.len(),
        1,
        "the connection itself survives the rematch"
    );
    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(&mut refs, "the joiner re-announces itself", |s| {
            s[0].peers[0].index.is_some()
        });
    }
    assert_eq!(
        host.roster_names().len(),
        2,
        "roster rebuilt from the fresh Join"
    );

    assert!(host.start_match());
    assert!(
        host.match_gen > gen_before,
        "each Start bumps the match generation (§15.1b)"
    );
}

/// spec: `implementation.md` §15.1b — a joiner's rejoin `Join` can race the
/// host's own `reset_for_rematch`; `send_keepalive`'s periodic retry (not
/// just the one-shot `Join` in `rejoin`) is what lets the roster recover.
/// Unlike `rematch_reuses_connections_and_rebuilds_the_roster`, this drives
/// the joiner's rejoin ahead of the host's own reset to force the race.
#[test]
fn rematch_join_survives_host_pressing_rematch_late() {
    let (mut host, mut js) = lobby(1);
    assert!(host.start_match());
    {
        let mut refs: Vec<&mut Session> = std::iter::once(&mut host).chain(js.iter_mut()).collect();
        pump_until(&mut refs, "joiner receives Start", |s| {
            s.iter().all(|x| x.started())
        });
    }

    // The joiner presses Rematch immediately; the host hasn't pressed its
    // own yet, so `host.machine` is still `Some`.
    js[0].rejoin();
    assert!(!js[0].started());
    assert!(host.started(), "host hasn't reset yet");

    // Several simulated seconds with the host lingering in S9: the joiner's
    // one-shot `Join` and its periodic retries (`LOBBY_KEEPALIVE_PERIOD_SECS`)
    // all arrive while the host rejects each one (`handle`'s `Join` arm
    // bails on `self.started()`, leaving `peers[0].index` untouched).
    let mut t = 0.0f64;
    while t < 5.0 {
        host.pump(t);
        js[0].pump(t);
        t += 0.05;
        std::thread::sleep(Duration::from_millis(5));
    }
    assert!(
        host.started(),
        "still hasn't reset — every arriving Join was rejected, not queued"
    );

    // The host presses its own Rematch, clearing `peers[0].index` — without
    // a retry there would be no further `Join` in flight to set it again.
    host.reset_for_rematch();
    assert!(
        host.peers[0].index.is_none(),
        "the host's own reset is what clears it"
    );

    let deadline = t + 10.0;
    while t < deadline && host.peers[0].index.is_none() {
        host.pump(t);
        js[0].pump(t);
        t += 0.05;
        std::thread::sleep(Duration::from_millis(5));
    }
    assert!(
        host.peers[0].index.is_some(),
        "the joiner's retried Join lands once the host resets"
    );
    assert_eq!(
        host.roster_names().len(),
        2,
        "roster rebuilt despite the host resetting late"
    );
    assert!(host.start_match());
}

/// spec: `implementation.md` §15.0 — `findWinner()`: `None` while the
/// match is live, the last player standing once it is not.
#[test]
fn find_winner_resolves_only_when_one_player_is_left() {
    let mut m =
        Machine::<Instance>::new(0, 3, make_bags_fn::<Instance>(), random_piece::<Instance>);
    assert_eq!(
        find_winner(&m),
        None,
        "three live players resolve no winner"
    );
    m.receive_gameover(1);
    assert_eq!(find_winner(&m), None, "two left is still no winner");
    m.receive_disconnect(2);
    assert_eq!(find_winner(&m), Some(0), "the last player standing wins");
    assert!(
        t7::model::winner_multi(&m.gameover_view, &m.connected_view, 0),
        "and that is winner_multi(self)"
    );
}
