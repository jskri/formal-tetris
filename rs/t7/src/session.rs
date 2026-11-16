//! spec: the networked-match core (`implementation.md` §15) — lobby, host
//! relay, connection setup, and the model↔network glue around the
//! per-player `Machine<Instance>` it drives.
//!
//! spec: §0.4 — `pub` so another binary can reuse T7's lobby/relay machinery
//! (`Session`, `Peer`, `Endpoint`, the `Machine<Instance>`-facing glue)
//! without reimplementing it; `Session` never touches a macroquad API, which
//! is what lets `tests/session_integration_test.rs` drive a full host and
//! joiners over real loopback UDP with no display server.
//!
//! **Bags are per-player and purely local**: each peer's `Machine` only ever
//! holds its own `s6`, so no bag sequence crosses the wire — every peer runs
//! `make_bags_fn` against its own RNG. What crosses the wire is `T7.v`'s own
//! `Message` set, plus the rendering-only `State` broadcast (§15.3).

use crate::instance;
use crate::misc::Action;
use crate::model::{Machine, Params};
use crate::net::{
    self, Connection, ConnectionCode, Destination, Message, NetWorkerHandle, Payload, Reliability,
    WireMessage,
};
use crate::view::{OpponentBoard, OpponentView};
use std::cell::RefCell;
use std::collections::HashMap;
use std::io;
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4, ToSocketAddrs, UdpSocket};
use std::sync::mpsc;
use std::time::Duration;
use t1::misc::random_piece;
use t1::model::Params as T1Params;

pub type Instance = instance::Tetris;
pub type Piece = <Instance as T1Params>::Piece;
pub type Cell = Option<t1::model::PieceOrExtra<Instance>>;

/// spec: §15.2 step 1 — the public STUN server the one Binding Request
/// goes to. Resolved by name at startup (`ToSocketAddrs`); a failure to
/// reach it is not fatal, see `Endpoint::discover`.
const STUN_SERVER: &str = "stun.l.google.com:19302";

/// spec: §15.2 step 1 — how often a joiner's not-yet-connected socket sends
/// a fresh Binding Request while its code is being exchanged out of band
/// (`Endpoint::send_mapping_keepalive`). Well under the shortest UDP NAT
/// mapping timeouts seen in practice (around 30s), so the mapping the code
/// advertises is still the one in place when the joiner finally connects.
pub const MAPPING_REFRESH_SECS: f64 = 15.0;

/// spec: §15.4 — how long a peer's channel may go silent before the host
/// declares it disconnected (and, symmetrically, before a joiner decides its
/// own link to the host is down). Comfortably more than `STATE_PERIOD_SECS`
/// so ordinary jitter never trips it.
const DISCONNECT_TIMEOUT_SECS: f64 = 10.0;

/// Before `Start`, `State` isn't flowing yet, so nothing follows the
/// one-shot handshake — without a keepalive a host that simply takes its
/// time would trip `DISCONNECT_TIMEOUT_SECS` for no reason. `Ping` (net.rs)
/// fills that gap, well under the timeout.
const LOBBY_KEEPALIVE_PERIOD_SECS: f64 = 2.0;

/// spec: §15.2 step 5 — the periodic `State` broadcast doubles as the NAT
/// keepalive (needs ≥3 Hz); 10 Hz also keeps the opponent minis visibly live
/// rather than steppy.
const STATE_PERIOD_SECS: f64 = 0.1;

/// Largest roster a match accepts, host included. Bounds every allocation
/// sized by a peer-supplied player count (`Start`) or roster (`Players`),
/// and is what the host's lobby enforces on `Join`.
pub const MAX_PLAYERS: usize = 16;

/// req-preview-init's "fair" randomization source. Bound at
/// `t1::model::Params` rather than `t7::model::Params` — the minimum this
/// actually reads (`piece_all()`) — so the single-player engine's own
/// instance, which doesn't implement `t7::model::Params`, can use it too.
pub fn shuffle_bag<P: T1Params>() -> Vec<P::Piece> {
    let mut a: Vec<P::Piece> = P::piece_all().to_vec();
    for i in (1..a.len()).rev() {
        let j = macroquad::rand::gen_range(0usize, i + 1);
        a.swap(i, j);
    }
    a
}

/// Same minimum-bound reasoning as `shuffle_bag` above.
pub fn make_bags_fn<P: T1Params>() -> impl FnMut(u64) -> Vec<P::Piece> {
    let mut bags: Vec<Vec<P::Piece>> = Vec::new();
    move |i: u64| {
        let i = i as usize;
        while bags.len() <= i {
            bags.push(shuffle_bag::<P>());
        }
        bags[i].clone()
    }
}

/// spec: §4-T7c′/§15.7 — a fresh RNG per call site, never persisted on
/// `Machine`; draws an independent, row-memoized hole column rather than one
/// shared column per delivery, so an I-piece can't clear a whole delivery
/// through an aligned vertical shaft.
pub fn fresh_holes(wm: i64) -> impl Fn(i64) -> i64 {
    let memo: RefCell<HashMap<i64, i64>> = RefCell::new(HashMap::new());
    move |y| {
        *memo
            .borrow_mut()
            .entry(y)
            .or_insert_with(|| macroquad::rand::gen_range(0i64, wm))
    }
}

pub fn rotate<P: Params>(machine: &mut Machine<P>, cw: bool) -> bool {
    machine.rotate_piece(cw) || machine.rotate_kick_piece(cw)
}

/// Returns whether this action *could* have fixed a piece — i.e. whether
/// the caller must now inspect `rem_gen_garbage`/`gameover_view[my_index]`
/// and send whatever they call for (`implementation.md` §4-T7d/§15.5).
/// Only `Down`/`Drop` reach a `fix_piece` at all. `on_result` is invoked
/// with each underlying model call's own real return value, for a caller
/// that wants to react to what actually happened (e.g. play a sound only
/// when a move/rotate/hold genuinely took effect) without reimplementing
/// this dispatch itself.
pub fn fire<P: Params>(
    action: Action,
    machine: &mut Machine<P>,
    wm: i64,
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
            on_result(rotate(machine, true));
            false
        }
        Action::Ccw => {
            on_result(rotate(machine, false));
            false
        }
        Action::Hold => {
            on_result(machine.hold_piece(&shuffle_bag::<P>()));
            false
        }
        Action::Down => {
            on_result(machine.fall_step(&shuffle_bag::<P>(), fresh_holes(wm)));
            true
        }
        Action::Drop => {
            on_result(machine.drop_piece(&shuffle_bag::<P>(), fresh_holes(wm)));
            true
        }
    }
}

/// Reads `rem_gen_garbage` **and clears it** (`implementation.md` §4-T7d:
/// "state the caller reads post-call rather than a return value"). The
/// clear is what makes the read a one-shot *consumption* rather than a
/// level-triggered one: the field is sticky across calls — it keeps its
/// last value until the next `fix_piece` overwrites it — so a caller that
/// merely re-read it after some later, non-fixing call would send the same
/// garbage twice. `fix_piece` overwrites it unconditionally on its own next
/// run, so clearing it here can never lose a value that was still owed.
pub fn take_rem_gen_garbage<P: Params>(machine: &mut Machine<P>) -> i64 {
    std::mem::replace(&mut machine.rem_gen_garbage, 0)
}

// ── Endpoint: one socket + its discovered addresses (§15.1, §15.2) ──────

/// One prospective connection's own socket, together with the two addresses
/// its connection code advertises. spec: §15.1a′ — one `Endpoint` per
/// joiner, since a NAT mapping belongs to a specific socket and a code
/// minted from it is only reachable on that same socket.
pub struct Endpoint {
    pub socket: UdpSocket,
    pub public: SocketAddrV4,
    pub local: SocketAddrV4,
    pub nonce: u64,
    /// The STUN server `public` was discovered through; `None` when
    /// discovery failed (there is then no mapping to keep alive).
    pub stun_server: Option<SocketAddr>,
    /// Transaction id of the last keepalive Binding Request whose response
    /// has not been read yet (`poll_mapping`).
    pending_txid: Option<[u8; 12]>,
}

impl Endpoint {
    /// Binds a fresh ephemeral socket and discovers its public mapping via
    /// STUN. A STUN failure is not fatal: the code then advertises the LAN
    /// address as both `public` and `local`, which is all that's honestly
    /// knowable and enough for same-LAN play; `stun_ok` lets the lobby
    /// screen flag that cross-NAT play won't work, rather than failing later
    /// with a mystery timeout.
    pub fn discover() -> io::Result<(Endpoint, bool)> {
        let socket = UdpSocket::bind("0.0.0.0:0")?;
        let port = match socket.local_addr()? {
            SocketAddr::V4(a) => a.port(),
            SocketAddr::V6(a) => a.port(),
        };
        let local = SocketAddrV4::new(local_ipv4().unwrap_or(Ipv4Addr::LOCALHOST), port);

        let stun_server = STUN_SERVER
            .to_socket_addrs()
            .ok()
            .and_then(|mut it| it.find(|a| a.is_ipv4()));
        let stun_result = stun_server
            .and_then(|server| net::stun::query(&socket, server, Duration::from_secs(2), 3).ok());

        // The read timeout STUN set is a query-time concern only; the
        // socket is switched to non-blocking when the connection thread
        // takes it over (`NetWorkerHandle::register`).
        socket.set_read_timeout(None)?;

        let (public, stun_ok) = match stun_result {
            Some(SocketAddr::V4(a)) => (a, true),
            _ => (local, false),
        };
        Ok((
            Endpoint {
                socket,
                public,
                local,
                nonce: fresh_nonce(),
                stun_server: stun_server.filter(|_| stun_ok),
                pending_txid: None,
            },
            stun_ok,
        ))
    }

    /// spec: §15.2 step 1 — keeps this socket's NAT mapping open while its
    /// code is exchanged out of band. Nothing else is sent on the socket
    /// until it connects, and a NAT drops an idle mapping after a while; a
    /// mapping recreated later may get a different public port, which the
    /// peer (accepting packets only from the advertised addresses) would
    /// then ignore. Sends one Binding Request and returns at once; the
    /// response is read by `poll_mapping`. A no-op without a STUN server.
    pub fn send_mapping_keepalive(&mut self) {
        let Some(server) = self.stun_server else {
            return;
        };
        let txid = net::stun::fresh_txid();
        if self
            .socket
            .send_to(&net::stun::build_binding_request(txid), server)
            .is_ok()
        {
            self.pending_txid = Some(txid);
        }
    }

    /// Non-blocking: reads whatever has arrived on the socket since the last
    /// call and, if a response to the pending keepalive reports a different
    /// public mapping, adopts it. Returns `true` exactly when `public` (and
    /// so `code()`) changed, so the caller can tell the player to share the
    /// new code. Anything else that arrives before the socket connects (an
    /// early `Hello` from the peer) is dropped; the reliable channel
    /// retransmits it.
    pub fn poll_mapping(&mut self) -> bool {
        let Some(server) = self.stun_server else {
            return false;
        };
        if self.socket.set_nonblocking(true).is_err() {
            return false;
        }
        let mut changed = false;
        let mut buf = [0u8; 1500];
        while let Ok((n, from)) = self.socket.recv_from(&mut buf) {
            let Some(txid) = self.pending_txid else {
                continue;
            };
            if from != server {
                continue;
            }
            let parsed = net::stun::parse_binding_response(&buf[..n], &txid);
            if let Some(SocketAddr::V4(mapped)) = parsed {
                self.pending_txid = None;
                if mapped != self.public {
                    self.public = mapped;
                    changed = true;
                }
            }
        }
        let _ = self.socket.set_nonblocking(false);
        changed
    }

    pub fn code(&self) -> ConnectionCode {
        ConnectionCode {
            public: self.public,
            local: self.local,
            nonce: self.nonce,
        }
    }
}

/// This host's own LAN address. A wildcard-bound socket reports `0.0.0.0`
/// as its local IP, useless in a connection code — so this asks the routing
/// table instead via the standard "connect a UDP socket off-link and read
/// back the local address the kernel chose" trick. `UdpSocket::connect` on a
/// datagram socket sends nothing and pins only the default destination, so
/// the address named here need not be reachable at all.
pub fn local_ipv4() -> Option<Ipv4Addr> {
    let probe = UdpSocket::bind("0.0.0.0:0").ok()?;
    probe.connect("8.8.8.8:80").ok()?;
    match probe.local_addr().ok()? {
        SocketAddr::V4(a) => Some(*a.ip()),
        SocketAddr::V6(_) => None,
    }
}

/// The nonce a connection code carries — the one secret that proves a
/// `Hello`'s sender is the peer the code was exchanged with (`net.rs`'s
/// `PeerPath`), so it must be unpredictable: drawn from OS entropy, all 64
/// bits. Only if the OS source fails does it fall back to macroquad's
/// (seeded, but not cryptographic) RNG. Never 0.
pub fn fresh_nonce() -> u64 {
    let n = getrandom::u64().unwrap_or_else(|_| {
        (u64::from(macroquad::rand::rand()) << 32) | u64::from(macroquad::rand::rand())
    });
    n.max(1)
}

// ── Session: one networked match (never touches macroquad) ─────────────

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Role {
    Host,
    Joiner,
}

/// One connected peer. On the host, one per joiner; on a joiner, exactly
/// one (the host, whose roster index is `0` by §15.1's own convention).
pub struct Peer {
    pub conn: Connection,
    /// Stable identity, independent of this peer's position in
    /// `Session::peers` — spec: §15.1a′ — a `Leave` can splice an earlier
    /// slot out and shift later ones down while a batch (`Session::pump`)
    /// still holds events for one; `id` lets it re-resolve the live slot.
    pub id: u64,
    /// Roster index. Host side: `None` until this peer's `Join` arrives and
    /// an index is assigned. Joiner side: always `Some(0)`, the host.
    pub index: Option<usize>,
    pub name: String,
    pub connected: bool,
}

/// An opponent's last-known board, from its `State` broadcasts — rendering
/// only, never model state (`implementation.md` §14.3).
pub struct RemoteBoard {
    pub mg: Vec<Vec<Cell>>,
    pub p: Piece,
    pub py: i64,
    pub px: i64,
    pub pr: u8,
    pub gameover: bool,
}

/// The whole networked match: this peer's own `Machine`, its connections,
/// and the lobby/relay state machine over them.
pub struct Session {
    pub role: Role,
    pub peers: Vec<Peer>,
    pub my_name: String,
    pub my_index: Option<usize>,
    pub player_count: Option<usize>,
    pub roster: Vec<String>,
    pub machine: Option<Machine<Instance>>,
    pub boards: Vec<Option<RemoteBoard>>,
    pub last_state_broadcast: f64,
    pub last_keepalive: f64,
    pub noticed_disconnect: bool,
    /// spec: §15.1b — match-generation counter, incremented once per
    /// `Start` (rematches included) and tagged on every application
    /// message; a receiver discards anything tagged with a generation it
    /// has left.
    pub match_gen: u64,
    /// Monotonic, never-reused source for `Peer::id` (see `Peer::id`).
    pub next_peer_id: u64,
    /// This session's one round-robin network thread — every `Peer::conn`
    /// in `peers` is registered against it. Kept alongside `peers` rather
    /// than inside `net.rs` so a connection can be registered before its
    /// `Peer` exists (`new_joiner`'s caller registers the first connection
    /// before `Session::new_joiner` is called).
    pub net: NetWorkerHandle,
}

impl Session {
    pub fn new_host(my_name: String) -> Session {
        Session {
            role: Role::Host,
            peers: Vec::new(),
            my_name,
            my_index: Some(0), // spec: §15.1 — Host is always roster index 0
            player_count: None,
            roster: Vec::new(),
            machine: None,
            boards: Vec::new(),
            last_state_broadcast: 0.0,
            last_keepalive: 0.0,
            noticed_disconnect: false,
            match_gen: 0,
            next_peer_id: 1, // 0 is used below for new_joiner's own initial host peer
            net: NetWorkerHandle::spawn(),
        }
    }

    pub fn new_joiner(net: NetWorkerHandle, conn: Connection, my_name: String) -> Session {
        Session {
            role: Role::Joiner,
            peers: vec![Peer {
                conn,
                id: 0,
                index: Some(0),
                name: "Host".into(),
                connected: true,
            }],
            my_name,
            my_index: None, // assigned by the host's own Start (§15.1)
            player_count: None,
            roster: Vec::new(),
            machine: None,
            boards: Vec::new(),
            last_state_broadcast: 0.0,
            last_keepalive: 0.0,
            noticed_disconnect: false,
            match_gen: 0,
            next_peer_id: 1,
            net,
        }
    }

    /// Allocates a fresh, never-reused `Peer::id` (`Session::pump`'s own
    /// slot-stability note).
    pub fn alloc_peer_id(&mut self) -> u64 {
        let id = self.next_peer_id;
        self.next_peer_id += 1;
        id
    }

    /// Returns the `Peer::id` allocated for `conn` — hold onto this instead
    /// of the peer's `Vec` position, which a later `Leave` can shift.
    pub fn add_peer(&mut self, conn: Connection) -> u64 {
        let id = self.alloc_peer_id();
        self.peers.push(Peer {
            conn,
            id,
            index: None,
            name: String::new(),
            connected: true,
        });
        id
    }

    /// Host lobby (§15.1a′): drops a pairing that never completed — the peer
    /// with stable id `id`, if it is still present and has not joined. A
    /// peer that already holds a roster index is left alone (it is a real
    /// player now, and only `Leave` or a timeout removes those).
    pub fn remove_unjoined_peer(&mut self, id: u64) {
        if let Some(slot) = self
            .peers
            .iter()
            .position(|p| p.id == id && p.index.is_none())
        {
            self.peers.remove(slot);
        }
    }

    pub fn started(&self) -> bool {
        self.machine.is_some()
    }

    /// spec: §15.1b — after a slot is spliced out, every later slot's roster
    /// index shifts down by one; unassigned slots (mid-handshake) stay
    /// `None`.
    pub fn reindex_peers(&mut self) {
        let mut assigned: Vec<usize> = (0..self.peers.len())
            .filter(|&i| self.peers[i].index.is_some())
            .collect();
        assigned.sort_by_key(|&i| self.peers[i].index.unwrap());
        for (next, i) in assigned.into_iter().enumerate() {
            self.peers[i].index = Some(next + 1);
        }
    }

    /// spec: §15.1b — drops the finished match's `Machine`/roster/boards
    /// while keeping every live peer connection; the host also clears peer
    /// indices so the fresh roster rebuilds from the `Join`s that follow.
    /// A peer the host declared disconnected during the match
    /// (`declare_disconnected`) is dropped here rather than kept: it is never
    /// serviced again (`handle`), so keeping it would only let it linger as
    /// a slot no timeout ever reaps.
    pub fn reset_for_rematch(&mut self) {
        self.machine = None;
        self.player_count = None;
        self.boards.clear();
        self.roster.clear();
        self.noticed_disconnect = false;
        if self.role == Role::Host {
            self.peers.retain(|p| p.connected);
            for p in self.peers.iter_mut() {
                p.index = None;
            }
        }
    }

    /// spec: `implementation.md` §15.0 (`S5`) — a joiner's rematch:
    /// re-announce over the existing channel, no code exchange at all.
    pub fn rejoin(&mut self) {
        self.reset_for_rematch();
        let name = self.my_name.clone();
        if let Some(host) = self.peers.first() {
            let _ = host.conn.outgoing.send((
                Reliability::Reliable,
                WireMessage::Untagged(Payload::Join { name }),
            ));
        }
    }

    /// spec: §15.0 (`S9`)/§15.1b — a joiner tells the host to drop its slot;
    /// a leaving host instead sends nothing, its departure already covered
    /// by every client's `DisconnectPlayer pl = Host` case.
    pub fn leave(&mut self) {
        if self.role == Role::Joiner {
            if let Some(host) = self.peers.first() {
                let _ = host
                    .conn
                    .outgoing
                    .send((Reliability::Reliable, WireMessage::Untagged(Payload::Leave)));
            }
        }
    }

    /// Host's own view of the roster: index 0 is the host, then each joiner
    /// at the index it was assigned on `Join`.
    pub fn roster_names(&self) -> Vec<String> {
        let mut assigned: Vec<(usize, String)> = self
            .peers
            .iter()
            .filter_map(|p| p.index.map(|i| (i, p.name.clone())))
            .collect();
        assigned.sort_by_key(|(i, _)| *i);
        let mut names = vec![self.my_name.clone()];
        names.extend(assigned.into_iter().map(|(_, n)| n));
        names
    }

    /// `State` is the one best-effort message (§15.2's own split); every
    /// other application message carries a `T7.v` `Message` and must not be
    /// lost.
    pub fn reliability_of(body: &Payload) -> Reliability {
        match body {
            Payload::State { .. } => Reliability::BestEffort,
            _ => Reliability::Reliable,
        }
    }

    /// Sends one application message wrapped in `Routed`, from this peer.
    /// A joiner has exactly one channel (to the host, who relays); the host
    /// sends straight down the addressed joiner's own channel, or all of
    /// them for a broadcast (§15.4).
    pub fn send_routed(&self, to: Destination, body: Payload) {
        let Some(from) = self.my_index else { return };
        self.send_routed_from(from, to, body);
    }

    /// `from` explicit: the host originates `Disconnect` on behalf of the
    /// peer that dropped — `T7.v`'s `DisconnectMessage`s come from the
    /// disconnected player, not the host (§4-T7f/§15.4).
    pub fn send_routed_from(&self, from: usize, to: Destination, body: Payload) {
        let rel = Self::reliability_of(&body);
        let env = WireMessage::Routed(Message {
            from,
            to,
            match_gen: self.match_gen,
            body,
        });
        match self.role {
            Role::Joiner => {
                if let Some(host) = self.peers.first() {
                    let _ = host.conn.outgoing.send((rel, env));
                }
            }
            Role::Host => {
                for p in &self.peers {
                    let Some(idx) = p.index else { continue };
                    if p.connected && to.reaches(idx) {
                        let _ = p.conn.outgoing.send((rel, env.clone()));
                    }
                }
            }
        }
    }

    /// Host relay (§15.4): pass an envelope on to whoever it was addressed
    /// to, never back to the channel it arrived on.
    pub fn forward(
        &self,
        except_slot: usize,
        to: Destination,
        env: &WireMessage,
        rel: Reliability,
    ) {
        for (i, p) in self.peers.iter().enumerate() {
            let Some(idx) = p.index else { continue };
            if i != except_slot && p.connected && to.reaches(idx) {
                let _ = p.conn.outgoing.send((rel, env.clone()));
            }
        }
    }

    pub fn broadcast_roster(&self) {
        let roster = self.roster_names();
        for p in &self.peers {
            if p.index.is_some() && p.connected {
                let _ = p.conn.outgoing.send((
                    Reliability::Reliable,
                    WireMessage::Untagged(Payload::Players {
                        roster: roster.clone(),
                    }),
                ));
            }
        }
    }

    /// spec: §15.1 — freezes `player_count`, sends `Start` to each joiner
    /// with its assigned `my_index`; every peer, host included, constructs
    /// its own `Machine` only at this point.
    pub fn start_match(&mut self) -> bool {
        if self.role != Role::Host || self.started() {
            return false;
        }
        let roster = self.roster_names();
        if roster.len() < 2 {
            return false; // t7::model::Machine::new asserts player_count > 1 (implementation.md §0.2)
        }
        let player_count = roster.len();
        self.match_gen += 1; // spec: §15.1b — incremented once per Start, rematch included
        for p in &self.peers {
            if let Some(idx) = p.index {
                let msg = WireMessage::Untagged(Payload::Start {
                    player_count,
                    my_index: idx,
                    match_gen: self.match_gen,
                });
                let _ = p.conn.outgoing.send((Reliability::Reliable, msg));
            }
        }
        self.roster = roster;
        self.init_machine(0, player_count);
        true
    }

    pub fn init_machine(&mut self, my_index: usize, player_count: usize) {
        self.my_index = Some(my_index);
        self.player_count = Some(player_count);
        self.machine = Some(Machine::<Instance>::new(
            my_index,
            player_count,
            make_bags_fn::<Instance>(),
            random_piece::<Instance>,
        ));
        self.boards = (0..player_count).map(|_| None).collect();
        if self.roster.len() != player_count {
            self.roster = (0..player_count).map(|i| format!("P{}", i + 1)).collect();
        }
    }

    /// Drains every connection's incoming events, dispatches them, then runs
    /// the periodic duties (keepalive `State` broadcast, disconnect
    /// timeouts). Called once per frame by the game loop, and directly by
    /// this crate's tests — hence taking `now` rather than calling
    /// `get_time()` itself.
    ///
    /// Events are collected by each peer's stable `id`, not its `peers`
    /// vector position: `handle`'s `Leave` arm can remove a slot mid-batch,
    /// shifting later positions down, so each event re-resolves its live
    /// slot from `id` immediately before dispatch rather than trusting a
    /// position that may already be stale.
    pub fn pump(&mut self, now: f64) {
        let mut events: Vec<(u64, WireMessage)> = Vec::new();
        for peer in self.peers.iter() {
            while let Ok(msg) = peer.conn.incoming.try_recv() {
                events.push((peer.id, msg));
            }
        }
        for (id, msg) in events {
            if let Some(slot) = self.peers.iter().position(|p| p.id == id) {
                self.handle(slot, msg);
            } // else: this peer was already removed earlier in this same batch (a Leave)
        }
        self.broadcast_state(now);
        self.send_keepalive(now);
        self.check_timeouts();
    }

    pub fn handle(&mut self, slot: usize, msg: WireMessage) {
        // spec: §15.4 — once the host has declared a peer disconnected
        // (`DisconnectPlayer`, `declare_disconnected`), nothing more from it
        // is applied or relayed, even if its link comes back: its
        // `Disconnect` has already been broadcast and must stay the last
        // message anyone receives from it (`LastMessagesGameoverDisconnect`),
        // and `connected` never flips back (`DisconnectedMonotone`).
        if self.role == Role::Host && !self.peers[slot].connected {
            return;
        }
        match msg {
            WireMessage::Untagged(payload) => self.handle_untagged(slot, payload),
            WireMessage::Routed(msg) => {
                // spec: §15.1b — discard anything not from the match this
                // peer believes it is in.
                if msg.match_gen == self.match_gen {
                    self.handle_routed(slot, msg);
                }
            }
        }
    }

    pub fn handle_untagged(&mut self, slot: usize, payload: Payload) {
        match payload {
            // spec: §15.2 step 4 — the Hello/HelloAck pair confirming
            // two-way delivery. net.rs sends our own Hello automatically on
            // spawn; replying to theirs is this layer's half.
            Payload::Hello { nonce } => {
                let _ = self.peers[slot].conn.outgoing.send((
                    Reliability::Reliable,
                    WireMessage::Untagged(Payload::HelloAck { nonce }),
                ));
            }
            // Our own Hello came back acked: the channel is confirmed
            // two-way, so a joiner may now announce itself (§15.2 step 4's
            // "before Join is ever sent").
            Payload::HelloAck { .. } => {
                if self.role == Role::Joiner && !self.started() {
                    let name = self.my_name.clone();
                    let _ = self.peers[slot].conn.outgoing.send((
                        Reliability::Reliable,
                        WireMessage::Untagged(Payload::Join { name }),
                    ));
                }
            }
            // spec: §15.1 — the host assigns the next free roster index and
            // rebroadcasts the roster to everyone connected so far.
            Payload::Join { name } => {
                if self.role != Role::Host || self.started() {
                    return;
                }
                if self.peers[slot].index.is_none() {
                    let next = 1 + self.peers.iter().filter(|p| p.index.is_some()).count();
                    if next >= MAX_PLAYERS {
                        return; // roster full: this peer stays unjoined
                    }
                    self.peers[slot].index = Some(next);
                    let trimmed = name.trim();
                    // Hardening: `name` is peer-supplied and otherwise unbounded (up to the
                    // decode-size cap) — clamp it to the same length local typing enforces
                    // (`text::TextInput::apply`'s `NAME_FIELD_MAX_LEN`).
                    self.peers[slot].name = if trimmed.is_empty() {
                        format!("P{}", next + 1)
                    } else {
                        trimmed
                            .chars()
                            .take(crate::text::NAME_FIELD_MAX_LEN)
                            .collect()
                    };
                }
                self.broadcast_roster();
            }
            // The roster is frozen at `Start`: a later `Players` (the host
            // renumbering after another peer's post-match `Leave`) describes
            // the next lobby, not this match's indices, which the winner
            // screen and the opponent strip still read.
            Payload::Players { roster } => {
                if self.role == Role::Joiner && !self.started() {
                    // Hardening: peer-supplied — bounded like the host's own
                    // `Join` handling bounds what it accepts.
                    self.roster = roster
                        .into_iter()
                        .take(MAX_PLAYERS)
                        .map(|n| n.chars().take(crate::text::NAME_FIELD_MAX_LEN).collect())
                        .collect();
                }
            }
            Payload::Start {
                player_count,
                my_index,
                match_gen,
            } => {
                if self.role == Role::Joiner
                    && !self.started()
                    && player_count > 1
                    && player_count <= MAX_PLAYERS // hardening: sizes allocations below
                    && my_index < player_count
                {
                    self.match_gen = match_gen; // spec: §15.1b — the host's counter is authoritative
                    self.init_machine(my_index, player_count);
                }
            }
            // spec: §15.1b — host-only. Before a match starts, or once one
            // has resolved a winner (`find_winner`), the slot is evicted
            // outright (no phantom slot). Mid-match, renumbering the frozen
            // roster would misalign indices already in flight, so the slot is
            // kept and the departure is realized as `DisconnectPlayer` for
            // that player instead (`declare_disconnected`) — the same effect
            // a timeout would have, without waiting for it.
            Payload::Leave => {
                if self.role != Role::Host {
                    return;
                }
                let match_over = self
                    .machine
                    .as_ref()
                    .is_some_and(|m| find_winner(m).is_some());
                if !self.started() || match_over {
                    self.peers.remove(slot);
                    self.reindex_peers();
                    self.broadcast_roster();
                } else {
                    self.declare_disconnected(slot);
                }
            }
            // Garbage/Gameover/Disconnect/State never legitimately arrive
            // untagged — always inside a Routed(Message) envelope
            // (net.rs's own WireMessage doc comment). Nothing at the type
            // level forbids constructing one this way; this arm is the
            // guard against it actually mattering if it ever happens.
            Payload::Ping
            | Payload::Garbage { .. }
            | Payload::Gameover
            | Payload::Disconnect
            | Payload::State { .. } => {}
        }
    }

    pub fn handle_routed(&mut self, slot: usize, msg: Message) {
        // The host overwrites `from` with the index it assigned to the
        // channel this actually arrived on, so one joiner cannot pass
        // traffic off as another's (net.rs's own `Message` doc comment).
        let from = match self.role {
            Role::Host => match self.peers[slot].index {
                Some(idx) => idx,
                None => return, // not yet through Join — nothing to attribute this to
            },
            Role::Joiner => msg.from,
        };
        // spec: §4-T7f — `DisconnectMessage` is only ever originated by the
        // host (`declare_disconnected`), on behalf of the player that
        // dropped. One arriving from a joiner states nothing the host has
        // established, so it is neither applied nor relayed.
        if self.role == Role::Host && matches!(msg.body, Payload::Disconnect) {
            return;
        }
        // Hardening: `T7.v`'s `SendMessages` only ever emits one
        // `GarbageMessage` per fix, to the sender's single target, carrying
        // `RemGenGarbage` — at most what one lock can generate. Anything else
        // claiming to be garbage (a broadcast, or an impossible amount) is a
        // misbehaving peer, so the host neither applies nor relays it.
        if self.role == Role::Host {
            if let Payload::Garbage { amount } = msg.body {
                let max = crate::model::generated_garbage(Instance::PW, true);
                if !matches!(msg.to, Destination::Single(_)) || !(1..=max).contains(&amount) {
                    return;
                }
            }
        }
        // Hardening: a `State` that would not decode into a renderable board
        // is dropped here, before the host relays it — otherwise one peer's
        // malformed board would reach every other peer's renderer too.
        if matches!(msg.body, Payload::State { .. }) && remote_board_from(&msg.body).is_none() {
            return;
        }

        let for_me = match msg.to {
            Destination::Broadcast => true,
            Destination::Single(idx) => self.my_index == Some(idx),
        };
        if self.role == Role::Host {
            let rel = Self::reliability_of(&msg.body);
            let env = WireMessage::Routed(Message {
                from,
                to: msg.to,
                match_gen: self.match_gen,
                body: msg.body.clone(),
            });
            self.forward(slot, msg.to, &env, rel);
        }
        if for_me && Some(from) != self.my_index {
            self.apply_local(from, msg.body);
        }
    }

    /// The one place a received application payload (§4-T7e's `T7.v`
    /// `Message`) reaches the model.
    pub fn apply_local(&mut self, from: usize, body: Payload) {
        match body {
            Payload::Garbage { amount } => {
                if let Some(m) = &mut self.machine {
                    // Hardening: `amount` is peer-supplied and unvalidated —
                    // negative would violate the `garbage >= 0` invariant
                    // (unchecked at runtime), huge or repeated risks
                    // overflowing `receive_garbage`'s `+=`. `hm` is already
                    // the natural ceiling since materialization clamps to it
                    // regardless, so nothing above it has any effect anyway.
                    let hm = m.s6.s4.s3.s2.s1.mg.len() as i64;
                    m.receive_garbage(amount.clamp(0, hm)); // spec: ReceiveMessage — GarbageMessage
                }
            }
            Payload::Gameover => {
                if let Some(m) = &mut self.machine {
                    if from < m.gameover_view.len() {
                        m.receive_gameover(from); // spec: ReceiveMessage — GameoverMessage
                    }
                }
            }
            Payload::Disconnect => {
                if let Some(m) = &mut self.machine {
                    if from < m.connected_view.len() {
                        m.receive_disconnect(from); // spec: ReceiveMessage — DisconnectMessage
                    }
                }
            }
            // Rendering only — never model state (implementation.md §14.3).
            body @ Payload::State { .. } => {
                let Some(board) = remote_board_from(&body) else {
                    return;
                };
                if from < self.boards.len() {
                    self.boards[from] = Some(board);
                }
            }
            _ => {}
        }
    }

    /// spec: §15.5 — after a call that may have fixed, reads
    /// `rem_gen_garbage`/`gameover_view[my_index]` and sends what they call
    /// for. `was_gameover` is sampled before the call so `Gameover` goes out
    /// exactly once, on the transition; `pre_target` is `machine.target` as
    /// it stood before the call, since `fix_piece` advances `target` to the
    /// next candidate in the same call that produces this garbage.
    pub fn broadcast_after_fix(&mut self, was_gameover: bool, pre_target: usize) {
        let Some(m) = &mut self.machine else { return };
        let me = m.my_index;
        let now_gameover = m.gameover_view[me];
        let rem_gen_garbage = take_rem_gen_garbage(m);

        // req-multi-garbage-send: to the sender's own target, one recipient.
        if rem_gen_garbage > 0 && pre_target != me {
            self.send_routed(
                Destination::Single(pre_target),
                Payload::Garbage {
                    amount: rem_gen_garbage,
                },
            );
        }
        // spec: SendMessages — "at most one GameoverMessage, to everyone else".
        if now_gameover && !was_gameover {
            self.send_routed(Destination::Broadcast, Payload::Gameover);
        }
    }

    /// spec: §15.5 — fires one action and immediately broadcasts whatever it
    /// produced, rather than aggregating across a frame: a single frame can
    /// dispatch more than one fixing call (e.g. an ARR repeat plus a fresh
    /// `Drop`, or a further gravity `fall_step`), and `fix_piece` overwrites
    /// `rem_gen_garbage`/`target` on every call — so `was_gameover`/
    /// `pre_target` must be sampled fresh per fixing call, not once per
    /// frame, or an earlier fix's garbage gets clobbered before it's read.
    pub fn fire_and_broadcast(
        &mut self,
        fire: impl FnOnce(&mut Machine<Instance>) -> bool,
    ) -> bool {
        let Some(machine) = self.machine.as_mut() else {
            return false;
        };
        let was_gameover = machine.gameover_view[machine.my_index];
        let pre_target = machine.target;
        let may_have_fixed = fire(machine);
        if may_have_fixed {
            self.broadcast_after_fix(was_gameover, pre_target);
        }
        may_have_fixed
    }

    /// spec: §15.2 step 5 / §15.3 — the periodic best-effort `State`
    /// broadcast: opponent-mini rendering (§14.3) and NAT keepalive in one.
    pub fn broadcast_state(&mut self, now: f64) {
        if now - self.last_state_broadcast < STATE_PERIOD_SECS {
            return;
        }
        self.last_state_broadcast = now;
        let Some(m) = &self.machine else { return };
        let s1 = &m.s6.s4.s3.s2.s1;
        let mg = s1
            .mg
            .iter()
            .map(|row| row.iter().map(|c| c.map(net::GridCell::from)).collect())
            .collect();
        let msg = Payload::State {
            p: net::piece_to_code(s1.p),
            py: s1.py,
            px: s1.px,
            pr: s1.pr,
            mg,
            gameover: s1.gameover,
        };
        self.send_routed(Destination::Broadcast, msg);
    }

    /// The lobby/waiting-room counterpart to `broadcast_state`'s keepalive
    /// role (`LOBBY_KEEPALIVE_PERIOD_SECS`).
    ///
    /// spec: §15.1b — for a joiner this also doubles as the rejoin retry: a
    /// rematch's one-shot `Join` (`rejoin`) may arrive before the host has
    /// pressed its own Rematch and gets silently dropped, so resending here
    /// on the same period is a harmless no-op once assigned an index, and
    /// otherwise the retry that survives the ordering race.
    pub fn send_keepalive(&mut self, now: f64) {
        if self.machine.is_some() || now - self.last_keepalive < LOBBY_KEEPALIVE_PERIOD_SECS {
            return;
        }
        self.last_keepalive = now;
        match self.role {
            Role::Host => {
                for p in &self.peers {
                    let _ = p.conn.outgoing.send((
                        Reliability::BestEffort,
                        WireMessage::Untagged(Payload::Ping),
                    ));
                }
            }
            Role::Joiner => {
                if let Some(host) = self.peers.first() {
                    let name = self.my_name.clone();
                    let _ = host.conn.outgoing.send((
                        Reliability::Reliable,
                        WireMessage::Untagged(Payload::Join { name }),
                    ));
                }
            }
        }
    }

    /// spec: §15.4 (host)/§4-T7g (joiner). The host realizes
    /// `DisconnectPlayer pl≠Host`: mark locally and relay a
    /// `DisconnectMessage` from that player to every other connected peer.
    /// A joiner instead realizes `NoticeDisconnection` when its own link to
    /// the host goes quiet.
    pub fn check_timeouts(&mut self) {
        match self.role {
            Role::Host => {
                let mut slot = 0;
                while slot < self.peers.len() {
                    // `None` (no packet ever) is not a timeout — see
                    // `seconds_since_last_activity`.
                    let Some(elapsed) = self.peers[slot].conn.seconds_since_last_activity() else {
                        slot += 1;
                        continue;
                    };
                    if !self.peers[slot].connected || elapsed <= DISCONNECT_TIMEOUT_SECS {
                        slot += 1;
                        continue;
                    }
                    if !self.started() {
                        // Pre-match, a timeout is a Leave this peer never
                        // sent: evict the slot outright rather than leave a
                        // phantom entry `start_match` would still count.
                        self.peers.remove(slot);
                        self.reindex_peers();
                        self.broadcast_roster();
                        continue; // the next peer has shifted down into this position
                    }
                    self.declare_disconnected(slot);
                    slot += 1;
                }
            }
            Role::Joiner => {
                let quiet = self.peers.first().is_some_and(|p| {
                    p.conn
                        .seconds_since_last_activity()
                        .is_some_and(|s| s > DISCONNECT_TIMEOUT_SECS)
                });
                if quiet && !self.noticed_disconnect {
                    self.noticed_disconnect = true;
                    if let Some(m) = &mut self.machine {
                        m.notice_disconnection();
                    }
                }
            }
        }
    }

    /// spec: `DisconnectPlayer pl` for `pl ≠ Host` (§4-T7f/§15.4), host only,
    /// mid-match: marks the slot disconnected (once — `DisconnectPlayer`'s
    /// own `connected s pl` guard), applies the host's own copy of the
    /// `DisconnectMessage` directly, and relays one from `pl` to every other
    /// connected peer. From here on `handle` drops everything this slot
    /// sends. Reached from a timeout (`check_timeouts`) or a mid-match
    /// `Leave`.
    fn declare_disconnected(&mut self, slot: usize) {
        if self.role != Role::Host || !self.peers[slot].connected {
            return;
        }
        self.peers[slot].connected = false;
        let Some(pl) = self.peers[slot].index else {
            return; // never joined this match — nobody's view holds a slot for it
        };
        if let Some(m) = &mut self.machine {
            if pl < m.connected_view.len() {
                m.receive_disconnect(pl);
            }
        }
        self.send_routed_from(pl, Destination::Broadcast, Payload::Disconnect);
    }

    /// spec: §14.3 — one `OpponentView` per player but this one. `gameover`
    /// ORs the model's view with the last `State`'s own flag: rendering-only,
    /// so showing a peer as dead as soon as its broadcast says so is more
    /// responsive and can't contradict the model (`GameoverMonotone`).
    pub fn opponent_views(&self) -> Vec<OpponentView<Instance>> {
        let Some(m) = &self.machine else {
            return Vec::new();
        };
        (0..m.gameover_view.len())
            .filter(|&pl| pl != m.my_index)
            .map(|pl| {
                let remote = self.boards.get(pl).and_then(|b| b.as_ref());
                OpponentView {
                    player_index: pl,
                    name: self
                        .roster
                        .get(pl)
                        .cloned()
                        .unwrap_or_else(|| format!("P{}", pl + 1)),
                    board: remote.map(|b| OpponentBoard {
                        mg: b.mg.clone(),
                        p: b.p,
                        py: b.py,
                        px: b.px,
                        pr: b.pr,
                    }),
                    gameover: m.gameover_view[pl] || remote.is_some_and(|b| b.gameover),
                    connected: m.connected_view[pl],
                }
            })
            .collect()
    }
}

/// spec: §15.0 — the resolved winner of a finished match, or `None` while
/// more than one player is still in it.
///
/// This peer's own slot counts as playing iff it is not gameover, whatever
/// `connected_view[my_index]` says: noticing one's own disconnection
/// (`notice_disconnection`) says nothing about who else is left, so it must
/// not resolve the match in favour of the one remaining opponent — that case
/// is S10 ("connection to host lost"), not S9. Every other slot is read
/// through `playing_view`. While this peer has not noticed a disconnection,
/// `Some(my_index)` is exactly `winner_multi(.., my_index)`.
pub fn find_winner(m: &Machine<Instance>) -> Option<usize> {
    let me = m.my_index;
    let mut playing = (0..m.gameover_view.len()).filter(|&pl| {
        if pl == me {
            !m.gameover_view[me]
        } else {
            crate::model::playing_view(&m.gameover_view, &m.connected_view, pl)
        }
    });
    match (playing.next(), playing.next()) {
        (Some(w), None) => Some(w),
        _ => None,
    }
}

/// Turns an already-resolved `Endpoint::discover()` result into an
/// `Endpoint`, reporting failure into `status` rather than panicking. Split
/// out from `mint_endpoint` so the same status-message logic applies
/// whether discovery ran synchronously or on `PendingEndpoint`'s background
/// thread.
pub fn endpoint_discovered(
    result: io::Result<(Endpoint, bool)>,
    status: &mut String,
) -> Option<Endpoint> {
    match result {
        // Silent on success — the code itself is the confirmation; a
        // "discovered via STUN" line was noise nobody acted on.
        Ok((ep, true)) => {
            *status = String::new();
            Some(ep)
        }
        Ok((ep, false)) => {
            *status = "Warning: public address couldn't be discovered by STUN.".into();
            Some(ep)
        }
        Err(e) => {
            *status = format!("Could not open a socket: {e}");
            None
        }
    }
}

/// Mints a fresh endpoint synchronously, blocking on the STUN round trip.
/// Every interactive call site instead uses `PendingEndpoint` so a
/// slow/absent STUN server never freezes the frame loop; this stays around
/// for the one place that genuinely wants a synchronous mint — a test
/// standing in for a second process's own joiner.
pub fn mint_endpoint(status: &mut String) -> Option<Endpoint> {
    endpoint_discovered(Endpoint::discover(), status)
}

/// spec: §15.2 — runs `Endpoint::discover()` on a background thread and
/// hands the result back through a channel so the STUN round trip never
/// blocks the frame loop; the one-shot analogue of `NetWorkerHandle`'s own
/// background-thread-plus-channel shape.
pub struct PendingEndpoint(mpsc::Receiver<io::Result<(Endpoint, bool)>>);

impl PendingEndpoint {
    pub fn spawn() -> PendingEndpoint {
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            let _ = tx.send(Endpoint::discover());
        });
        PendingEndpoint(rx)
    }

    /// Non-blocking: `None` while discovery is still in flight.
    pub fn poll(&self) -> Option<io::Result<(Endpoint, bool)>> {
        self.0.try_recv().ok()
    }
}

/// Registers `endpoint`'s socket against `net` as the connection to the
/// peer named by `code`: both of its advertised addresses
/// (`ConnectionCode::candidates`, §15.2 step 3) are punched at once, and
/// the peer must prove itself with the nonce in `code` before anything from
/// it is accepted. `net` immediately starts sending `Hello`, punching the
/// local NAT mapping open in the process.
pub fn connect_to(
    net: &NetWorkerHandle,
    endpoint: Endpoint,
    code: ConnectionCode,
) -> io::Result<Connection> {
    let candidates: Vec<SocketAddr> = code.candidates().into_iter().map(SocketAddr::V4).collect();
    net.register(
        endpoint.socket,
        &candidates,
        endpoint.nonce,
        code.nonce,
        max_decoded_message_bytes(),
    )
}

/// `Instance::initial_main_grid()`'s own dimensions (`rows`, `cols`) — the
/// one place both `apply_local`'s `State.mg` shape check and
/// `max_decoded_message_bytes`'s decode-size bound read them from, so the
/// two call sites can't silently drift apart.
pub fn instance_grid_dims() -> (usize, usize) {
    let mg = Instance::initial_main_grid();
    (mg.len(), mg.first().map_or(0, |r| r.len()))
}

/// Number of rotation states a piece can be in — `t1::model`'s rotation is
/// taken modulo 4, so a valid `pr` is always below this.
const ROTATION_COUNT: u8 = 4;

/// Validates a peer-supplied `Payload::State` and converts it into a
/// renderable `RemoteBoard`; `None` for any other payload, and for a `State`
/// the renderer could not draw safely. Every field is peer-controlled:
/// - `p` and every `mg` cell must name a piece this build has;
/// - `mg` must have this instance's exact board dimensions;
/// - `pr` must be a real rotation (the renderer indexes the rotation table
///   with it);
/// - `py`/`px` must lie within one piece width of the board (the renderer
///   adds piece offsets to them, which must not overflow).
pub fn remote_board_from(body: &Payload) -> Option<RemoteBoard> {
    let Payload::State {
        p,
        py,
        px,
        pr,
        mg,
        gameover,
    } = body
    else {
        return None;
    };
    let p = net::code_to_piece(*p)?;
    if *pr >= ROTATION_COUNT {
        return None;
    }
    let (expected_h, expected_w) = instance_grid_dims();
    let pw = Instance::PW;
    let in_range = |v: i64, len: usize| -pw <= v && v <= len as i64 + pw;
    if !in_range(*py, expected_h) || !in_range(*px, expected_w) {
        return None;
    }
    if mg.len() != expected_h || mg.iter().any(|row| row.len() != expected_w) {
        return None;
    }
    let mut rows: Vec<Vec<Cell>> = Vec::with_capacity(mg.len());
    for row in mg {
        let mut out: Vec<Cell> = Vec::with_capacity(row.len());
        for cell in row {
            out.push(match cell {
                None => None,
                Some(c) => Some(t1::model::PieceOrExtra::<Instance>::try_from(*c).ok()?),
            });
        }
        rows.push(out);
    }
    Some(RemoteBoard {
        mg: rows,
        p,
        py: *py,
        px: *px,
        pr: *pr,
        gameover: *gameover,
    })
}

/// The decode-size bound this build's connections should enforce; `net.rs`
/// treats the bound as caller-supplied and opaque since the grid dimensions
/// are a fact only this crate knows.
pub fn max_decoded_message_bytes() -> u64 {
    let (rows, cols) = instance_grid_dims();
    net::recommended_max_decoded_bytes(rows, cols)
}
