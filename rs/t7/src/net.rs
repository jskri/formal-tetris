//! spec: net.rs — networking (§15.2–§15.5, `implementation.md`).
//!
//! Public (§0.4): another binary can reuse this transport layer without
//! reimplementing it; `model.rs` never imports it and stays fully testable
//! without a socket ever opening.
//!
//! Ships the *transport* layer in full: STUN, the reliable and best-effort
//! framing/delivery guarantees over one shared `UdpSocket` per connection,
//! and `WireMessage`'s own encode/decode. It does **not** ship the *lobby
//! state machine* (roster exchange, `Start`, host relay decisions,
//! disconnect-timeout policy) — that is `t7::session`'s job, layered on top
//! of `Connection`'s plain `incoming`/`outgoing` channels. `t7::session::Session`
//! is fully wired against this module (`Connection`, `ConnectionCode`,
//! `WireMessage`) and exercised end to end, over real loopback UDP, in
//! `tests/session_integration_test.rs`. Most of this module's own transport
//! mechanism (STUN, wire codec, packet framing, the pure delivery state
//! machines) is exercised directly in `tests/net_unit_test.rs`; a handful of
//! tests pinned to private tuning constants stay in this file's own `tests`
//! module below.
//!
//! **Design**, top to bottom:
//! - [`stun`] — a minimal, hand-rolled RFC 5389 client (§15.2).
//! - [`WireMessage`] — the wire format (§15.3), JSON- then
//!   deflate-encoded (`encode_message`/`decode_message`).
//! - A one-byte-tagged outer packet framing (`encode_packet`/
//!   `decode_packet`) distinguishing reliable data, an ack, and
//!   best-effort data on the one shared socket.
//! - [`ReliableSender`]/[`ReliableReceiver`]/[`BestEffortReceiver`] — pure,
//!   socket-free state machines implementing §15.2's two delivery
//!   guarantees, unit-tested without a real socket.
//! - [`NetWorkerHandle`]/[`Connection`] — one round-robin thread per
//!   `Session` (§15.5), visiting each connection in turn to drain its
//!   outgoing queue and run a short-timeout receive.
//!
//! **Hole-punching is folded into the reliable channel** (§15.2): the
//! initial `Hello{nonce}` is sent as a normal reliable message, so
//! `ReliableSender`'s own retransmit timer supplies "a few packets, a bit
//! apart" for free — no separate punch routine is needed. Deciding when to
//! reply `HelloAck` is the lobby layer's job; this module only guarantees
//! `Hello{nonce}` eventually arrives and any reply eventually arrives back.

// `DecodeError`'s variants carry the underlying error only for
// `Debug`/logging use — callers just match `Ok`/`Err` and drop the `Err`
// payload unread.
#![allow(dead_code)]

use serde::{Deserialize, Serialize};
use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, HashMap};
use std::hash::{Hash, Hasher};
use std::io::{self, Read, Write};
use std::net::{SocketAddr, UdpSocket};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

// ── STUN (§15.2 step 1) ──────────────────────────────────────────────────

/// spec: §15.2 — a minimal, hand-rolled RFC 5389 client (no dependency;
/// kept short and auditable). IPv4-only — `XOR-MAPPED-ADDRESS`'s IPv6 case
/// (`family = 0x02`) is left unhandled.
pub mod stun {
    use super::*;

    const MAGIC_COOKIE: u32 = 0x2112_A442;
    const BINDING_REQUEST: u16 = 0x0001;
    const BINDING_RESPONSE: u16 = 0x0101;
    const XOR_MAPPED_ADDRESS: u16 = 0x0020;
    const FAMILY_IPV4: u8 = 0x01;

    /// spec: RFC 5389 §6 — a STUN message header is `type(2) | length(2) |
    /// magic-cookie(4) | transaction-id(12)`, no attributes for a bare
    /// Binding Request.
    pub fn build_binding_request(txid: [u8; 12]) -> Vec<u8> {
        let mut msg = Vec::with_capacity(20);
        msg.extend_from_slice(&BINDING_REQUEST.to_be_bytes());
        msg.extend_from_slice(&0u16.to_be_bytes()); // length: no attributes
        msg.extend_from_slice(&MAGIC_COOKIE.to_be_bytes());
        msg.extend_from_slice(&txid);
        msg
    }

    /// spec: RFC 5389 §15.2 — `XOR-MAPPED-ADDRESS`'s port/address are XORed
    /// against the magic cookie (address: the full 32-bit cookie; port: its
    /// high 16 bits) so they don't appear as literal addresses to
    /// address-rewriting NAT boxes inspecting the payload in transit.
    pub fn parse_binding_response(data: &[u8], expected_txid: &[u8; 12]) -> Option<SocketAddr> {
        if data.len() < 20 {
            return None;
        }
        let msg_type = u16::from_be_bytes([data[0], data[1]]);
        let msg_len = u16::from_be_bytes([data[2], data[3]]) as usize;
        let cookie = u32::from_be_bytes([data[4], data[5], data[6], data[7]]);
        if msg_type != BINDING_RESPONSE || cookie != MAGIC_COOKIE || &data[8..20] != expected_txid {
            return None;
        }
        let attrs = data.get(20..20 + msg_len)?;

        let mut i = 0;
        while i + 4 <= attrs.len() {
            let atype = u16::from_be_bytes([attrs[i], attrs[i + 1]]);
            let alen = u16::from_be_bytes([attrs[i + 2], attrs[i + 3]]) as usize;
            let vstart = i + 4;
            let vend = vstart.checked_add(alen)?;
            if vend > attrs.len() {
                break; // truncated/malformed attribute — stop rather than misparse
            }
            if atype == XOR_MAPPED_ADDRESS && alen >= 8 && attrs[vstart + 1] == FAMILY_IPV4 {
                let xport = u16::from_be_bytes([attrs[vstart + 2], attrs[vstart + 3]]);
                let port = xport ^ ((MAGIC_COOKIE >> 16) as u16);
                let xaddr = u32::from_be_bytes([
                    attrs[vstart + 4],
                    attrs[vstart + 5],
                    attrs[vstart + 6],
                    attrs[vstart + 7],
                ]);
                let addr = std::net::Ipv4Addr::from(xaddr ^ MAGIC_COOKIE);
                return Some(SocketAddr::new(addr.into(), port));
            }
            // STUN attributes are padded to a 4-byte boundary.
            i = vstart + alen.div_ceil(4) * 4;
        }
        None
    }

    /// One Binding Request/Response round trip, retried up to `retries`
    /// times (a UDP send can silently be lost, same as any other packet on
    /// this transport). `socket`'s read timeout is set to `timeout` for the
    /// duration of the call.
    pub fn query(
        socket: &UdpSocket,
        server: SocketAddr,
        timeout: Duration,
        retries: u32,
    ) -> io::Result<SocketAddr> {
        socket.set_read_timeout(Some(timeout))?;
        let mut buf = [0u8; 1500];
        for _ in 0..retries.max(1) {
            let txid = fresh_txid();
            socket.send_to(&build_binding_request(txid), server)?;
            match socket.recv_from(&mut buf) {
                Ok((n, from)) if from == server => {
                    if let Some(addr) = parse_binding_response(&buf[..n], &txid) {
                        return Ok(addr);
                    }
                }
                Ok(_) => continue, // a stray packet from someone else — ignore, retry
                Err(e)
                    if e.kind() == io::ErrorKind::WouldBlock
                        || e.kind() == io::ErrorKind::TimedOut =>
                {
                    continue
                }
                Err(e) => return Err(e),
            }
        }
        Err(io::Error::new(
            io::ErrorKind::TimedOut,
            "STUN: no response after retries",
        ))
    }

    fn fresh_txid() -> [u8; 12] {
        let a = fresh_u64();
        let b = fresh_u64();
        let mut txid = [0u8; 12];
        txid[0..8].copy_from_slice(&a.to_le_bytes());
        txid[8..12].copy_from_slice(&(b as u32).to_le_bytes());
        txid
    }
}

/// Not cryptographic — only needs to be unlikely to collide, not
/// unguessable. Seeds `DefaultHasher` with the current time and a
/// process-lifetime counter, avoiding a `rand` crate dependency (§15.2).
fn fresh_u64() -> u64 {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let mut h = DefaultHasher::new();
    Instant::now().hash(&mut h);
    COUNTER.fetch_add(1, Ordering::Relaxed).hash(&mut h);
    h.finish()
}

// ── Connection code (§15.1) ──────────────────────────────────────────────

/// spec: §15.1 — a short connection code (public + local address + a
/// random nonce) to share out-of-band. Lives here, not in lobby code: it
/// is the STUN lookup's own output plus the local socket's address — a
/// transport fact. IPv4-only, matching [`stun::parse_binding_response`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConnectionCode {
    pub public: std::net::SocketAddrV4,
    pub local: std::net::SocketAddrV4,
    pub nonce: u64,
}

/// Crockford's base32 alphabet — no `I`, `L`, `O`, or `U`, so a code read
/// aloud over a voice call (§15.1's own suggested exchange channel) has no
/// `1`/`I`/`l` or `0`/`O` ambiguity to trip over, and no accidental
/// profanity. 20 bytes of payload encode to exactly 32 characters with no
/// padding.
pub const B32_ALPHABET: &[u8; 32] = b"0123456789ABCDEFGHJKMNPQRSTVWXYZ";

pub fn b32_encode(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len().div_ceil(5) * 8);
    let (mut acc, mut bits) = (0u32, 0u32);
    for &b in bytes {
        acc = (acc << 8) | b as u32;
        bits += 8;
        while bits >= 5 {
            bits -= 5;
            out.push(B32_ALPHABET[((acc >> bits) & 31) as usize] as char);
        }
    }
    if bits > 0 {
        out.push(B32_ALPHABET[((acc << (5 - bits)) & 31) as usize] as char);
    }
    out
}

/// Case-insensitive; `-` and whitespace are skipped (so a code may be
/// written in readable groups), and Crockford's own confusable mappings
/// are honored on input: `I`/`L` read as `1`, `O` reads as `0`. `None` on
/// any other unrecognized character.
pub fn b32_decode(s: &str) -> Option<Vec<u8>> {
    let mut out = Vec::new();
    let (mut acc, mut bits) = (0u32, 0u32);
    for c in s.chars() {
        if c == '-' || c.is_whitespace() {
            continue;
        }
        let v = b32_value(c)?;
        acc = (acc << 5) | v as u32;
        bits += 5;
        if bits >= 8 {
            bits -= 8;
            out.push(((acc >> bits) & 0xFF) as u8);
        }
    }
    Some(out)
}

fn b32_value(c: char) -> Option<u8> {
    let c = c.to_ascii_uppercase();
    match c {
        'I' | 'L' => Some(1),
        'O' => Some(0),
        _ => B32_ALPHABET
            .iter()
            .position(|&x| x as char == c)
            .map(|i| i as u8),
    }
}

impl ConnectionCode {
    /// `4 + 2` (public) `+ 4 + 2` (local) `+ 8` (nonce) — exactly 20 bytes,
    /// hence exactly 32 base32 characters.
    const BYTES: usize = 20;

    fn to_bytes(self) -> [u8; Self::BYTES] {
        let mut b = [0u8; Self::BYTES];
        b[0..4].copy_from_slice(&self.public.ip().octets());
        b[4..6].copy_from_slice(&self.public.port().to_be_bytes());
        b[6..10].copy_from_slice(&self.local.ip().octets());
        b[10..12].copy_from_slice(&self.local.port().to_be_bytes());
        b[12..20].copy_from_slice(&self.nonce.to_be_bytes());
        b
    }

    fn from_bytes(b: &[u8]) -> Option<Self> {
        let b: &[u8; Self::BYTES] = b.try_into().ok()?;
        let addr = |o: &[u8], p: &[u8]| {
            std::net::SocketAddrV4::new(
                std::net::Ipv4Addr::new(o[0], o[1], o[2], o[3]),
                u16::from_be_bytes([p[0], p[1]]),
            )
        };
        Some(ConnectionCode {
            public: addr(&b[0..4], &b[4..6]),
            local: addr(&b[6..10], &b[10..12]),
            nonce: u64::from_be_bytes(b[12..20].try_into().expect("8 bytes")),
        })
    }

    /// Which of the peer's two addresses to punch toward. If the peer's
    /// public IP equals our own, we're behind the same NAT: many routers
    /// won't hairpin a packet back to their own external address, so the
    /// peer's LAN address is the one that works. Otherwise the public
    /// address is the only one routable to them.
    pub fn best_target(&self, my_public: std::net::SocketAddrV4) -> std::net::SocketAddrV4 {
        if self.public.ip() == my_public.ip() {
            self.local
        } else {
            self.public
        }
    }
}

impl std::fmt::Display for ConnectionCode {
    /// Grouped in 8s (`XXXXXXXX-XXXXXXXX-XXXXXXXX-XXXXXXXX`) purely for
    /// legibility when read aloud or retyped; `from_str` skips the dashes.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = b32_encode(&self.to_bytes());
        let groups: Vec<&str> = (0..s.len())
            .step_by(8)
            .map(|i| &s[i..(i + 8).min(s.len())])
            .collect();
        write!(f, "{}", groups.join("-"))
    }
}

impl std::str::FromStr for ConnectionCode {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, ()> {
        // 32 base32 chars carry 160 bits = 20 bytes exactly, so a
        // well-formed code decodes to exactly BYTES with no trailing
        // partial byte to discard.
        ConnectionCode::from_bytes(&b32_decode(s).ok_or(())?).ok_or(())
    }
}

// ── Wire format (§15.3) ──────────────────────────────────────────────────

/// A piece, on the wire: its **index into `Tetris::piece_all()`**, not the
/// `t1::instance::Piece` value itself. `t1` is a frozen input with no
/// `serde` derive on `Piece`; the index into the finite enumeration
/// `piece_all()` returns is the one encoding every `Params` instantiation
/// already guarantees well-defined, and both peers run the same binary so
/// the ordering is unambiguous between them.
pub type PieceCode = u8;

/// Panics on a piece not in `piece_all()` — impossible for any value the
/// engine produces (`t1::model::type_ok`'s own `piece_all().contains(&s.p)`
/// conjunct, checked by `check_invariants`), hence an `expect` rather than
/// a `Result` the caller would have no meaningful way to handle.
pub fn piece_to_code(p: t1::instance::Piece) -> PieceCode {
    <crate::instance::Tetris as t1::model::Params>::piece_all()
        .iter()
        .position(|&q| q == p)
        .expect("p is always a member of piece_all() — t1::model::type_ok's own conjunct")
        as PieceCode
}

/// `None` for an out-of-range code — this reads attacker-or-corruption-
/// reachable wire input, unlike `piece_to_code`'s engine-internal input,
/// so it validates rather than asserting.
pub fn code_to_piece(code: PieceCode) -> Option<t1::instance::Piece> {
    <crate::instance::Tetris as t1::model::Params>::piece_all()
        .get(code as usize)
        .copied()
}

/// A locked `mg` cell, wire-serializable — `t1::model::PieceOrExtra<P>`
/// itself carries no `serde` dependency (a `model.rs`-owned type, generic
/// over any `Params`); this is `net.rs`'s own concrete stand-in,
/// specialized to `crate::instance::Tetris`.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum GridCell {
    Piece(PieceCode),
    Garbage,
}

impl From<t1::model::PieceOrExtra<crate::instance::Tetris>> for GridCell {
    fn from(c: t1::model::PieceOrExtra<crate::instance::Tetris>) -> Self {
        match c {
            t1::model::PieceOrExtra::Piece(p) => GridCell::Piece(piece_to_code(p)),
            t1::model::PieceOrExtra::Extra(crate::model::Garbage) => GridCell::Garbage,
        }
    }
}

/// `None` on an out-of-range `PieceCode` (see `code_to_piece`) — the whole
/// received `State` is then discarded by the caller rather than rendered
/// with a guessed piece.
impl TryFrom<GridCell> for t1::model::PieceOrExtra<crate::instance::Tetris> {
    type Error = ();

    fn try_from(c: GridCell) -> Result<Self, ()> {
        Ok(match c {
            GridCell::Piece(code) => t1::model::PieceOrExtra::Piece(code_to_piece(code).ok_or(())?),
            GridCell::Garbage => t1::model::PieceOrExtra::Extra(crate::model::Garbage),
        })
    }
}

/// spec: §15.3 — every message this app sends, lobby/handshake and
/// application alike, in one flat enum; `Message` below adds
/// addressing/generation metadata for the four variants that need it.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Payload {
    Join {
        name: String,
    }, // lobby-only
    Players {
        roster: Vec<String>,
    }, // lobby-only
    Start {
        player_count: usize,
        my_index: usize,
        match_gen: u64,
    }, // lobby-only
    /// Sent by a joiner clicking "Leave" on the winner screen. Host evicts
    /// the sender's slot outright and rebroadcasts `Players` — unlike a
    /// mid-match disconnect, a `Leave` slot isn't kept as a phantom for the
    /// next match. spec: §15.1b (lobby message, untagged by `match_gen`).
    Leave,
    Hello {
        nonce: u64,
    }, // handshake-only (§15.2)
    HelloAck {
        nonce: u64,
    }, // handshake-only
    /// Lobby-only keepalive: before `Start`, `State`'s own broadcast isn't
    /// flowing yet to double as keepalive, so both sides send `Ping` on a
    /// short period instead. No payload; any valid `WireMessage` already
    /// refreshes the connection's last-activity timestamp. spec: §15.2.
    Ping,
    Garbage {
        amount: i64,
    }, // spec: GarbageMessage
    Gameover,   // spec: GameoverMessage
    Disconnect, // spec: DisconnectMessage
    State {
        // rendering-only, best-effort channel (§15.3)
        p: PieceCode,
        py: i64,
        px: i64,
        pr: u8,
        mg: Vec<Vec<Option<GridCell>>>,
        gameover: bool,
    },
}

/// Where a `Message` should end up — named instead of `Option<usize>` so
/// `Broadcast` reads as the deliberate choice it is at every call site.
/// spec: §15.3 — `Broadcast` means "every player but `from`," never "the
/// host" specifically; a single recipient (host included) is named via
/// `Single`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Destination {
    Single(usize),
    Broadcast,
}

impl Destination {
    /// Whether a message addressed `self` should reach the peer at roster
    /// index `idx` — `Broadcast` reaches everyone, `Single(pl)` only `pl`.
    pub fn reaches(self, idx: usize) -> bool {
        match self {
            Destination::Broadcast => true,
            Destination::Single(pl) => pl == idx,
        }
    }
}

/// The envelope `Garbage`/`Gameover`/`Disconnect`/`State` travel inside.
/// `from` is structural on a direct peer channel (whoever is on the other
/// end) but is lost at the host's relay hop unless carried explicitly, so
/// it travels here; the host overwrites `from` with the roster index of
/// the channel a message actually arrived on before relaying it onward, so
/// a joiner cannot forge traffic as another player.
///
/// `to`'s semantics are `Destination`'s own doc comment; a joiner's
/// physical send always goes to the host regardless of `to`'s value.
///
/// `match_gen`: the match-generation counter (spec: §15.1b) — incremented
/// once per `Start` (including a rematch) and carried on every application
/// message so a receiver can discard traffic from a match it has already
/// left. Lobby messages travel as `WireMessage::Untagged`, outside this
/// envelope entirely.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Message {
    pub from: usize,
    pub to: Destination,
    pub match_gen: u64,
    pub body: Payload,
}

/// spec: §15.3 — wire format; `net.rs` is the only module that ever names
/// `WireMessage` (§0.4). `Untagged` carries lobby/handshake payloads (no
/// `from`/`to`/`match_gen` needed before a match generation exists);
/// `Routed` carries `Garbage`/`Gameover`/`Disconnect`/`State` — see
/// `Message`'s own doc comment.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum WireMessage {
    Untagged(Payload),
    Routed(Message),
}

/// spec: §15.3 — JSON then deflate. Raw deflate, not gzip: no
/// checksum/filename overhead worth paying atop UDP's own checksum for a
/// payload this small.
pub fn encode_message(msg: &WireMessage) -> Vec<u8> {
    let json = serde_json::to_vec(msg).expect("WireMessage always serializes");
    let mut enc = flate2::write::DeflateEncoder::new(Vec::new(), flate2::Compression::fast());
    enc.write_all(&json)
        .expect("in-memory Vec write never fails");
    enc.finish().expect("in-memory Vec write never fails")
}

#[derive(Debug)]
pub enum DecodeError {
    Inflate(io::Error),
    Json(serde_json::Error),
}

/// Hardening (§15.2): bounds decompression against a caller-supplied byte
/// cap, so a small compressible payload can't inflate unboundedly. The
/// bound is a parameter, not a module constant — the largest legitimate
/// message (`Payload::State`'s `mg` snapshot) depends on the board
/// dimensions, which `net.rs` has no `Instance` of its own to ask;
/// `main.rs` computes it via `recommended_max_decoded_bytes` and threads
/// it through `NetWorkerHandle::register` → `Control::Register` →
/// `ConnState` → `service_one`.
pub fn decode_message(bytes: &[u8], max_bytes: u64) -> Result<WireMessage, DecodeError> {
    let mut dec = flate2::read::DeflateDecoder::new(bytes).take(max_bytes);
    let mut json = Vec::new();
    dec.read_to_end(&mut json).map_err(DecodeError::Inflate)?;
    serde_json::from_slice(&json).map_err(DecodeError::Json)
}

/// Conservative upper bound on the JSON text size of one `Option<GridCell>`
/// cell inside `Payload::State.mg`: `Some(GridCell::Piece(255))` serializes
/// to `{"Piece":255}` (14 bytes) plus a separating comma — rounded
/// generously up so a future field on `GridCell`/`State` doesn't require
/// retuning this.
const BYTES_PER_CELL_UPPER_BOUND: u64 = 32;

/// Headroom for `State`'s other fields (`p`/`py`/`px`/`pr`/`gameover`) and
/// the enclosing JSON object/array punctuation.
const STATE_OVERHEAD_BYTES: u64 = 512;

/// A floor so a tiny board doesn't get an unreasonably tight decode cap.
pub const MIN_DECODED_MESSAGE_BYTES: u64 = 4096;

/// A `decode_message` bound sized off one connection's actual board
/// dimensions. `rows`/`cols` are opaque to this module (`decode_message`'s
/// own doc comment) — this function only knows how many bytes *this
/// module's own wire format* spends per cell. `main.rs` is the only
/// production caller (`connect_to`), reading `rows`/`cols` off
/// `Instance::initial_main_grid()`.
pub fn recommended_max_decoded_bytes(rows: usize, cols: usize) -> u64 {
    let cells = (rows as u64).saturating_mul(cols as u64);
    let estimate =
        STATE_OVERHEAD_BYTES.saturating_add(cells.saturating_mul(BYTES_PER_CELL_UPPER_BOUND));
    // Doubled for headroom beyond worst-case JSON text — State is not the
    // only WireMessage decode_message ever sees — deliberately generous,
    // not tight.
    estimate.saturating_mul(2).max(MIN_DECODED_MESSAGE_BYTES)
}

// ── Outer packet framing: one byte tag distinguishes reliable data, an ──
// ── ack, and best-effort data on the one shared socket (§15.2's close). ──

pub const TAG_RELIABLE: u8 = 0;
const TAG_ACK: u8 = 1;
const TAG_BEST_EFFORT: u8 = 2;

pub fn encode_packet(tag: u8, seq: u64, payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(9 + payload.len());
    out.push(tag);
    out.extend_from_slice(&seq.to_be_bytes());
    out.extend_from_slice(payload);
    out
}

/// `None` on anything too short to hold a header — a malformed/truncated
/// packet is simply dropped by the caller, never a panic.
pub fn decode_packet(bytes: &[u8]) -> Option<(u8, u64, &[u8])> {
    if bytes.len() < 9 {
        return None;
    }
    let tag = bytes[0];
    let seq = u64::from_be_bytes(bytes[1..9].try_into().expect("length checked above"));
    Some((tag, seq, &bytes[9..]))
}

// ── Reliable delivery (§15.2): sequence number, acked, unacked ──────────
// ── retransmitted on a short timer; delivered only up through the next ──
// ── contiguous sequence number. Pure, socket-free — see module doc. ─────

const RETRANSMIT_INTERVAL: Duration = Duration::from_millis(300);

/// Hardening (§15.2): caps `ReliableSender::unacked` so a peer that keeps
/// the connection superficially alive (its own traffic keeps resetting
/// `seconds_since_last_activity`, so the disconnect timeout never trips)
/// but never acks anything can't grow it unbounded over a long match. Far
/// larger than any backlog this app's own low-volume reliable traffic
/// could produce against a responsive peer.
const MAX_UNACKED_MESSAGES: usize = 1024;

/// Send side. `send`/`due_retransmits` return raw wire bytes (packet
/// framing + encoded message) ready to hand to a socket — kept here rather
/// than in `Connection` so the retransmit *policy* (what counts as "due,"
/// what to resend) is exercised by this module's own unit tests without a
/// real socket or a real clock tick.
pub struct ReliableSender {
    next_seq: u64,
    unacked: BTreeMap<u64, (Vec<u8>, Instant)>,
}

impl Default for ReliableSender {
    fn default() -> Self {
        Self::new()
    }
}

impl ReliableSender {
    pub fn new() -> Self {
        ReliableSender {
            next_seq: 0,
            unacked: BTreeMap::new(),
        }
    }

    /// Assigns the next sequence number, encodes `msg`, records it for
    /// retransmission, and returns the bytes to send now. If `unacked` is
    /// already at `MAX_UNACKED_MESSAGES`, the single oldest entry is
    /// evicted first — an unresponsive-enough peer to hit this cap already
    /// implies those messages aren't landing anyway.
    pub fn send(&mut self, msg: &WireMessage, now: Instant) -> Vec<u8> {
        let seq = self.next_seq;
        self.next_seq += 1;
        let bytes = encode_packet(TAG_RELIABLE, seq, &encode_message(msg));
        // Evicting the oldest entry bounds memory, but isn't merely
        // space-freeing: the evicted message is never retransmitted, so if
        // it was genuinely lost, the receiver's next_expected can never
        // advance past that gap — every later reliable message on this
        // connection sits in the receiver's reorder buffer forever (or is
        // dropped once it falls outside MAX_REORDER_WINDOW). Acceptable
        // only because reaching this cap requires ~1024 distinct reliable
        // sends, which this app's low-volume traffic would take a long
        // time to produce against a peer that isn't already unresponsive.
        if self.unacked.len() >= MAX_UNACKED_MESSAGES {
            if let Some(&oldest) = self.unacked.keys().next() {
                self.unacked.remove(&oldest);
            }
        }
        self.unacked.insert(seq, (bytes.clone(), now));
        bytes
    }

    /// A duplicate/late ack for an already-removed `seq` is a no-op —
    /// idempotent, matching a reliable channel's own tolerance for a
    /// redundant ack (the peer may re-ack an already-delivered packet, see
    /// `ReliableReceiver::on_packet`'s own doc comment).
    pub fn on_ack(&mut self, seq: u64) {
        self.unacked.remove(&seq);
    }

    /// Every still-unacked packet last (re)transmitted more than
    /// `RETRANSMIT_INTERVAL` ago, in ascending sequence order. spec: §15.2
    /// — a short timer, not exponential backoff (no other traffic on this
    /// connection to back off from).
    pub fn due_retransmits(&mut self, now: Instant) -> Vec<Vec<u8>> {
        let mut due = Vec::new();
        for (bytes, last_sent) in self.unacked.values_mut() {
            if now.duration_since(*last_sent) >= RETRANSMIT_INTERVAL {
                *last_sent = now;
                due.push(bytes.clone());
            }
        }
        due
    }
}

/// Hardening (§15.2): caps `ReliableReceiver::pending` so a peer sending
/// ever-increasing sequence numbers without the filling packet can't grow
/// it unbounded. Far larger than any legitimate reordering gap this app's
/// own low-volume traffic could produce.
const MAX_REORDER_WINDOW: u64 = 1024;

/// Receive side. Buffers out-of-order arrivals; delivers only through the
/// next contiguous sequence number. spec: §15.2 — realizes `T7.v`'s
/// "reliable, no loss/duplication/reordering" network axiom rather than
/// merely assuming it.
pub struct ReliableReceiver {
    next_expected: u64,
    pending: BTreeMap<u64, WireMessage>,
}

impl Default for ReliableReceiver {
    fn default() -> Self {
        Self::new()
    }
}

impl ReliableReceiver {
    pub fn new() -> Self {
        ReliableReceiver {
            next_expected: 0,
            pending: BTreeMap::new(),
        }
    }

    /// Returns `Some(seq)` as the ack to send back — including for a
    /// duplicate/already-delivered `seq < next_expected`, since re-acking
    /// is the only way the peer's `ReliableSender` ever stops
    /// retransmitting it. Returns `None` when `seq` falls outside
    /// `MAX_REORDER_WINDOW`, dropped unbuffered and deliberately not
    /// acked — acking a packet this receiver didn't keep would falsely
    /// tell the sender to stop retransmitting something still lost.
    /// Returns every message newly deliverable in contiguous order (empty
    /// if `seq` only filled a gap further out, or duplicated one already
    /// delivered).
    pub fn on_packet(&mut self, seq: u64, msg: WireMessage) -> (Option<u64>, Vec<WireMessage>) {
        if seq >= self.next_expected {
            if seq - self.next_expected >= MAX_REORDER_WINDOW {
                return (None, Vec::new());
            }
            self.pending.insert(seq, msg);
        } // else: duplicate of an already-delivered seq — nothing to buffer, still ack it

        let mut delivered = Vec::new();
        while let Some(m) = self.pending.remove(&self.next_expected) {
            delivered.push(m);
            self.next_expected += 1;
        }
        (Some(seq), delivered)
    }
}

/// Best-effort delivery (§15.2, `State` only): no seq/ack/retransmit — a
/// monotonic counter lets the receiver discard a packet older than the
/// last one already applied.
#[derive(Default)]
pub struct BestEffortReceiver {
    last_applied: Option<u64>,
}

impl BestEffortReceiver {
    pub fn on_packet(&mut self, seq: u64, msg: WireMessage) -> Option<WireMessage> {
        if self.last_applied.is_none_or(|last| seq > last) {
            self.last_applied = Some(seq);
            Some(msg)
        } else {
            None // stale — superseded by (or a duplicate of) one already applied
        }
    }
}

// ── NetWorkerHandle/Connection: one round-robin thread per Session ──────

/// Which of §15.2's two delivery guarantees an outgoing message should get.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reliability {
    Reliable,
    BestEffort,
}

const RECV_POLL_TIMEOUT: Duration = Duration::from_millis(50);

type ConnId = u64;

/// One connection's worker-thread-owned state: the socket plus the three
/// reliability state machines above. spec: §15.5 — one round-robin thread
/// per `Session`, visiting each connection's entry in turn.
struct ConnState {
    socket: UdpSocket,
    out_rx: mpsc::Receiver<(Reliability, WireMessage)>,
    event_tx: mpsc::Sender<WireMessage>,
    last_activity: Arc<std::sync::Mutex<Option<Instant>>>,
    sender: ReliableSender,
    receiver: ReliableReceiver,
    best_effort: BestEffortReceiver,
    best_effort_next_seq: u64,
    max_decoded_bytes: u64,
    // Diagnostics only, for tracking down asymmetric packet loss such as a
    // peer's best-effort `State` stream (the minigrid data) never arriving
    // despite the reliable handshake having gone through — see
    // net_debug_tick's doc comment.
    best_effort_sent: u64,
    best_effort_recv: u64,
    net_debug_logged_at: Instant,
}

/// Messages from a `NetWorkerHandle`/`Connection` to the one worker thread
/// they share. Both variants are fire-and-forget: the worker owns nothing
/// but a socket and some buffers per connection, so there is no state for a
/// caller to race by not waiting on an acknowledgement.
enum Control {
    Register {
        id: ConnId,
        socket: UdpSocket,
        out_rx: mpsc::Receiver<(Reliability, WireMessage)>,
        event_tx: mpsc::Sender<WireMessage>,
        last_activity: Arc<std::sync::Mutex<Option<Instant>>>,
        max_decoded_bytes: u64,
    },
    Deregister(ConnId),
}

/// A cheaply-`Clone`-able handle to one `Session`'s round-robin network
/// thread. `Session` holds one — minted once by `new_host` (the host lobby
/// starts with zero connections), or handed in by whatever minted the
/// first connection for `new_joiner` — and every `Connection` registered
/// against it keeps its own clone, purely so `Drop` can reach the worker
/// without going back through `Session`.
#[derive(Clone)]
pub struct NetWorkerHandle {
    control: mpsc::Sender<Control>,
    next_id: Arc<AtomicU64>, // Relaxed: the frame thread is the only real caller; kept atomic since the handle is `Clone`
}

impl NetWorkerHandle {
    /// Starts the one thread this handle (and every clone of it) shares.
    /// No explicit shutdown call anywhere — see `worker_loop`'s own doc
    /// comment for why none is needed.
    pub fn spawn() -> NetWorkerHandle {
        let (control, control_rx) = mpsc::channel();
        thread::spawn(move || worker_loop(control_rx));
        NetWorkerHandle {
            control,
            next_id: Arc::new(AtomicU64::new(0)),
        }
    }

    /// `socket` is connected to `peer` (`UdpSocket::connect`, filtering any
    /// packet not from `peer` at the OS level — the star topology's own
    /// one-connection-one-socket model) and `set_read_timeout`/the initial
    /// `Hello { nonce: local_nonce }` enqueue (the hole-punch handshake
    /// folded into the reliable channel, module doc comment above) happen
    /// synchronously here, on the caller's own thread — only handing the
    /// socket itself to the worker thread crosses a channel, without
    /// blocking on the worker ever picking it up. `max_decoded_bytes` is
    /// threaded straight through to `service_one`'s `decode_message` calls
    /// — see `decode_message`'s own doc comment for why this module takes
    /// it as an opaque parameter rather than computing it.
    pub fn register(
        &self,
        socket: UdpSocket,
        peer: SocketAddr,
        local_nonce: u64,
        max_decoded_bytes: u64,
    ) -> io::Result<Connection> {
        socket.connect(peer)?;
        socket.set_read_timeout(Some(RECV_POLL_TIMEOUT))?;

        let id = self.next_id.fetch_add(1, Ordering::Relaxed);
        let (event_tx, event_rx) = mpsc::channel();
        let (out_tx, out_rx) = mpsc::channel();
        // `None` until the peer's first packet actually arrives — see
        // `Connection::seconds_since_last_activity`'s own doc comment for why
        // this must not start ticking at registration time.
        let last_activity = Arc::new(std::sync::Mutex::new(None));

        out_tx
            .send((
                Reliability::Reliable,
                WireMessage::Untagged(Payload::Hello { nonce: local_nonce }),
            ))
            .expect("out_rx held by the Control::Register below, not yet dropped");

        let _ = self.control.send(Control::Register {
            id,
            socket,
            out_rx,
            event_tx,
            last_activity: Arc::clone(&last_activity),
            max_decoded_bytes,
        });

        Ok(Connection {
            incoming: event_rx,
            outgoing: out_tx,
            last_activity,
            id,
            control: self.control.clone(),
        })
    }
}

/// One peer connection, from the frame thread's point of view: an
/// `incoming`/`outgoing` `mpsc` pair, backed by one entry in a shared
/// `NetWorkerHandle`'s round-robin thread (§15.5).
pub struct Connection {
    pub incoming: mpsc::Receiver<WireMessage>,
    pub outgoing: mpsc::Sender<(Reliability, WireMessage)>,
    last_activity: Arc<std::sync::Mutex<Option<Instant>>>,
    id: ConnId,
    control: mpsc::Sender<Control>,
}

impl Connection {
    /// Wall-clock time since any packet (data or ack, from `peer`) was last
    /// received — the raw signal a disconnect-timeout policy reads; this
    /// module makes no timeout decision of its own.
    ///
    /// `None` means no packet has ever arrived, distinct from "arrived long
    /// ago": this connection's clock otherwise starts ticking at
    /// `register()` time, not at first contact, and the out-of-band
    /// `ConnectionCode` exchange (§15.1) routinely takes longer than a
    /// short disconnect timeout before the peer's first packet ever
    /// arrives. A caller must treat `None` as "not yet timed out," not as
    /// a connection already dead.
    pub fn seconds_since_last_activity(&self) -> Option<f64> {
        self.last_activity
            .lock()
            .expect("poisoned only if the worker thread panicked")
            .map(|t| t.elapsed().as_secs_f64())
    }
}

impl Drop for Connection {
    /// Fire-and-forget: tells the worker to stop servicing this connection
    /// and returns immediately — there is no thread of this value's own to
    /// join. If the worker has already exited (every handle/connection for
    /// this `Session` dropping in the same wave), the send is simply a
    /// no-op into a closed channel.
    fn drop(&mut self) {
        let _ = self.control.send(Control::Deregister(self.id));
    }
}

/// The one thread a `NetWorkerHandle` (and every `Session` that holds one)
/// shares. Blocks on the control channel while it owns zero connections —
/// so an idle host lobby (`S3`, before the first "Add connection") costs no
/// CPU — and exits the instant that channel disconnects, which happens
/// exactly when every `NetWorkerHandle`/`Connection` clone for this
/// `Session` has dropped: no explicit shutdown call anywhere, no
/// `JoinHandle` for anyone to hold or join.
fn worker_loop(control_rx: mpsc::Receiver<Control>) {
    let mut conns: HashMap<ConnId, ConnState> = HashMap::new();
    let mut buf = [0u8; 65536];
    loop {
        if conns.is_empty() {
            match control_rx.recv() {
                Ok(msg) => apply_control(msg, &mut conns),
                Err(_) => return, // every handle for this Session is gone — nothing left to ever service
            }
            continue;
        }
        while let Ok(msg) = control_rx.try_recv() {
            apply_control(msg, &mut conns);
        }
        // One send/retransmit/recv pass per registered connection, per
        // outer iteration — round-robin, `implementation.md` §15.5. No one
        // connection's silence can stall another's turn (or the control
        // channel's own next drain) by more than RECV_POLL_TIMEOUT.
        let ids: Vec<ConnId> = conns.keys().copied().collect();
        for id in ids {
            if let Some(state) = conns.get_mut(&id) {
                service_one(id, state, &mut buf);
            }
        }
    }
}

fn apply_control(msg: Control, conns: &mut HashMap<ConnId, ConnState>) {
    match msg {
        Control::Register {
            id,
            socket,
            out_rx,
            event_tx,
            last_activity,
            max_decoded_bytes,
        } => {
            conns.insert(
                id,
                ConnState {
                    socket,
                    out_rx,
                    event_tx,
                    last_activity,
                    sender: ReliableSender::new(),
                    receiver: ReliableReceiver::new(),
                    best_effort: BestEffortReceiver::default(),
                    best_effort_next_seq: 0,
                    max_decoded_bytes,
                    best_effort_sent: 0,
                    best_effort_recv: 0,
                    net_debug_logged_at: Instant::now(),
                },
            );
        }
        Control::Deregister(id) => {
            conns.remove(&id);
        }
    }
}

/// One round-robin pass over a single connection: drain everything queued
/// to send, resend anything reliable gone unacked too long, then receive
/// once, bounded by `RECV_POLL_TIMEOUT` so no connection's silence can
/// stall another's turn by more than that. A socket error other than
/// would-block/timeout doesn't tear down anything by itself — that would
/// take every other connection this thread owns down with it — it just
/// leaves this entry inert (no more events, `last_activity` stops
/// advancing) until a `Deregister` removes it, matching `main.rs`'s own
/// `check_timeouts`.
fn service_one(id: ConnId, state: &mut ConnState, buf: &mut [u8]) {
    // 1. Drain everything currently queued to send.
    while let Ok((reliability, msg)) = state.out_rx.try_recv() {
        let now = Instant::now();
        let bytes = match reliability {
            Reliability::Reliable => state.sender.send(&msg, now),
            Reliability::BestEffort => {
                let seq = state.best_effort_next_seq;
                state.best_effort_next_seq += 1;
                state.best_effort_sent += 1;
                encode_packet(TAG_BEST_EFFORT, seq, &encode_message(&msg))
            }
        };
        let _ = state.socket.send(&bytes); // a dropped send is just a lost packet — reliable side self-heals via retransmit
    }

    // 2. Resend anything reliable that's gone unacked too long.
    for bytes in state.sender.due_retransmits(Instant::now()) {
        let _ = state.socket.send(&bytes);
    }

    // 3. Receive, bounded by this socket's own RECV_POLL_TIMEOUT — never a
    // blocking read past it, so every other connection this thread owns
    // waits at most that long behind this one's turn.
    match state.socket.recv(buf) {
        Ok(n) => {
            *state
                .last_activity
                .lock()
                .expect("poisoned only on a panic in this same thread") = Some(Instant::now());
            if let Some((tag, seq, payload)) = decode_packet(&buf[..n]) {
                match tag {
                    TAG_ACK => state.sender.on_ack(seq),
                    TAG_RELIABLE => {
                        if let Ok(msg) = decode_message(payload, state.max_decoded_bytes) {
                            let (ack_seq, delivered) = state.receiver.on_packet(seq, msg);
                            // `None` — outside MAX_REORDER_WINDOW — means
                            // deliberately not acked (`on_packet`'s own
                            // doc comment): sending no ack lets the
                            // sender's retransmit refill the gap later.
                            if let Some(ack_seq) = ack_seq {
                                let ack = encode_packet(TAG_ACK, ack_seq, &[]);
                                let _ = state.socket.send(&ack);
                            }
                            for m in delivered {
                                if state.event_tx.send(m).is_err() {
                                    return; // Connection dropped from the other side — a Deregister for this id is already on its way
                                }
                            }
                        } // an undecodable payload is simply dropped — the sender's own retransmit will resend it verbatim
                    }
                    TAG_BEST_EFFORT => {
                        state.best_effort_recv += 1;
                        if let Ok(msg) = decode_message(payload, state.max_decoded_bytes) {
                            if let Some(m) = state.best_effort.on_packet(seq, msg) {
                                if state.event_tx.send(m).is_err() {
                                    return;
                                }
                            }
                        }
                    }
                    _ => {} // unrecognized tag — drop
                }
            }
        }
        Err(e) if e.kind() == io::ErrorKind::WouldBlock || e.kind() == io::ErrorKind::TimedOut => {}
        // Socket genuinely broken — leave it registered; a Deregister, not
        // this pass, is what removes it. Unlike every other path above,
        // this error returns immediately rather than blocking for
        // RECV_POLL_TIMEOUT (e.g. ICMP port-unreachable on a connected UDP
        // socket right after the peer's process dies) — sleep that off so
        // this connection can't spin the round-robin at full CPU while
        // `check_timeouts` catches up.
        Err(_) => std::thread::sleep(RECV_POLL_TIMEOUT),
    }

    net_debug_tick(id, state);
}

/// Diagnostic-only: with `TETRIS_NET_DEBUG` set in the environment, prints
/// each connection's best-effort send/receive counts to stderr every 5s.
/// `State` (the minigrid payload) is sent best-effort — no ack, no
/// retransmit — so a one-way network fault silently drops it forever
/// while the reliable handshake still gets through; the visible symptoms
/// are a peer's minigrid staying blank and, eventually, a spurious
/// win-by-disconnect. `sent > 0` with `recv` never advancing on the other
/// end pins the fault to the network path, not the game logic.
fn net_debug_tick(id: ConnId, state: &mut ConnState) {
    use std::sync::OnceLock;
    static ENABLED: OnceLock<bool> = OnceLock::new();
    if !*ENABLED.get_or_init(|| std::env::var_os("TETRIS_NET_DEBUG").is_some()) {
        return;
    }
    let now = Instant::now();
    if now.duration_since(state.net_debug_logged_at) < Duration::from_secs(5) {
        return;
    }
    state.net_debug_logged_at = now;
    let last_activity = match *state
        .last_activity
        .lock()
        .expect("poisoned only on a panic in this same thread")
    {
        Some(t) => format!("{:.1}s ago", t.elapsed().as_secs_f64()),
        None => "never".to_string(),
    };
    eprintln!(
        "[net conn={id}] best-effort sent={} recv={} last_activity={last_activity}",
        state.best_effort_sent, state.best_effort_recv,
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Hardening regression: a `seq` far beyond `MAX_REORDER_WINDOW` must be
    /// neither buffered (unbounded memory growth from a peer that never
    /// sends the filling packet) nor acked (acking it would tell the
    /// sender's `ReliableSender` to stop retransmitting something this
    /// receiver didn't actually keep). Pinned to `MAX_REORDER_WINDOW` and
    /// `ReliableReceiver::pending`, both private — kept beside the code
    /// they test rather than in the external `net_unit_test.rs` suite.
    #[test]
    fn reliable_receiver_drops_and_does_not_ack_far_future_seq() {
        let mut r = ReliableReceiver::new();
        let (ack, delivered) =
            r.on_packet(MAX_REORDER_WINDOW, WireMessage::Untagged(Payload::Ping));
        assert_eq!(ack, None, "outside the window — not acked");
        assert!(delivered.is_empty());
        assert!(r.pending.is_empty(), "not buffered either");

        // A subsequent, legitimately in-window packet still works normally.
        let (ack0, d0) = r.on_packet(0, WireMessage::Untagged(Payload::Ping));
        assert_eq!(ack0, Some(0));
        assert_eq!(d0, vec![WireMessage::Untagged(Payload::Ping)]);
    }

    /// Pinned to the private `RETRANSMIT_INTERVAL` tuning constant.
    #[test]
    fn reliable_sender_tracks_and_clears_unacked() {
        let mut s = ReliableSender::new();
        let now = Instant::now();
        let bytes0 = s.send(&WireMessage::Untagged(Payload::Hello { nonce: 1 }), now);
        let (tag, seq, _) = decode_packet(&bytes0).unwrap();
        assert_eq!((tag, seq), (TAG_RELIABLE, 0));
        assert!(s.due_retransmits(now).is_empty(), "not due yet — just sent");

        s.on_ack(0);
        assert!(
            s.due_retransmits(now + RETRANSMIT_INTERVAL * 2).is_empty(),
            "acked — nothing left to retransmit"
        );
    }

    /// Hardening regression: an unresponsive peer that never acks anything
    /// must not grow `unacked` without bound. Pinned to the private
    /// `MAX_UNACKED_MESSAGES` cap and `ReliableSender::unacked` field.
    #[test]
    fn reliable_sender_unacked_is_capped() {
        let mut s = ReliableSender::new();
        let now = Instant::now();
        for _ in 0..(MAX_UNACKED_MESSAGES + 1) {
            s.send(&WireMessage::Untagged(Payload::Ping), now);
        }
        assert_eq!(s.unacked.len(), MAX_UNACKED_MESSAGES);
    }

    /// Pinned to the private `RETRANSMIT_INTERVAL` tuning constant.
    #[test]
    fn reliable_sender_retransmits_only_once_interval_elapsed() {
        let mut s = ReliableSender::new();
        let t0 = Instant::now();
        let sent = s.send(&WireMessage::Untagged(Payload::Ping), t0);

        assert!(
            s.due_retransmits(t0 + Duration::from_millis(10)).is_empty(),
            "well under the interval"
        );

        let due = s.due_retransmits(t0 + RETRANSMIT_INTERVAL + Duration::from_millis(1));
        assert_eq!(
            due,
            vec![sent],
            "past the interval — resend the exact original bytes (same seq)"
        );

        // Immediately due again should now be empty (retransmit resets the clock).
        assert!(s
            .due_retransmits(t0 + RETRANSMIT_INTERVAL + Duration::from_millis(2))
            .is_empty());
    }
}
