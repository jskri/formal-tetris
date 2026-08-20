//! spec: tests/net_unit_test.rs — `net.rs`'s transport mechanism (§9,
//! `implementation.md`): STUN, the wire codec, packet framing, the pure
//! delivery state machines, and a real loopback-socket exercise of
//! `NetWorkerHandle`/`Connection`.
//!
//! Hardening tests pinned to `net.rs`-private tuning constants (the reorder
//! window, the unacked-message cap) and to `ReliableSender`/
//! `ReliableReceiver`'s own private buffer fields stay in `net.rs`'s own
//! `#[cfg(test)] mod tests` instead of here — an implementation detail the
//! public API has no reason to expose.

use std::io::Write as _;
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4, UdpSocket};
use std::time::Duration;
use t1::model::Params;
use t7::net::{
    self, b32_decode, b32_encode, code_to_piece, decode_message, decode_packet, encode_message,
    encode_packet, piece_to_code, recommended_max_decoded_bytes, BestEffortReceiver,
    ConnectionCode, Destination, GridCell, Message, NetWorkerHandle, Payload, PieceCode,
    Reliability, ReliableReceiver, WireMessage, B32_ALPHABET, MIN_DECODED_MESSAGE_BYTES,
    TAG_RELIABLE,
};

fn hex_decode(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// A realistic decode-size bound: the board dimensions
/// `t7::session::max_decoded_message_bytes` would compute for the one
/// instance this crate ships.
fn test_max_decoded_bytes() -> u64 {
    let mg = <t7::instance::Tetris as Params>::initial_main_grid();
    recommended_max_decoded_bytes(mg.len(), mg.first().map_or(0, |r| r.len()))
}

fn sample_code() -> ConnectionCode {
    ConnectionCode {
        public: SocketAddrV4::new(Ipv4Addr::new(203, 0, 113, 7), 54321),
        local: SocketAddrV4::new(Ipv4Addr::new(192, 168, 1, 42), 41234),
        nonce: 0x0123_4567_89AB_CDEF,
    }
}

fn loopback_pair() -> (UdpSocket, SocketAddr, UdpSocket, SocketAddr) {
    let a = UdpSocket::bind("127.0.0.1:0").expect("bind a");
    let b = UdpSocket::bind("127.0.0.1:0").expect("bind b");
    let addr_a = a.local_addr().unwrap();
    let addr_b = b.local_addr().unwrap();
    (a, addr_a, b, addr_b)
}

// ── stun ──────────────────────────────────────────────────────────────

#[test]
fn stun_build_request_has_correct_header() {
    let txid = [1u8; 12];
    let req = net::stun::build_binding_request(txid);
    assert_eq!(req.len(), 20);
    assert_eq!(&req[0..2], &[0x00, 0x01]); // Binding Request
    assert_eq!(&req[2..4], &[0x00, 0x00]); // no attributes
    assert_eq!(&req[4..8], &[0x21, 0x12, 0xA4, 0x42]); // magic cookie
    assert_eq!(&req[8..20], &txid);
}

/// A real Binding Success Response captured from a live round trip against
/// `stun.l.google.com:19302`, so this parser is checked against a real
/// server's own wire format, not only against bytes this module produced.
#[test]
fn stun_parse_response_matches_real_captured_packet() {
    let txid: [u8; 12] = [
        0x0e, 0xfb, 0xb3, 0x81, 0x04, 0x6e, 0x08, 0xf1, 0x95, 0x3a, 0xae, 0x1f,
    ];
    let data = hex_decode("0101000c2112a4420efbb381046e08f1953aae1f002000080001cafc919cfa0f");
    let addr = net::stun::parse_binding_response(&data, &txid)
        .expect("must parse a real Binding Success Response");
    assert_eq!(
        addr,
        SocketAddr::new(Ipv4Addr::new(176, 142, 94, 77).into(), 60398)
    );
}

/// Same captured packet as above, matched against a *different* expected
/// transaction ID: a response to somebody else's request, or a spoof, must
/// not be accepted as this request's own answer.
#[test]
fn stun_parse_rejects_wrong_transaction_id() {
    let wrong_txid = [0u8; 12];
    let data = hex_decode("0101000c2112a4420efbb381046e08f1953aae1f002000080001cafc919cfa0f");
    assert!(net::stun::parse_binding_response(&data, &wrong_txid).is_none());
}

#[test]
fn stun_build_then_parse_round_trip_with_synthetic_response() {
    let txid = [7u8; 12];
    let req = net::stun::build_binding_request(txid);
    assert_eq!(&req[8..20], &txid);

    // Hand-build a synthetic response for a known address, mirroring
    // RFC 5389 §15.2's XOR construction, independent of
    // `parse_binding_response`'s own implementation.
    let want = SocketAddr::new(Ipv4Addr::new(203, 0, 113, 42).into(), 51820);
    let mut resp = Vec::new();
    resp.extend_from_slice(&0x0101u16.to_be_bytes());
    resp.extend_from_slice(&12u16.to_be_bytes()); // one 8-byte attr + 4-byte header
    resp.extend_from_slice(&0x2112_A442u32.to_be_bytes());
    resp.extend_from_slice(&txid);
    resp.extend_from_slice(&0x0020u16.to_be_bytes());
    resp.extend_from_slice(&8u16.to_be_bytes());
    resp.push(0); // reserved
    resp.push(1); // family IPv4
    resp.extend_from_slice(&(51820u16 ^ 0x2112).to_be_bytes());
    let ip_bits = u32::from(Ipv4Addr::new(203, 0, 113, 42));
    resp.extend_from_slice(&(ip_bits ^ 0x2112_A442).to_be_bytes());

    assert_eq!(net::stun::parse_binding_response(&resp, &txid), Some(want));
}

#[test]
fn stun_parse_rejects_too_short() {
    assert_eq!(
        net::stun::parse_binding_response(&[0u8; 10], &[0u8; 12]),
        None
    );
}

/// Live round trip against a real public STUN server, exercising the actual
/// UDP send/receive path, not just wire-format parsing. `#[ignore]`d by
/// default since `cargo test` must not require network access; run with
/// `--ignored` to include it.
#[test]
#[ignore = "requires real internet access to a public STUN server"]
fn stun_query_live_google_server() {
    use std::net::ToSocketAddrs;
    let socket = UdpSocket::bind("0.0.0.0:0").expect("bind ephemeral local UDP socket");
    let server = "stun.l.google.com:19302"
        .to_socket_addrs()
        .expect("DNS resolve")
        .find(|a| a.is_ipv4())
        .expect("at least one IPv4 address for the STUN server");
    let addr = net::stun::query(&socket, server, Duration::from_secs(2), 3)
        .expect("STUN query against a real public server");
    assert!(!addr.ip().is_unspecified());
    assert_ne!(addr.port(), 0);
}

// ── connection code ──────────────────────────────────────────────────

#[test]
fn connection_code_round_trips_through_its_string_form() {
    let code = sample_code();
    let s = code.to_string();
    assert_eq!(s.parse::<ConnectionCode>(), Ok(code));
}

#[test]
fn connection_code_string_is_32_chars_plus_group_dashes() {
    let s = sample_code().to_string();
    assert_eq!(
        s.chars().filter(|c| *c != '-').count(),
        32,
        "20 bytes = exactly 32 base32 chars"
    );
    assert_eq!(s.matches('-').count(), 3, "grouped in 8s");
}

/// Crockford's confusables and the cosmetic grouping must all survive a
/// retype: lowercase, `I`/`l` for `1`, `O` for `0`, dashes moved or dropped,
/// stray spaces.
#[test]
fn connection_code_parse_is_forgiving_about_retyping() {
    let code = sample_code();
    let canonical: String = code.to_string().chars().filter(|c| *c != '-').collect();
    assert_eq!(canonical.parse::<ConnectionCode>(), Ok(code), "no dashes");
    assert_eq!(
        canonical.to_lowercase().parse::<ConnectionCode>(),
        Ok(code),
        "lowercase"
    );

    let spaced = format!("{} {}", &canonical[..16], &canonical[16..]);
    assert_eq!(
        spaced.parse::<ConnectionCode>(),
        Ok(code),
        "whitespace ignored"
    );

    let confused: String = canonical
        .chars()
        .map(|c| match c {
            '1' => 'I', // Crockford: I reads as 1
            '0' => 'O', // Crockford: O reads as 0
            other => other,
        })
        .collect();
    assert_eq!(
        confused.parse::<ConnectionCode>(),
        Ok(code),
        "I/O read back as 1/0"
    );
}

#[test]
fn connection_code_rejects_malformed() {
    assert!("".parse::<ConnectionCode>().is_err(), "empty");
    assert!("ABC".parse::<ConnectionCode>().is_err(), "too short");
    assert!(
        sample_code()
            .to_string()
            .repeat(2)
            .parse::<ConnectionCode>()
            .is_err(),
        "too long"
    );
    // 'U' is deliberately absent from Crockford's alphabet.
    let mut bad: String = sample_code()
        .to_string()
        .chars()
        .filter(|c| *c != '-')
        .collect();
    bad.replace_range(0..1, "U");
    assert!(
        bad.parse::<ConnectionCode>().is_err(),
        "character outside the alphabet"
    );
}

/// The same-NAT hairpin case `best_target` exists for: a peer whose public
/// IP matches ours is reached on its LAN address, anyone else on their
/// public one.
#[test]
fn best_target_prefers_local_address_behind_a_shared_nat() {
    let peer = sample_code();
    let same_nat = SocketAddrV4::new(Ipv4Addr::new(203, 0, 113, 7), 9999);
    assert_eq!(peer.best_target(same_nat), peer.local);

    let elsewhere = SocketAddrV4::new(Ipv4Addr::new(198, 51, 100, 3), 9999);
    assert_eq!(peer.best_target(elsewhere), peer.public);
}

// ── base32 ────────────────────────────────────────────────────────────

#[test]
fn b32_encode_matches_known_vectors() {
    assert_eq!(b32_encode(&[]), "");
    assert_eq!(b32_encode(&[0x00]), "00");
    assert_eq!(b32_encode(&[0xFF]), "ZW");
    assert_eq!(b32_encode(&[0x01]), "04");
    assert_eq!(b32_encode(&[0xDE, 0xAD, 0xBE, 0xEF]), "VTPVXVR");
    assert_eq!(b32_encode(b"Hi!"), "91MJ2");
}

/// A length that's an exact multiple of 5 bytes (40 bits) drains to
/// `bits == 0` after the last byte, so the trailing partial-group branch
/// never fires — every character comes from the main loop alone.
#[test]
fn b32_encode_exact_multiple_of_five_bytes_has_no_padding() {
    assert_eq!(b32_encode(&[0, 0, 0, 0, 0]), "00000000");
    assert_eq!(
        b32_encode(&[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        "0000000000000000"
    );
}

/// 20 bytes of payload — a `ConnectionCode`'s own size — encode to exactly
/// 32 characters with no padding, per `b32_encode`'s own doc comment.
#[test]
fn b32_encode_twenty_bytes_is_exactly_thirty_two_chars() {
    assert_eq!(b32_encode(&[0u8; 20]).len(), 32);
}

/// Output length is `ceil(8 * bytes.len() / 5)` characters for every input
/// length, and every character comes from `B32_ALPHABET` — in particular
/// never the visually-confusable `I`/`L`/`O`/`U` this alphabet exists to
/// avoid.
#[test]
fn b32_encode_length_and_charset_hold_for_every_length() {
    for len in 0..40usize {
        let bytes = vec![0xA5u8; len]; // an arbitrary fixed non-zero byte pattern
        let encoded = b32_encode(&bytes);
        assert_eq!(encoded.len(), (len * 8).div_ceil(5), "len {len}");
        assert!(
            encoded.chars().all(|c| B32_ALPHABET.contains(&(c as u8))),
            "len {len}: {encoded:?} contains a character outside B32_ALPHABET"
        );
        assert!(
            !encoded.contains(['I', 'L', 'O', 'U']),
            "len {len}: {encoded:?} contains a confusable character"
        );
    }
}

#[test]
fn b32_round_trips_arbitrary_bytes() {
    for len in 0..40usize {
        let bytes: Vec<u8> = (0..len)
            .map(|i| (i as u8).wrapping_mul(37).wrapping_add(11))
            .collect();
        let decoded = b32_decode(&b32_encode(&bytes)).expect("own output always decodes");
        // Encoding pads the final partial group with zero bits, so the
        // decode can yield the same bytes plus at most one zero byte of
        // padding — the prefix is what must match.
        assert_eq!(&decoded[..len], &bytes[..], "len {len}");
    }
}

// ── piece code / grid cell ───────────────────────────────────────────

#[test]
fn piece_code_round_trips_every_piece() {
    for &p in <t7::instance::Tetris as Params>::piece_all() {
        assert_eq!(code_to_piece(piece_to_code(p)), Some(p));
    }
}

#[test]
fn code_to_piece_rejects_out_of_range() {
    let n = <t7::instance::Tetris as Params>::piece_all().len();
    assert_eq!(code_to_piece(n as PieceCode), None);
    assert_eq!(code_to_piece(PieceCode::MAX), None);
}

#[test]
fn grid_cell_round_trips_both_variants() {
    use t1::model::PieceOrExtra;
    type Cell = PieceOrExtra<t7::instance::Tetris>;

    let garbage: Cell = PieceOrExtra::Extra(t7::model::Garbage);
    assert_eq!(Cell::try_from(GridCell::from(garbage)), Ok(garbage));

    for &p in <t7::instance::Tetris as Params>::piece_all() {
        let cell: Cell = PieceOrExtra::Piece(p);
        assert_eq!(Cell::try_from(GridCell::from(cell)), Ok(cell));
    }
}

#[test]
fn grid_cell_conversion_rejects_out_of_range_code() {
    use t1::model::PieceOrExtra;
    let n = <t7::instance::Tetris as Params>::piece_all().len();
    assert!(
        PieceOrExtra::<t7::instance::Tetris>::try_from(GridCell::Piece(n as PieceCode)).is_err()
    );
}

// ── wire format ───────────────────────────────────────────────────────

#[test]
fn message_round_trips_every_variant() {
    let wire_cases = vec![
        WireMessage::Untagged(Payload::Join { name: "Ada".into() }),
        WireMessage::Untagged(Payload::Players {
            roster: vec!["Ada".into(), "Grace".into()],
        }),
        WireMessage::Untagged(Payload::Start {
            player_count: 3,
            my_index: 1,
            match_gen: 7,
        }),
        WireMessage::Untagged(Payload::Leave),
        WireMessage::Untagged(Payload::Hello { nonce: 0xDEAD_BEEF }),
        WireMessage::Untagged(Payload::HelloAck { nonce: 0xDEAD_BEEF }),
        WireMessage::Untagged(Payload::Ping),
        WireMessage::Routed(Message {
            from: 1,
            to: Destination::Single(2),
            match_gen: 7,
            body: Payload::Garbage { amount: 4 },
        }),
        WireMessage::Routed(Message {
            from: 1,
            to: Destination::Broadcast,
            match_gen: 7,
            body: Payload::Gameover,
        }),
        WireMessage::Routed(Message {
            from: 1,
            to: Destination::Broadcast,
            match_gen: 7,
            body: Payload::Disconnect,
        }),
        WireMessage::Routed(Message {
            from: 1,
            to: Destination::Broadcast,
            match_gen: 7,
            body: Payload::State {
                p: piece_to_code(t1::instance::Piece::T),
                py: 3,
                px: 1,
                pr: 2,
                mg: vec![vec![
                    None,
                    Some(GridCell::Garbage),
                    Some(GridCell::Piece(piece_to_code(t1::instance::Piece::I))),
                ]],
                gameover: false,
            },
        }),
    ];
    for msg in wire_cases {
        let bytes = encode_message(&msg);
        let decoded =
            decode_message(&bytes, test_max_decoded_bytes()).expect("round trip must decode");
        assert_eq!(decoded, msg);
    }
}

#[test]
fn decode_rejects_garbage_bytes() {
    assert!(decode_message(&[1, 2, 3, 4, 5], test_max_decoded_bytes()).is_err());
}

/// spec: §15.2 hardening — `decode_message` bounds decompression against
/// the connection's decode-size cap: a payload fitting one UDP packet but
/// inflating well past that cap must fail cleanly, not allocate unbounded.
#[test]
fn decode_message_rejects_a_zip_bomb_sized_payload() {
    let bound = test_max_decoded_bytes();
    let huge = vec![0u8; (bound * 4) as usize];
    let mut enc = flate2::write::DeflateEncoder::new(Vec::new(), flate2::Compression::best());
    enc.write_all(&huge)
        .expect("in-memory Vec write never fails");
    let compressed = enc.finish().expect("in-memory Vec write never fails");
    assert!(
        compressed.len() < 65536,
        "sanity: fits in a single real UDP packet despite decompressing to 4x the cap"
    );
    assert!(
        decode_message(&compressed, bound).is_err(),
        "truncated at the cap, so it fails to parse as JSON"
    );
}

#[test]
fn recommended_max_decoded_bytes_grows_with_board_size() {
    assert!(recommended_max_decoded_bytes(40, 20) > recommended_max_decoded_bytes(20, 10));
}

#[test]
fn recommended_max_decoded_bytes_respects_the_floor() {
    assert_eq!(
        recommended_max_decoded_bytes(0, 0),
        MIN_DECODED_MESSAGE_BYTES
    );
}

#[test]
fn packet_framing_round_trips() {
    let payload = b"hello world";
    let bytes = encode_packet(TAG_RELIABLE, 42, payload);
    let (tag, seq, decoded_payload) = decode_packet(&bytes).unwrap();
    assert_eq!(tag, TAG_RELIABLE);
    assert_eq!(seq, 42);
    assert_eq!(decoded_payload, payload);
}

#[test]
fn packet_framing_rejects_too_short() {
    assert!(decode_packet(&[0u8; 3]).is_none());
}

// ── ReliableReceiver / BestEffortReceiver: pure state machine tests ────

#[test]
fn reliable_receiver_delivers_in_order_arrival() {
    let mut r = ReliableReceiver::new();
    let (ack0, d0) = r.on_packet(0, WireMessage::Untagged(Payload::Ping));
    assert_eq!(ack0, Some(0));
    assert_eq!(d0, vec![WireMessage::Untagged(Payload::Ping)]);
    let (ack1, d1) = r.on_packet(1, WireMessage::Untagged(Payload::Ping));
    assert_eq!(ack1, Some(1));
    assert_eq!(d1, vec![WireMessage::Untagged(Payload::Ping)]);
}

/// spec: §15.2 — reliable delivery buffers an out-of-order arrival and
/// delivers only once the gap is contiguous; seq 1 arrives before seq 0.
#[test]
fn reliable_receiver_buffers_out_of_order_then_delivers_contiguous() {
    let mut r = ReliableReceiver::new();
    let (ack1, d1) = r.on_packet(1, WireMessage::Untagged(Payload::Ping));
    assert_eq!(ack1, Some(1), "still acks the out-of-order packet itself");
    assert!(d1.is_empty(), "nothing deliverable yet — seq 0 is missing");

    let (ack0, d0) = r.on_packet(0, WireMessage::Untagged(Payload::Ping));
    assert_eq!(ack0, Some(0));
    assert_eq!(
        d0,
        vec![
            WireMessage::Untagged(Payload::Ping),
            WireMessage::Untagged(Payload::Ping)
        ],
        "both deliverable now, in seq order"
    );
}

#[test]
fn reliable_receiver_duplicate_delivery_is_a_noop() {
    let mut r = ReliableReceiver::new();
    r.on_packet(0, WireMessage::Untagged(Payload::Ping));
    let (ack, delivered) = r.on_packet(0, WireMessage::Untagged(Payload::Ping));
    assert_eq!(
        ack,
        Some(0),
        "still re-acks — the peer's own ack may have been lost"
    );
    assert!(
        delivered.is_empty(),
        "already delivered once — not delivered again"
    );
}

#[test]
fn reliable_receiver_handles_reordering_and_duplication_together() {
    let mut r = ReliableReceiver::new();
    let mut all_delivered = Vec::new();
    // 0, 2, 1, 1 (dup), 3 — out of order plus a duplicate.
    for seq in [0u64, 2, 1, 1, 3] {
        let msg = WireMessage::Routed(Message {
            from: 0,
            to: Destination::Broadcast,
            match_gen: 0,
            body: Payload::Garbage { amount: seq as i64 },
        });
        let (_, d) = r.on_packet(seq, msg);
        all_delivered.extend(d);
    }
    let amounts: Vec<i64> = all_delivered
        .iter()
        .map(|m| match m {
            WireMessage::Routed(Message {
                body: Payload::Garbage { amount },
                ..
            }) => *amount,
            _ => unreachable!(),
        })
        .collect();
    assert_eq!(
        amounts,
        vec![0, 1, 2, 3],
        "delivered exactly once each, in sequence order"
    );
}

#[test]
fn best_effort_receiver_drops_stale_and_duplicate_but_keeps_newer() {
    let mut b = BestEffortReceiver::default();
    assert!(b
        .on_packet(5, WireMessage::Untagged(Payload::Ping))
        .is_some());
    assert!(
        b.on_packet(3, WireMessage::Untagged(Payload::Ping))
            .is_none(),
        "older than last applied"
    );
    assert!(
        b.on_packet(5, WireMessage::Untagged(Payload::Ping))
            .is_none(),
        "duplicate of last applied"
    );
    assert!(
        b.on_packet(6, WireMessage::Untagged(Payload::Ping))
            .is_some(),
        "newer — applied"
    );
}

// ── Connection: end-to-end over real loopback sockets ──────────────────

/// Two real `Connection`s sharing one `NetWorkerHandle` over loopback (no
/// artificial loss) — exercises the happy-path glue (thread, channels,
/// socket wiring, round-robin scheduling) end to end; the *hard* logic
/// (retransmit-on-loss, reorder buffering, dedup) is exercised separately
/// above, against the pure state machines directly.
#[test]
fn connection_handshake_and_reliable_exchange_over_loopback() {
    let (sock_a, addr_a, sock_b, addr_b) = loopback_pair();
    let net = NetWorkerHandle::spawn();
    let conn_a = net
        .register(sock_a, addr_b, 111, test_max_decoded_bytes())
        .expect("register a");
    let conn_b = net
        .register(sock_b, addr_a, 222, test_max_decoded_bytes())
        .expect("register b");

    // Each side's own Hello, sent automatically by `spawn`, must reach the
    // other.
    let hello_at_b = conn_b
        .incoming
        .recv_timeout(Duration::from_secs(2))
        .expect("b receives a's Hello");
    assert_eq!(
        hello_at_b,
        WireMessage::Untagged(Payload::Hello { nonce: 111 })
    );
    let hello_at_a = conn_a
        .incoming
        .recv_timeout(Duration::from_secs(2))
        .expect("a receives b's Hello");
    assert_eq!(
        hello_at_a,
        WireMessage::Untagged(Payload::Hello { nonce: 222 })
    );

    // Application-level reply, exactly what a lobby's own dispatch would do
    // on observing a Hello.
    conn_b
        .outgoing
        .send((
            Reliability::Reliable,
            WireMessage::Untagged(Payload::HelloAck { nonce: 111 }),
        ))
        .unwrap();
    let ack_at_a = conn_a
        .incoming
        .recv_timeout(Duration::from_secs(2))
        .expect("a receives b's HelloAck");
    assert_eq!(
        ack_at_a,
        WireMessage::Untagged(Payload::HelloAck { nonce: 111 })
    );

    // A handful of further reliable messages, in order.
    for n in 0..5i64 {
        let msg = WireMessage::Routed(Message {
            from: 0,
            to: Destination::Broadcast,
            match_gen: 0,
            body: Payload::Garbage { amount: n },
        });
        conn_a.outgoing.send((Reliability::Reliable, msg)).unwrap();
    }
    let mut received = Vec::new();
    for _ in 0..5 {
        match conn_b
            .incoming
            .recv_timeout(Duration::from_secs(2))
            .expect("b receives a's Garbage messages")
        {
            WireMessage::Routed(Message {
                body: Payload::Garbage { amount },
                ..
            }) => received.push(amount),
            other => panic!("unexpected message: {other:?}"),
        }
    }
    assert_eq!(received, vec![0, 1, 2, 3, 4]);

    assert!(conn_a
        .seconds_since_last_activity()
        .is_some_and(|s| s < 2.0));
}

/// A connection that has received nothing at all must report `None` from
/// `seconds_since_last_activity`, not a large-but-finite elapsed time — so a
/// caller's timeout policy can tell "still arriving" apart from "arrived,
/// then stopped."
#[test]
fn connection_reports_no_activity_before_the_first_packet_arrives() {
    let (sock_a, _addr_a, _sock_b, addr_b) = loopback_pair();
    let net = NetWorkerHandle::spawn();
    // `sock_a` is registered but `_sock_b` is left unregistered and never
    // reads/replies — `conn_a`'s own automatic Hello (fired by `register()`)
    // targets `addr_b`, so `conn_a` itself never receives anything back.
    let conn_a = net
        .register(sock_a, addr_b, 111, test_max_decoded_bytes())
        .expect("register a");
    std::thread::sleep(Duration::from_millis(200));
    assert_eq!(
        conn_a.seconds_since_last_activity(),
        None,
        "no packet ever received — not merely a long time ago"
    );
}

#[test]
fn connection_best_effort_exchange_over_loopback() {
    let (sock_a, addr_a, sock_b, addr_b) = loopback_pair();
    let net = NetWorkerHandle::spawn();
    let conn_a = net
        .register(sock_a, addr_b, 1, test_max_decoded_bytes())
        .expect("register a");
    let conn_b = net
        .register(sock_b, addr_a, 2, test_max_decoded_bytes())
        .expect("register b");
    // Drain the automatic Hello handshake first so it doesn't get confused
    // with the State messages below.
    conn_a
        .incoming
        .recv_timeout(Duration::from_secs(2))
        .unwrap();
    conn_b
        .incoming
        .recv_timeout(Duration::from_secs(2))
        .unwrap();

    let state = |py: i64| {
        WireMessage::Routed(Message {
            from: 0,
            to: Destination::Broadcast,
            match_gen: 0,
            body: Payload::State {
                p: piece_to_code(t1::instance::Piece::O),
                py,
                px: 0,
                pr: 0,
                mg: vec![],
                gameover: false,
            },
        })
    };
    conn_a
        .outgoing
        .send((Reliability::BestEffort, state(1)))
        .unwrap();
    conn_a
        .outgoing
        .send((Reliability::BestEffort, state(2)))
        .unwrap();

    let mut last = None;
    for _ in 0..2 {
        if let Ok(WireMessage::Routed(Message {
            body: Payload::State { py, .. },
            ..
        })) = conn_b.incoming.recv_timeout(Duration::from_secs(2))
        {
            last = Some(py);
        }
    }
    assert_eq!(
        last,
        Some(2),
        "the most recent State observed is the last one sent"
    );
}
