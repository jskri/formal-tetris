//! spec: tests/oracle.rs — §9, `implementation.md`.
//!
//! A from-scratch reimplementation of `hold`/`swapped` and `HoldPiece`'s
//! field-update, independent of `t3::model`'s `hold_piece` under test.
//! Hand-rolls the update rather than calling `t1::model::new_piece_state`,
//! so a bug shared between the translation and a reused helper would still
//! surface as a mismatch here (t2's oracle takes the same approach with its
//! saturating-add helper).
//!
//! R-TestScope: the `s2` half of every step is not re-verified here — `t2`'s
//! and `t1`'s own oracles already check it exhaustively, one layer down.
//! R-HoldOrdering: the old current piece is read before a hold mutates it,
//! mirroring what `t3::model::Machine::hold_piece` itself must do.

#[path = "test_instance.rs"]
mod fixture;

use fixture::{Prng, TestInstance};
use t1::model::Params;
use t3::instance::Tetris;
use t3::model::Machine;

// ── Independent hold/swap bookkeeping (spec: HoldPiece, UnchangedT3Part) ──

struct RocqState3<Piece> {
    hold: Option<Piece>,
    swapped: bool,
}

fn rocq_init3<Piece>() -> RocqState3<Piece> {
    RocqState3 {
        hold: None,
        swapped: false,
    }
}

/// spec: `T1.NewPieceState p2 (s1 s2_)`, hand-rolled independently of
/// `t1::model::new_piece_state` — returns the four fields it would set.
fn rocq_new_piece_state<P: Params>(p2: P::Piece) -> (P::Piece, i64, i64, u8) {
    (p2, P::initial_y(p2), P::initial_x(p2), 0)
}

/// spec: `HoldPiece`'s `hold`/`swapped` field-update (R-HoldOrdering: `old_p`
/// must be read before mutation, §4-T3e). `_s` is unused — both fields are
/// written unconditionally once the guard holds — kept as a parameter only
/// so the call site reads as "transition from state s".
fn rocq_hold3<Piece>(_s: &RocqState3<Piece>, old_p: Piece) -> RocqState3<Piece> {
    RocqState3 {
        hold: Some(old_p), // req-hold
        swapped: true,     // req-hold-limit
    }
}

fn equivalent3<P: Params>(m: &Machine<P>, s: &RocqState3<P::Piece>) -> bool {
    m.hold == s.hold && m.swapped == s.swapped
}

// ── Random-trace differential check ───────────────────────────────────────

fn run_differential<P: Params>(seed: u64, steps: usize) {
    let mut rng = Prng::new(seed);
    let pieces = P::piece_all();
    let start = rng.choose(pieces);

    let mut m = Machine::<P>::new(start, || rng.choose(pieces));
    let mut s = rocq_init3::<P::Piece>();
    assert!(equivalent3(&m, &s), "diverged at Init");

    for step in 1..=steps {
        let cmd = rng.next_below(8) as u8;
        let piece = rng.choose(pieces);

        match cmd {
            0 => {
                m.move_piece(0, -1);
                s = RocqState3 {
                    hold: s.hold,
                    swapped: s.swapped,
                }; // UnchangedT3Part
            }
            1 => {
                m.move_piece(0, 1);
                s = RocqState3 {
                    hold: s.hold,
                    swapped: s.swapped,
                };
            }
            2 => {
                m.move_piece(-1, 0);
                s = RocqState3 {
                    hold: s.hold,
                    swapped: s.swapped,
                };
            }
            3 => {
                m.rotate_piece(true);
                s = RocqState3 {
                    hold: s.hold,
                    swapped: s.swapped,
                };
            }
            4 => {
                m.rotate_piece(false);
                s = RocqState3 {
                    hold: s.hold,
                    swapped: s.swapped,
                };
            }
            5 => {
                if m.fix_piece(piece) {
                    s = RocqState3 {
                        hold: s.hold,
                        swapped: false,
                    }; // req-hold-limit
                }
            }
            6 => {
                // spec: FallStep — branch observed directly from move_piece's return value.
                if !m.move_piece(-1, 0)
                    && m.fix_piece(piece) {
                        s = RocqState3 {
                            hold: s.hold,
                            swapped: false,
                        };
                    }
            }
            _ => {
                let guard_holds = !m.s2.s1.gameover && !m.swapped;
                if guard_holds {
                    let old_p = m.s2.s1.p; // R-HoldOrdering: read before mutation
                    let (expected_p, expected_py, expected_px, expected_pr) =
                        rocq_new_piece_state::<P>(s.hold.unwrap_or(piece));
                    let fired = m.hold_piece(piece);
                    assert!(
                        fired,
                        "guard predicted to hold but hold_piece returned false at step {step}"
                    );
                    assert_eq!(
                        m.s2.s1.p, expected_p,
                        "p mismatch after hold at step {step}"
                    );
                    assert_eq!(
                        m.s2.s1.py, expected_py,
                        "py mismatch after hold at step {step}"
                    );
                    assert_eq!(
                        m.s2.s1.px, expected_px,
                        "px mismatch after hold at step {step}"
                    );
                    assert_eq!(
                        m.s2.s1.pr, expected_pr,
                        "pr mismatch after hold at step {step}"
                    );
                    s = rocq_hold3(&s, old_p);
                } else {
                    let fired = m.hold_piece(piece);
                    assert!(
                        !fired,
                        "guard predicted to fail but hold_piece returned true at step {step}"
                    );
                    // s unchanged (stutter)
                }
            }
        }
        assert!(equivalent3(&m, &s), "hold/swapped diverged at step {step}");
    }
}

#[test]
fn oracle_matches_random_trace_on_test_instance() {
    run_differential::<TestInstance>(0x0ff1_ce0d_d1ce_5eed, 5_000);
}

#[test]
fn oracle_matches_random_trace_on_real_instance() {
    run_differential::<Tetris>(0xfeed_face_f00d_cafe, 1_000);
}
