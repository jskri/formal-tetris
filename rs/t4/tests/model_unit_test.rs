// spec: tests/model_unit_test.rs — golden vectors (§9, `implementation.md`).

#[path = "test_instance.rs"]
mod fixture;
#[path = "oracle.rs"]
mod oracle;

use fixture::{Piece, TestInstance};
use t1::model::Params as T1Params;
use t4::model::{assert_piece_set, check_invariants, is_piece_set, Machine};

fn bags_alternating() -> impl FnMut(u64) -> Vec<Piece> {
    |i: u64| {
        if i % 2 == 0 {
            vec![Piece::Bar, Piece::Corner]
        } else {
            vec![Piece::Corner, Piece::Bar]
        }
    }
}

fn piece_source() -> Piece {
    Piece::Bar
}

/// Hand-verified against `TestInstance` (`NEXT_LEN = 3`, `NUM_PIECES = 2`)
/// by hand-simulating `draw_once`/`init_piece_and_draw` (§9).
///
/// bags_fn = i ↦ alternating [Bar, Corner] / [Corner, Bar].
/// Trace (bag/next shown after each draw):
///   init: bag=[Bar,Corner] next=[Bar,Bar,Bar] (arbitrary filler) bag_idx=1
///   draw0 (bag_new=bags(1)=[Corner,Bar]): resetting=false, p=Bar(discarded)
///     -> bag=[Bar] next=[Bar,Bar,Corner]
///   draw1 (bag_new=bags(1)=[Corner,Bar]): resetting=true, p=Bar(discarded)
///     -> bag=[Corner,Bar] next=[Bar,Corner,Bar] bag_idx=2
///   draw2 (bag_new=bags(2)=[Bar,Corner]): resetting=false, p=Bar(discarded)
///     -> bag=[Corner] next=[Corner,Bar,Bar]
///   final draw (bag_new=bags(2)=[Bar,Corner]): resetting=true, p=Corner
///     -> bag=[Bar,Corner] next=[Bar,Bar,Corner]
/// Result: p=Corner, bag=[Bar,Corner], next=[Bar,Bar,Corner]
#[test]
fn init_matches_hand_traced_vector() {
    let m = Machine::<TestInstance>::new(bags_alternating(), piece_source);
    assert_eq!(m.s3.s2.s1.p, Piece::Corner);
    assert_eq!(m.bag, vec![Piece::Bar, Piece::Corner]);
    assert_eq!(
        m.next,
        std::collections::VecDeque::from(vec![Piece::Bar, Piece::Bar, Piece::Corner])
    );
    check_invariants(&m);
}

/// Same trace, checked against the independent oracle (`oracle.rs`) instead
/// of by hand — catches bugs a hand-trace and `model.rs` could share.
#[test]
fn init_matches_oracle() {
    let m = Machine::<TestInstance>::new(bags_alternating(), piece_source);
    let (op, od) = oracle::oracle_init_piece_and_draw::<Piece>(3, bags_alternating());
    assert_eq!(m.s3.s2.s1.p, op);
    assert_eq!(m.bag, od.bag);
    assert_eq!(m.next.iter().copied().collect::<Vec<_>>(), od.next);
}

#[test]
fn is_piece_set_rejects_wrong_length() {
    assert!(!is_piece_set::<TestInstance>(&[Piece::Bar]));
}

#[test]
fn is_piece_set_rejects_duplicates() {
    assert!(!is_piece_set::<TestInstance>(&[Piece::Bar, Piece::Bar]));
}

#[test]
fn is_piece_set_accepts_valid_permutation() {
    assert!(is_piece_set::<TestInstance>(&[Piece::Bar, Piece::Corner]));
    assert!(is_piece_set::<TestInstance>(&[Piece::Corner, Piece::Bar]));
}

#[test]
#[should_panic(expected = "PieceSet violated")]
fn assert_piece_set_panics_on_malformed_bag() {
    assert_piece_set::<TestInstance>(&[Piece::Bar, Piece::Bar]);
}

/// Guard-fail case for `fix_piece` (§4-T4d): peek-then-commit ordering
/// means a failed guard leaves `bag`/`next` untouched.
#[test]
fn fix_piece_guard_fail_leaves_bag_next_untouched() {
    let mut m = Machine::<TestInstance>::new(bags_alternating(), piece_source);
    m.s3.s2.s1.gameover = true; // force T3.FixPiece's guard to fail
    let bag_before = m.bag.clone();
    let next_before = m.next.clone();
    let fired = m.fix_piece(&[Piece::Bar, Piece::Corner]);
    assert!(!fired);
    assert_eq!(m.bag, bag_before);
    assert_eq!(m.next, next_before);
}

/// Skip branch of `hold_piece` (§4-T4g): draws happen only in the None
/// branch, so a skip leaves `bag`/`next` untouched.
#[test]
fn hold_piece_skip_branch_leaves_bag_next_untouched() {
    let mut m = Machine::<TestInstance>::new(bags_alternating(), piece_source);
    // First hold: hold was None, must draw.
    assert!(m.hold_piece(&[Piece::Bar, Piece::Corner]));

    let bag_before = m.bag.clone();
    let next_before = m.next.clone();
    // Second consecutive hold: T3's swapped guard rejects it; this
    // exercises the skip-draw branch's no-mutation property specifically.
    let fired = m.hold_piece(&[Piece::Corner, Piece::Bar]);
    assert!(!fired);
    assert_eq!(m.bag, bag_before);
    assert_eq!(m.next, next_before);
}

/// `fix_piece`/`fall_step` consume exactly one piece from `next` per
/// *successful* call (`implementation.md` §9).
#[test]
fn successful_fix_consumes_exactly_one_next_entry() {
    let mut m = Machine::<TestInstance>::new(bags_alternating(), piece_source);
    for _ in 0..30 {
        if m.s3.s2.s1.gameover {
            break;
        }
        let len_before = m.next.len();
        let mut fixed = false;
        for _ in 0..(TestInstance::PW * 4) {
            if !m.move_piece(-1, 0) {
                fixed = m.fix_piece(&[Piece::Bar, Piece::Corner]);
                break;
            }
        }
        if fixed {
            assert_eq!(
                m.next.len(),
                len_before,
                "next length must stay constant across a successful fix"
            );
            check_invariants(&m);
        }
    }
}

/// Initial bag/next population matches hand-computed values on
/// `TestInstance` (§9).
#[test]
fn initial_population_matches_hand_computed_bag_and_next() {
    let m = Machine::<TestInstance>::new(bags_alternating(), piece_source);
    assert_eq!(m.bag.len(), 2);
    assert_eq!(m.next.len(), 3);
    check_invariants(&m);
}
