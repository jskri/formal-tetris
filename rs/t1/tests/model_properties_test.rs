//! spec: tests/model_properties_test.rs — §9.2, `implementation.md`.

#[path = "test_instance.rs"]
mod fixture;

use fixture::{Piece as TPiece, TestInstance};
use proptest::prelude::*;
use t1::model::{self, Machine, Params, PieceOrExtra};

const HM: i64 = 6; // TestInstance's board dimensions (tests/test_instance.rs)
const WM: i64 = 5;
const B: i64 = 8; // max(HM,WM) + PW - 1 = max(6,5) + 3 - 1 (D10)

fn check_common_invariants(m: &Machine<TestInstance>) {
    // type_ok after every step
    assert!(model::type_ok(m), "type_ok violated: {:?}", m.mg);
    // mg stays HM×WM
    assert_eq!(m.mg.len() as i64, HM);
    for row in &m.mg {
        assert_eq!(row.len() as i64, WM);
    }
    // every integer field within ±B (D10)
    assert!(m.py.abs() <= B, "py={} out of ±{B}", m.py);
    assert!(m.px.abs() <= B, "px={} out of ±{B}", m.px);
    // check_invariants: Correct's five conjuncts, re-checked every step
    model::check_invariants(m);
}

/// One step of a random trace, dispatched by a small integer command plus a
/// piece choice (only consumed by `Fix`/`Fall`).
fn apply_command(m: &mut Machine<TestInstance>, cmd: u8, piece: TPiece) {
    match cmd % 7 {
        0 => {
            m.move_piece(0, -1);
        }
        1 => {
            m.move_piece(0, 1);
        }
        2 => {
            m.move_piece(-1, 0);
        }
        3 => {
            m.rotate_piece(true);
        }
        4 => {
            m.rotate_piece(false);
        }
        5 => {
            m.fix_piece(piece);
        }
        _ => {
            m.fall_step(piece);
        }
    }
}

fn piece_from_index(i: u8) -> TPiece {
    TestInstance::piece_all()[(i % 2) as usize]
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 256, .. ProptestConfig::default() })]

    #[test]
    fn invariants_hold_over_random_traces(
        start_piece_idx in 0u8..2,
        trace in prop::collection::vec((0u8..7, 0u8..2), 1..300),
    ) {
        let mut m = Machine::<TestInstance>::new(piece_from_index(start_piece_idx), fixture::piece_source_stub());
        check_common_invariants(&m);
        let mut prev_gameover = m.gameover;

        for (cmd, piece_idx) in trace {
            apply_command(&mut m, cmd, piece_from_index(piece_idx));
            check_common_invariants(&m);
            // gameover monotonicity: never flips back to false once true
            prop_assert!(!(prev_gameover && !m.gameover), "gameover flipped false after being true");
            prev_gameover = m.gameover;
        }
    }
}

// ── fix_piece's swap-partition: buffer reuse, not reallocation ──────────
//
// D13: line-clearing is fused in place, not a fresh allocation. This checks
// that every surviving row keeps its original buffer (by address), just
// possibly reordered or reset in place.

proptest! {
    #![proptest_config(ProptestConfig { cases: 128, .. ProptestConfig::default() })]

    #[test]
    fn fix_piece_reuses_row_buffers(
        // which of the 5 rows *other than* row 0 (the piece's resting row)
        // to pre-fill as full lines
        full_rows in prop::collection::hash_set(1usize..6, 0..5),
    ) {
        let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
        m.py = -1; // rests on row 0 (see model_unit_test.rs's bar_at_rest)
        m.px = 0;
        prop_assert!(!model::can_move_piece(-1, 0, &m));

        for &y in &full_rows {
            m.mg[y] = vec![Some(PieceOrExtra::Piece(TPiece::Corner)); WM as usize];
        }

        let before: std::collections::BTreeSet<usize> =
            m.mg.iter().map(|row| row.as_ptr() as usize).collect();
        prop_assert_eq!(before.len(), HM as usize, "rows should have distinct buffers to begin with");

        prop_assert!(m.fix_piece(TPiece::Corner));
        prop_assert_eq!(m.cleared_lines as usize, full_rows.len());

        let after: std::collections::BTreeSet<usize> =
            m.mg.iter().map(|row| row.as_ptr() as usize).collect();
        prop_assert_eq!(before, after, "row buffers should be the same set, just reordered/cleared in place");
    }
}
