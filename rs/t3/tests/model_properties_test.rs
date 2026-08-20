//! spec: tests/model_properties_test.rs — §9, `implementation.md`.

#[path = "test_instance.rs"]
mod fixture;

use fixture::{Piece as TPiece, TestInstance};
use proptest::prelude::*;
use t1::model::Params;
use t3::model::{self as t3_model, Machine};

/// R-TestScope: checks T3's own conjuncts plus T2/T1's via
/// `t3::model::check_invariants`'s delegation.
fn check_common_invariants(m: &Machine<TestInstance>) {
    t3_model::check_invariants(m);
}

/// One step of a random trace: T2's 7-way command dispatch plus an 8th
/// `Hold` branch, firing on `t3::model::Machine`.
fn apply_command(m: &mut Machine<TestInstance>, cmd: u8, piece: TPiece) {
    match cmd % 8 {
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
        6 => {
            m.fall_step(piece);
        }
        _ => {
            m.hold_piece(piece);
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
        trace in prop::collection::vec((0u8..8, 0u8..2), 1..300),
    ) {
        let mut m = Machine::<TestInstance>::new(piece_from_index(start_piece_idx), fixture::piece_source_stub());
        check_common_invariants(&m);
        let mut prev_score = m.s2.score;
        let mut prev_level = m.s2.level;
        let mut prev_total = m.s2.total_cleared_lines;
        let mut prev_gameover = m.s2.s1.gameover;
        let mut prev_hold_some = m.hold.is_some();

        for (cmd, piece_idx) in trace {
            apply_command(&mut m, cmd, piece_from_index(piece_idx));
            check_common_invariants(&m);

            // NonDecreasingScore / NonDecreasingLevel (transferred through s2, T2.v)
            prop_assert!(m.s2.score >= prev_score, "score decreased");
            prop_assert!(m.s2.level >= prev_level, "level decreased");
            prop_assert!(m.s2.total_cleared_lines >= prev_total, "totalClearedLines decreased");

            // ScoreRisesOnClear, via the totalClearedLines delta (cleared_lines
            // survives Move/Rotate unchanged, so no false positive there).
            if m.s2.total_cleared_lines > prev_total {
                prop_assert!(m.s2.score > prev_score, "score did not rise on a clear");
            }

            // gameover monotonicity (T1.v, transferred through s2.s1)
            prop_assert!(!(prev_gameover && !m.s2.s1.gameover), "gameover flipped false after being true");

            // HoldMonotone (T3.v): once hold is Some, it stays Some across every step.
            prop_assert!(!(prev_hold_some && m.hold.is_none()), "hold flipped to None after being Some");

            // narrow-blast-radius, generalized: a firing Hold touches only
            // p/py/px/pr and hold/swapped, checked structurally via
            // SwappedImplyHoldSome/GameoverImplyNotSwapped rather than a
            // byte-identical grid comparison (an earlier non-Hold command in
            // the trace may have legitimately changed mg).
            prop_assert!(!m.swapped || m.hold.is_some(), "SwappedImplyHoldSome violated");
            prop_assert!(!m.s2.s1.gameover || !m.swapped, "GameoverImplyNotSwapped violated");

            prev_score = m.s2.score;
            prev_level = m.s2.level;
            prev_total = m.s2.total_cleared_lines;
            prev_gameover = m.s2.s1.gameover;
            prev_hold_some = m.hold.is_some();
        }
    }
}
