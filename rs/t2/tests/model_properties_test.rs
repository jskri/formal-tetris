//! spec: tests/model_properties_test.rs — §9, `implementation.md`.

#[path = "test_instance.rs"]
mod fixture;

use fixture::{Piece as TPiece, TestInstance};
use proptest::prelude::*;
use t1::model::{self as t1_model, Params};
use t2::model::{self as t2_model, Machine};

/// Checks `T2.Correct` (`T1.Correct (s1 s) ∧ LevelCorrect s`) after a step,
/// via `t2::model::check_invariants` (delegates to t1 for the `s1` half, §9).
fn check_common_invariants(m: &Machine<TestInstance>) {
    assert!(t1_model::type_ok(&m.s1), "type_ok violated: {:?}", m.s1.mg);
    assert_eq!(
        m.level,
        1 + m.total_cleared_lines / 10,
        "LevelCorrect violated"
    );
    assert!(m.level >= 1);
    t2_model::check_invariants(m);
}

/// One step of a random trace, dispatched by a small integer command plus a
/// piece choice (only consumed by `Fix`/`Fall`) — same 7-way shape as T1's
/// own `apply_command` (`t1/tests/model_properties_test.rs`), now firing on
/// `t2::model::Machine`.
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
        let mut prev_score = m.score;
        let mut prev_level = m.level;
        let mut prev_total = m.total_cleared_lines;
        let mut prev_gameover = m.s1.gameover;

        for (cmd, piece_idx) in trace {
            apply_command(&mut m, cmd, piece_from_index(piece_idx));
            check_common_invariants(&m);

            // NonDecreasingScore / NonDecreasingLevel (T2.v)
            prop_assert!(m.score >= prev_score, "score decreased");
            prop_assert!(m.level >= prev_level, "level decreased");
            prop_assert!(m.total_cleared_lines >= prev_total, "totalClearedLines decreased");

            // ScoreRisesOnClear (T2.v); clear is detected via the
            // total_cleared_lines delta, not s1.cleared_lines (§9).
            if m.total_cleared_lines > prev_total {
                prop_assert!(m.score > prev_score, "score did not rise on a clear");
            }

            // gameover monotonicity (T1.v, transferred through s1)
            prop_assert!(!(prev_gameover && !m.s1.gameover), "gameover flipped false after being true");

            prev_score = m.score;
            prev_level = m.level;
            prev_total = m.total_cleared_lines;
            prev_gameover = m.s1.gameover;
        }
    }
}
