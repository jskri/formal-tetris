//! spec: tests/model_fuzz_test.rs — §9, `implementation.md`.

#[path = "test_instance.rs"]
mod fixture;

use fixture::{Prng, TestInstance};
use t1::model::Params;
use t3::instance::Tetris;
use t3::model::Machine;

/// Runs `steps` random commands against a fresh `Machine<P>`, asserting no
/// panic, `type_ok` on the innermost `s2.s1`, `LevelCorrect`,
/// `SwappedImplyHoldSome`, `GameoverImplyNotSwapped`, `HoldMonotone`,
/// score/level/totalClearedLines monotonicity, `ScoreRisesOnClear`, and
/// `s2.s1.gameover` monotonicity, after every step.
///
/// Scope: R-TestScope (implementation.md §9) — only what's new to T3, plus
/// checks reached via delegation into T1/T2.
fn fuzz<P: Params>(seed: u64, steps: usize) {
    let mut rng = Prng::new(seed);
    let pieces = P::piece_all();
    let start = rng.choose(pieces);
    let mut m = Machine::<P>::new(start, || rng.choose(pieces));
    let mut prev_score = m.s2.score;
    let mut prev_level = m.s2.level;
    let mut prev_total = m.s2.total_cleared_lines;
    let mut prev_gameover = m.s2.s1.gameover;
    let mut prev_hold_some = m.hold.is_some();

    for step in 0..steps {
        match rng.next_below(8) {
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
                m.fix_piece(rng.choose(pieces));
            }
            6 => {
                m.fall_step(rng.choose(pieces));
            }
            _ => {
                m.hold_piece(rng.choose(pieces));
            }
        }

        assert!(
            t1::model::type_ok(&m.s2.s1),
            "type_ok failed at step {step}: {:?}",
            m.s2.s1.mg
        );
        assert_eq!(
            m.s2.level,
            1 + m.s2.total_cleared_lines / 10,
            "LevelCorrect failed at step {step}"
        );
        assert!(
            !m.swapped || m.hold.is_some(),
            "SwappedImplyHoldSome failed at step {step}"
        );
        assert!(
            !m.s2.s1.gameover || !m.swapped,
            "GameoverImplyNotSwapped failed at step {step}"
        );
        assert!(
            !(prev_hold_some && m.hold.is_none()),
            "HoldMonotone failed at step {step}: hold flipped to None"
        );
        assert!(m.s2.score >= prev_score, "score decreased at step {step}");
        assert!(m.s2.level >= prev_level, "level decreased at step {step}");
        assert!(
            m.s2.total_cleared_lines >= prev_total,
            "totalClearedLines decreased at step {step}"
        );
        if m.s2.total_cleared_lines > prev_total {
            assert!(
                m.s2.score > prev_score,
                "score did not rise on a clear at step {step}"
            );
        }
        assert!(
            !(prev_gameover && !m.s2.s1.gameover),
            "gameover flipped false at step {step}"
        );

        prev_score = m.s2.score;
        prev_level = m.s2.level;
        prev_total = m.s2.total_cleared_lines;
        prev_gameover = m.s2.s1.gameover;
        prev_hold_some = m.hold.is_some();
    }
}

#[test]
fn fuzz_test_instance_long_trace() {
    fuzz::<TestInstance>(0x1234_5678_9abc_def0, 20_000);
}

#[test]
fn fuzz_test_instance_many_seeds() {
    for seed in 1u64..=20 {
        fuzz::<TestInstance>(seed, 2_000);
    }
}

#[test]
fn fuzz_real_instance_long_trace() {
    fuzz::<Tetris>(0xdead_beef_cafe_f00d, 5_000);
}
