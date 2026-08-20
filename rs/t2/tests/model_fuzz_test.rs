//! spec: tests/model_fuzz_test.rs — §9, `implementation.md`.

#[path = "test_instance.rs"]
mod fixture;

use fixture::{Prng, TestInstance};
use t1::model::{self as t1_model, Params};
use t2::instance::Tetris;
use t2::model::Machine;

/// Runs `steps` random commands against a fresh `Machine<P>`, asserting no
/// panic and, after every step, `type_ok` on `s1`, `LevelCorrect`, score/
/// level/`totalClearedLines` monotonicity, `ScoreRisesOnClear`, and
/// `s1.gameover` monotonicity.
///
/// §9 — clear detection uses the `totalClearedLines` delta. §9 (oracle
/// scope) / §0.1 — T1's grid-shaped `Correct` conjuncts aren't re-checked
/// here: `t1/tests/model_fuzz_test.rs` covers those on the same engine, and
/// `t2::model` never mutates grid content.
fn fuzz<P: Params>(seed: u64, steps: usize) {
    let mut rng = Prng::new(seed);
    let pieces = P::piece_all();
    let start = rng.choose(pieces);
    let mut m = Machine::<P>::new(start, || rng.choose(pieces));
    let mut prev_score = m.score;
    let mut prev_level = m.level;
    let mut prev_total = m.total_cleared_lines;
    let mut prev_gameover = m.s1.gameover;

    for step in 0..steps {
        match rng.next_below(7) {
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
            _ => {
                m.fall_step(rng.choose(pieces));
            }
        }

        assert!(
            t1_model::type_ok(&m.s1),
            "type_ok failed at step {step}: {:?}",
            m.s1.mg
        );
        assert_eq!(
            m.level,
            1 + m.total_cleared_lines / 10,
            "LevelCorrect failed at step {step}"
        );
        assert!(m.score >= prev_score, "score decreased at step {step}");
        assert!(m.level >= prev_level, "level decreased at step {step}");
        assert!(
            m.total_cleared_lines >= prev_total,
            "totalClearedLines decreased at step {step}"
        );
        if m.total_cleared_lines > prev_total {
            assert!(
                m.score > prev_score,
                "score did not rise on a clear at step {step}"
            );
        }
        assert!(
            !(prev_gameover && !m.s1.gameover),
            "gameover flipped false at step {step}"
        );

        prev_score = m.score;
        prev_level = m.level;
        prev_total = m.total_cleared_lines;
        prev_gameover = m.s1.gameover;
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
