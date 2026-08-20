//! spec: tests/model_fuzz_test.rs — §9.3, `implementation.md`.

#[path = "test_instance.rs"]
mod fixture;

use fixture::{Prng, TestInstance};
use t1::instance::Tetris;
use t1::model::{self, Machine, Params};

/// Runs `steps` random commands against a fresh `Machine<P>`, asserting no
/// panic, `type_ok`, integer-field bounds (D10), and gameover monotonicity
/// after every single step. Does not check the other four `Correct`
/// conjuncts (would just be re-checking `model.rs` against itself);
/// `tests/oracle.rs` (§9.4) verifies those independently at lower step counts.
fn fuzz<P: Params>(seed: u64, steps: usize) {
    let hm = P::initial_main_grid().len() as i64;
    let wm = if hm > 0 {
        P::initial_main_grid()[0].len() as i64
    } else {
        0
    };
    let b = std::cmp::max(hm, wm) + P::PW - 1;

    let mut rng = Prng::new(seed);
    let pieces = P::piece_all();
    let start = rng.choose(pieces);
    let mut m = Machine::<P>::new(start, || rng.choose(pieces));
    let mut prev_gameover = m.gameover;

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
            model::type_ok(&m),
            "type_ok failed at step {step}: {:?}",
            m.mg
        );
        assert!(m.py.abs() <= b, "py out of bounds at step {step}: {}", m.py);
        assert!(m.px.abs() <= b, "px out of bounds at step {step}: {}", m.px);
        assert!(
            !(prev_gameover && !m.gameover),
            "gameover flipped false at step {step}"
        );
        prev_gameover = m.gameover;
    }
}

#[test]
fn fuzz_test_instance_long_trace() {
    fuzz::<TestInstance>(0x1234_5678_9abc_def0, 20_000);
}

#[test]
fn fuzz_test_instance_many_seeds() {
    // shorter independent traces to catch seed-dependent issues a single run might miss
    for seed in 1u64..=20 {
        fuzz::<TestInstance>(seed, 2_000);
    }
}

#[test]
fn fuzz_real_instance_long_trace() {
    fuzz::<Tetris>(0xdead_beef_cafe_f00d, 5_000);
}

// ── Adversarial check_axioms ─────────────────────────────────────────────
//
// Violates `AxiomsPW` (`PW = 0`). `check_axioms` checks `AxiomsPW` first, so
// `unreachable!()` bodies suffice for the rest of this impl.

struct MalformedPw;

impl Params for MalformedPw {
    type Piece = ();
    type CellExtra = std::convert::Infallible;

    const PW: i64 = 0; // violates AxiomsPW (`PW > 0`)
    const FY: i64 = 0;
    const FX: i64 = 0;

    fn piece_all() -> &'static [()] {
        unreachable!("check_axioms fails on AxiomsPW before reaching this")
    }
    fn initial_main_grid() -> &'static Vec<Vec<bool>> {
        unreachable!()
    }
    fn forbidden_grid() -> &'static Vec<Vec<bool>> {
        unreachable!()
    }
    fn rot_grid(_p: (), _r: u8) -> &'static Vec<Vec<Option<()>>> {
        unreachable!()
    }
    fn initial_y(_p: ()) -> i64 {
        unreachable!()
    }
    fn initial_x(_p: ()) -> i64 {
        unreachable!()
    }
}

#[test]
#[should_panic]
fn malformed_pw_trips_check_axioms() {
    model::check_axioms::<MalformedPw>();
}

/// Violates `AxiomsInitialYX` (spawn position outside the main grid).
/// Reachable only after `AxiomsPW`/dimension checks pass, so the rest of
/// this impl must be genuinely well-formed.
struct MalformedInitialYX;

const MALFORMED_MAIN_GRID: [[bool; 3]; 3] = [[false; 3]; 3];
const MALFORMED_FORBIDDEN_GRID: [[bool; 3]; 1] = [[true; 3]];
const MALFORMED_PIECE_GRID: [[Option<()>; 3]; 3] = [
    [None, None, None],
    [Some(()), Some(()), Some(())],
    [None, None, None],
];

impl Params for MalformedInitialYX {
    type Piece = ();
    type CellExtra = std::convert::Infallible;

    const PW: i64 = 3;
    const FY: i64 = 2;
    const FX: i64 = 0;

    fn piece_all() -> &'static [()] {
        &[()]
    }
    fn initial_main_grid() -> &'static Vec<Vec<bool>> {
        static G: std::sync::LazyLock<Vec<Vec<bool>>> =
            std::sync::LazyLock::new(|| MALFORMED_MAIN_GRID.iter().map(|r| r.to_vec()).collect());
        &G
    }
    fn forbidden_grid() -> &'static Vec<Vec<bool>> {
        static G: std::sync::LazyLock<Vec<Vec<bool>>> = std::sync::LazyLock::new(|| {
            MALFORMED_FORBIDDEN_GRID
                .iter()
                .map(|r| r.to_vec())
                .collect()
        });
        &G
    }
    fn rot_grid(_p: (), _r: u8) -> &'static Vec<Vec<Option<()>>> {
        static G: std::sync::LazyLock<Vec<Vec<Option<()>>>> =
            std::sync::LazyLock::new(|| MALFORMED_PIECE_GRID.iter().map(|r| r.to_vec()).collect());
        &G
    }
    fn initial_y(_p: ()) -> i64 {
        1000 // far outside the 3-row main grid — violates AxiomsInitialYX
    }
    fn initial_x(_p: ()) -> i64 {
        0
    }
}

#[test]
#[should_panic]
fn malformed_initial_y_trips_check_axioms() {
    model::check_axioms::<MalformedInitialYX>();
}
