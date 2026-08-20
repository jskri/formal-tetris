// spec: tests/model_fuzz_test.rs — N seeds × M steps (§9, `implementation.md`).
//
// Runs on `TestInstanceWide` (`NEXT_LEN = 5`), the shared deterministic
// `Prng` (`t1/tests/test_instance.rs`), matching T1–T5's own fuzz suites.
// Checks every step: `check_invariants`, and on kick steps the same
// `oracle_rotate_kick_piece` differential `model_properties_test.rs` uses
// (see that file's header — this one differential covers mutual
// exclusivity too, not just value agreement). `t5`'s own mechanics are not
// re-tested here; no new axioms exist to fuzz (§7).

#[path = "test_instance.rs"]
mod fixture;
#[path = "oracle.rs"]
mod oracle;

use fixture::{Piece, Prng, TestInstanceWide};
use t1::model::Params as T1Params;
use t5::model::check_invariants;
use t6::model::{Machine, T6MachineExt};

const SEEDS: u64 = 20;
const STEPS: usize = 300;

fn shuffle_bag(rng: &mut Prng) -> Vec<Piece> {
    let mut a = TestInstanceWide::piece_all().to_vec();
    for i in (1..a.len()).rev() {
        let j = rng.next_below(i + 1);
        a.swap(i, j);
    }
    a
}

#[derive(Copy, Clone)]
enum Action {
    MoveLeft,
    MoveRight,
    RotateCw,
    RotateCcw,
    Fall,
    Hold,
    Drop,
    KickCw,
    KickCcw,
}
const ACTIONS: [Action; 9] = [
    Action::MoveLeft,
    Action::MoveRight,
    Action::RotateCw,
    Action::RotateCcw,
    Action::Fall,
    Action::Hold,
    Action::Drop,
    Action::KickCw,
    Action::KickCcw,
];

/// Snapshots the pre-kick state, calls `rotate_kick_piece`, and checks the
/// result against `oracle_rotate_kick_piece` from that snapshot. Duplicated
/// from `model_properties_test.rs`'s own helper, not shared (§9's
/// per-file convention).
fn check_kick_against_oracle(m: &mut Machine<TestInstanceWide>, cw: bool, seed: u64, step: usize) {
    let s1 = &m.s4.s3.s2.s1;
    let (p0, py0, px0, pr0, go0) = (s1.p, s1.py, s1.px, s1.pr, s1.gameover);
    let mg0 = s1.mg.clone();
    let rot_grids: Vec<Vec<Vec<Option<Piece>>>> = (0..4u8)
        .map(|r| TestInstanceWide::rot_grid(p0, r).clone())
        .collect();
    let expected = oracle::oracle_rotate_kick_piece(cw, &mg0, &rot_grids, py0, px0, pr0, go0);

    let fired = m.rotate_kick_piece(cw);

    match expected {
        Some((ey, ex, epr)) => {
            assert!(
                fired,
                "seed {seed} step {step}: oracle expected a fire, implementation returned false"
            );
            assert_eq!(
                m.s4.s3.s2.s1.py, ey,
                "seed {seed} step {step}: py diverged from oracle"
            );
            assert_eq!(
                m.s4.s3.s2.s1.px, ex,
                "seed {seed} step {step}: px diverged from oracle"
            );
            assert_eq!(
                m.s4.s3.s2.s1.pr, epr,
                "seed {seed} step {step}: pr diverged from oracle"
            );
            assert_eq!(
                m.s4.s3.s2.s1.mg, mg0,
                "seed {seed} step {step}: mg must be untouched by a kick"
            );
        }
        None => {
            assert!(
                !fired,
                "seed {seed} step {step}: oracle expected no fire, implementation returned true"
            );
            assert_eq!(
                m.s4.s3.s2.s1.py, py0,
                "seed {seed} step {step}: py must be restored/untouched"
            );
            assert_eq!(
                m.s4.s3.s2.s1.px, px0,
                "seed {seed} step {step}: px must be restored/untouched"
            );
            assert_eq!(
                m.s4.s3.s2.s1.pr, pr0,
                "seed {seed} step {step}: pr must be untouched"
            );
            assert_eq!(
                m.s4.s3.s2.s1.mg, mg0,
                "seed {seed} step {step}: mg must be untouched"
            );
        }
    }
}

#[test]
fn fuzz_invariants_and_kick_oracle_hold() {
    for seed in 1..=SEEDS {
        let mut rng = Prng::new(seed);

        // Referentially-consistent, per-run memoizing bags_fn
        // (inherited requirement, `t4/implementation.md`'s own note).
        let mut bags: Vec<Vec<Piece>> = Vec::new();
        let mut seed_rng = Prng::new(seed ^ 0xA5A5_A5A5);
        let mut bags_fn = move |i: u64| -> Vec<Piece> {
            let i = i as usize;
            while bags.len() <= i {
                bags.push(shuffle_bag(&mut seed_rng));
            }
            bags[i].clone()
        };

        let mut m = Machine::<TestInstanceWide>::new(&mut bags_fn, || Piece::Bar);
        check_invariants(&m);

        for step in 1..=STEPS {
            if m.s4.s3.s2.s1.gameover {
                break;
            }
            match ACTIONS[rng.next_below(ACTIONS.len())] {
                Action::MoveLeft => {
                    m.move_piece(0, -1);
                }
                Action::MoveRight => {
                    m.move_piece(0, 1);
                }
                Action::RotateCw => {
                    m.rotate_piece(true);
                }
                Action::RotateCcw => {
                    m.rotate_piece(false);
                }
                Action::Fall => {
                    m.fall_step(&shuffle_bag(&mut rng));
                }
                Action::Hold => {
                    m.hold_piece(&shuffle_bag(&mut rng));
                }
                Action::Drop => {
                    m.drop_piece(&shuffle_bag(&mut rng));
                }
                Action::KickCw => {
                    check_kick_against_oracle(&mut m, true, seed, step);
                }
                Action::KickCcw => {
                    check_kick_against_oracle(&mut m, false, seed, step);
                }
            }
            check_invariants(&m);
        }
    }
}
