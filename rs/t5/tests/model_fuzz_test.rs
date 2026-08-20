// spec: tests/model_fuzz_test.rs — N seeds × M steps (§9, `implementation.md`).
//
// §9: `TestInstanceWide` traces trigger repeated bag resets, exercising
// T4's full inherited invariant set plus T5's two new ones. Uses the
// shared deterministic `Prng` fixture. Checks `check_invariants` and an
// independent `oracle_shadow_y` differential against `gy` after every step
// (not just at resets — `gy` can change on any successful action).

#[path = "test_instance.rs"]
mod fixture;
#[path = "oracle.rs"]
mod oracle;

use fixture::{Piece, Prng, TestInstanceWide};
use t1::model::Params as T1Params;
use t4::model::Params as T4Params; // brings NEXT_LEN into scope for TestInstanceWide::NEXT_LEN below
use t5::model::{check_invariants, Machine};

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
}
const ACTIONS: [Action; 7] = [
    Action::MoveLeft,
    Action::MoveRight,
    Action::RotateCw,
    Action::RotateCcw,
    Action::Fall,
    Action::Hold,
    Action::Drop,
];

/// Asserts `m.gy` matches an independently-recomputed value whenever
/// `!gameover` (`GyEqShadowY`'s own precondition, `implementation.md` §6.8).
fn assert_gy_matches_oracle(m: &Machine<TestInstanceWide>, seed: u64, step: usize) {
    let s1 = &m.s4.s3.s2.s1;
    if s1.gameover {
        return;
    }
    let pg = TestInstanceWide::rot_grid(s1.p, s1.pr);
    let expected = oracle::oracle_shadow_y(&s1.mg, pg, s1.py, s1.px);
    assert_eq!(
        m.gy, expected,
        "seed {seed} step {step}: gy diverged from the independent oracle"
    );
    assert!(
        m.gy <= s1.py,
        "seed {seed} step {step}: LowestShadowY: gy <= py must hold"
    );
}

#[test]
fn fuzz_invariants_and_gy_oracle_hold() {
    for seed in 1..=SEEDS {
        let mut rng = Prng::new(seed);

        // Referentially-consistent, per-run memoizing bags_fn
        // (`t4/implementation.md` §4-T4b's requirement, inherited from T4).
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
        assert_gy_matches_oracle(&m, seed, 0);

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
                    let next_len_before = m.s4.next.len();
                    let fired = m.fall_step(&shuffle_bag(&mut rng));
                    if fired {
                        // next length is conserved by every successful
                        // fall/fix (inherited from T4; unaffected by gy).
                        assert_eq!(m.s4.next.len(), next_len_before);
                    }
                }
                Action::Hold => {
                    m.hold_piece(&shuffle_bag(&mut rng));
                }
                Action::Drop => {
                    let was_gameover = m.s4.s3.s2.s1.gameover;
                    let fired = m.drop_piece(&shuffle_bag(&mut rng));
                    if !was_gameover {
                        assert!(
                            fired,
                            "seed {seed} step {step}: drop_piece must fire whenever not gameover"
                        );
                    }
                }
            }
            check_invariants(&m);
            assert_gy_matches_oracle(&m, seed, step);
        }
    }
}

/// Differential check on `bag`/`next`: drives the production `Machine` and
/// `t4`'s independent oracle through the same sequence of `draw_once`
/// calls, reusing T4's own oracle for the `s4`-level mechanics (this
/// file's `oracle_shadow_y` differential above covers what's new to T5).
#[path = "../../t4/tests/oracle.rs"]
mod t4_oracle;

#[test]
fn fuzz_oracle_differential_on_bag_next_through_t5_actions() {
    for seed in 1..=SEEDS {
        let mut rng = Prng::new(seed ^ 0xDEAD_BEEF);
        let mut bags: Vec<Vec<Piece>> = Vec::new();
        let mut seed_rng = Prng::new(seed ^ 0xFEED_FACE);
        let mut bags_fn = move |i: u64| -> Vec<Piece> {
            let i = i as usize;
            while bags.len() <= i {
                bags.push(shuffle_bag(&mut seed_rng));
            }
            bags[i].clone()
        };

        let mut o_bags: Vec<Vec<Piece>> = Vec::new();
        let mut o_seed_rng = Prng::new(seed ^ 0xFEED_FACE);
        let mut o_bags_fn = move |i: u64| -> Vec<Piece> {
            let i = i as usize;
            while o_bags.len() <= i {
                o_bags.push(shuffle_bag(&mut o_seed_rng));
            }
            o_bags[i].clone()
        };

        let mut m = Machine::<TestInstanceWide>::new(&mut bags_fn, || Piece::Bar);
        let (op, mut od) = t4_oracle::oracle_init_piece_and_draw::<Piece>(
            TestInstanceWide::NEXT_LEN as usize,
            &mut o_bags_fn,
        );
        assert_eq!(m.s4.s3.s2.s1.p, op, "seed {seed}: initial piece mismatch");
        assert_eq!(m.s4.bag, od.bag, "seed {seed}: initial bag mismatch");
        assert_eq!(
            m.s4.next.iter().copied().collect::<Vec<_>>(),
            od.next,
            "seed {seed}: initial next mismatch"
        );

        for step in 0..STEPS {
            if m.s4.s3.s2.s1.gameover {
                break;
            }
            let bag_new = shuffle_bag(&mut rng);
            // fall_step and drop_piece can both reach fix_piece; drive them
            // through an explicit disjoint-guard pattern (matching T4's own
            // fuzz test) so it's known which one triggered a draw.
            let fired = if rng.next_below(2) == 0 {
                if !m.move_piece(-1, 0) {
                    m.fix_piece(&bag_new)
                } else {
                    false
                }
            } else {
                m.drop_piece(&bag_new)
            };
            if fired {
                od.draw_once(&bag_new);
                assert_eq!(
                    m.s4.bag, od.bag,
                    "seed {seed} step {step}: bag diverged from oracle after fix"
                );
                assert_eq!(
                    m.s4.next.iter().copied().collect::<Vec<_>>(),
                    od.next,
                    "seed {seed} step {step}: next diverged from oracle after fix"
                );
            }
        }
    }
}
