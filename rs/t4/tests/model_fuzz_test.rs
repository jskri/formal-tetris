// spec: tests/model_fuzz_test.rs — N seeds × M steps (§9, `implementation.md`).
//
// Runs on `TestInstanceWide` so bag resets happen repeatedly, not just once
// at startup (§9). Checks structural invariants (`check_invariants`) after
// every successful action, that `next`'s length is conserved across a
// successful fix, and an oracle differential over `bag`/`next` at every
// reset boundary.

#[path = "test_instance.rs"]
mod fixture;
#[path = "oracle.rs"]
mod oracle;

use fixture::{Piece, Prng, TestInstanceWide};
use t1::model::Params as T1Params;
use t4::model::{check_invariants, Machine, Params};

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
    Rotate,
    Fall,
    Hold,
}
const ACTIONS: [Action; 5] = [
    Action::MoveLeft,
    Action::MoveRight,
    Action::Rotate,
    Action::Fall,
    Action::Hold,
];

#[test]
fn fuzz_structural_and_new_invariants_hold() {
    for seed in 1..=SEEDS {
        let mut rng = Prng::new(seed);

        // Referentially-consistent, per-run memoizing bags_fn
        // (`implementation.md` §4-T4b's requirement).
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

        for _ in 0..STEPS {
            if m.s3.s2.s1.gameover {
                break;
            }
            match ACTIONS[rng.next_below(ACTIONS.len())] {
                Action::MoveLeft => {
                    m.move_piece(0, -1);
                }
                Action::MoveRight => {
                    m.move_piece(0, 1);
                }
                Action::Rotate => {
                    m.rotate_piece(rng.next_below(2) == 0);
                }
                Action::Fall => {
                    let next_len_before = m.next.len();
                    let fired = m.fall_step(&shuffle_bag(&mut rng));
                    if fired {
                        // one popped, one pushed; a reset only ever changes
                        // bag's length, never next's.
                        assert_eq!(m.next.len(), next_len_before);
                    }
                }
                Action::Hold => {
                    m.hold_piece(&shuffle_bag(&mut rng));
                }
            }
            check_invariants(&m);
        }
    }
}

/// Differential check: drives `Machine` and `OracleDraw` through the same
/// sequence of `draw_once` calls, keeping `bag`/`next` in agreement at
/// every step.
#[test]
fn fuzz_oracle_differential_on_bag_next() {
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

        // Independently-memoized bags_fn for the oracle, seeded to match.
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
        let (op, mut od) = oracle::oracle_init_piece_and_draw::<Piece>(
            TestInstanceWide::NEXT_LEN as usize,
            &mut o_bags_fn,
        );
        assert_eq!(m.s3.s2.s1.p, op, "seed {seed}: initial piece mismatch");
        assert_eq!(m.bag, od.bag, "seed {seed}: initial bag mismatch");
        assert_eq!(
            m.next.iter().copied().collect::<Vec<_>>(),
            od.next,
            "seed {seed}: initial next mismatch"
        );

        for _ in 0..STEPS {
            if m.s3.s2.s1.gameover {
                break;
            }
            let bag_new = shuffle_bag(&mut rng);
            // Disjoint-guard sequencing matching fall_step's body (§4-T4e),
            // done by hand here so the test knows for certain which branch
            // fired.
            if !m.move_piece(-1, 0) {
                let fired = m.fix_piece(&bag_new);
                if fired {
                    od.draw_once(&bag_new);
                    assert_eq!(
                        m.bag, od.bag,
                        "seed {seed}: bag diverged from oracle after fix"
                    );
                    assert_eq!(
                        m.next.iter().copied().collect::<Vec<_>>(),
                        od.next,
                        "seed {seed}: next diverged from oracle after fix"
                    );
                }
            }
        }
    }
}
