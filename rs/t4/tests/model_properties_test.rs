// spec: tests/model_properties_test.rs — `proptest` (§9, `implementation.md`).
//
// NOTE: not compiled in the generation sandbox (rustc predates proptest's
// MSRV). Uses the same `proptest!` conventions as other floors' own
// `model_properties_test.rs`; run `cargo test -p t4` locally to confirm.
//
// Runs on `TestInstanceWide` (`NEXT_LEN = 5`) so traces cross multiple bag
// boundaries (§9). Checks, after every step:
// - `TypeOK`'s representable analogue, `BagNonEmpty`, and `next`'s
//   well-formedness via `t4::model::check_invariants` (delegates to
//   `t3::model::check_invariants` for `T3.Correct`'s conjuncts).
// - `BagNextConsistent` is not checked here: `T4.v`'s abstract check reads
//   already-popped values that this crate's finite `bag: Vec` doesn't
//   retain, so they're not representable at runtime (§3).
// - A differential oracle over every snapshot field (including `next`),
//   using the same disjoint-guard pattern as `model_fuzz_test.rs` to know
//   which `fall_step` branch fired.

#[path = "test_instance.rs"]
mod fixture;
#[path = "oracle.rs"]
mod oracle;

use fixture::{Piece, TestInstanceWide};
use proptest::prelude::*;
use t1::model::Params as T1Params;
use t4::model::{check_invariants, Machine, Params};

fn shuffle_bag_det(seed: &mut u64) -> Vec<Piece> {
    // Deterministic shuffle driven by proptest `u64`s (not the shared
    // `Prng` fixture) so randomness stays proptest-controlled and
    // shrinkable; same xorshift core as `t1/tests/test_instance.rs`'s `Prng`.
    let mut a = TestInstanceWide::piece_all().to_vec();
    for i in (1..a.len()).rev() {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        let j = (*seed as usize) % (i + 1);
        a.swap(i, j);
    }
    a
}

proptest! {
    #[test]
    fn invariants_and_oracle_hold_across_random_traces(
        init_seed in any::<u64>(),
        action_seed in any::<u64>(),
        actions in prop::collection::vec(0u8..5, 1..200),
    ) {
        let mut bags_seed = init_seed | 1; // avoid the xorshift fixed point at 0
        let mut bags: Vec<Vec<Piece>> = Vec::new();
        let mut bags_fn = move |i: u64| -> Vec<Piece> {
            let i = i as usize;
            while bags.len() <= i {
                bags.push(shuffle_bag_det(&mut bags_seed));
            }
            bags[i].clone()
        };

        let mut o_bags_seed = init_seed | 1;
        let mut o_bags: Vec<Vec<Piece>> = Vec::new();
        let mut o_bags_fn = move |i: u64| -> Vec<Piece> {
            let i = i as usize;
            while o_bags.len() <= i {
                o_bags.push(shuffle_bag_det(&mut o_bags_seed));
            }
            o_bags[i].clone()
        };

        let mut m = Machine::<TestInstanceWide>::new(&mut bags_fn, || Piece::Bar);
        let (op, mut od) = oracle::oracle_init_piece_and_draw::<Piece>(
            TestInstanceWide::NEXT_LEN as usize,
            &mut o_bags_fn,
        );
        prop_assert_eq!(m.s3.s2.s1.p, op);
        prop_assert_eq!(&m.bag, &od.bag);
        prop_assert_eq!(m.next.iter().copied().collect::<Vec<_>>(), od.next.clone());
        check_invariants(&m);

        let mut act_seed = action_seed | 1;
        for a in actions {
            if m.s3.s2.s1.gameover {
                break;
            }
            match a % 5 {
                0 => { m.move_piece(0, -1); }
                1 => { m.move_piece(0, 1); }
                2 => { m.rotate_piece(true); }
                3 => {
                    let bag_new = shuffle_bag_det(&mut act_seed);
                    if !m.move_piece(-1, 0) {
                        let fired = m.fix_piece(&bag_new);
                        if fired {
                            od.draw_once(&bag_new);
                        }
                    }
                }
                _ => {
                    let bag_new = shuffle_bag_det(&mut act_seed);
                    // hold_piece draws only when hold was empty (§4-T4g);
                    // mirror the oracle only then, or bag/next desync.
                    let will_draw = m.s3.hold.is_none() && !m.s3.s2.s1.gameover;
                    let fired = m.hold_piece(&bag_new);
                    if fired && will_draw {
                        od.draw_once(&bag_new);
                    }
                }
            }
            check_invariants(&m);
            prop_assert_eq!(&m.bag, &od.bag);
            prop_assert_eq!(m.next.iter().copied().collect::<Vec<_>>(), od.next.clone());
        }
    }
}
