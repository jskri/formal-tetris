// spec: tests/model_properties_test.rs — `proptest` (§9, `implementation.md`).
//
// VERIFICATION: run standalone with `proptest` 1.4.0 pinned (not part of
// `t5`'s manifest); all 256 default cases pass. `view.rs`/`misc.rs`/`main.rs`
// need rustc 1.84+ and are unverified here; this file, `model.rs`, and
// `oracle.rs` don't depend on them.
//
// §9: `TestInstanceWide` traces cross bag boundaries, exercising T4's full
// inherited invariant set plus T5's two new ones; `gy` is checked against
// an independent oracle (`oracle.rs`) after every step, since
// `check_invariants` alone reuses `model.rs`'s own `shadow_y`.

#[path = "test_instance.rs"]
mod fixture;
#[path = "oracle.rs"]
mod oracle;

use fixture::{Piece, TestInstanceWide};
use proptest::prelude::*;
use t1::model::Params as T1Params;
use t5::model::{check_invariants, Machine};

fn shuffle_bag_det(seed: &mut u64) -> Vec<Piece> {
    // Same xorshift core as t4/tests/model_properties_test.rs's own
    // shuffle_bag_det — proptest-shrinkable, not the shared Prng fixture.
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

/// Asserts `m.gy` matches an independently-recomputed value whenever
/// `!gameover` (`GyEqShadowY`'s own precondition, `implementation.md` §6.8).
fn assert_gy_matches_oracle(m: &Machine<TestInstanceWide>) {
    let s1 = &m.s4.s3.s2.s1;
    if s1.gameover {
        return;
    }
    let pg = TestInstanceWide::rot_grid(s1.p, s1.pr);
    let expected = oracle::oracle_shadow_y(&s1.mg, pg, s1.py, s1.px);
    assert_eq!(m.gy, expected, "gy diverged from the independent oracle");
    assert!(m.gy <= s1.py, "LowestShadowY: gy <= py must hold");
}

proptest! {
    #[test]
    fn invariants_and_gy_oracle_hold_across_random_traces(
        init_seed in any::<u64>(),
        action_seed in any::<u64>(),
        actions in prop::collection::vec(0u8..7, 1..200),
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

        let mut m = Machine::<TestInstanceWide>::new(&mut bags_fn, || Piece::Bar);
        check_invariants(&m);
        assert_gy_matches_oracle(&m);

        let mut act_seed = action_seed | 1;
        for a in actions {
            if m.s4.s3.s2.s1.gameover {
                break;
            }
            match a % 7 {
                0 => { m.move_piece(0, -1); }
                1 => { m.move_piece(0, 1); }
                2 => { m.rotate_piece(true); }
                3 => { m.rotate_piece(false); }
                4 => { m.fall_step(&shuffle_bag_det(&mut act_seed)); }
                5 => { m.hold_piece(&shuffle_bag_det(&mut act_seed)); }
                _ => { m.drop_piece(&shuffle_bag_det(&mut act_seed)); }
            }
            check_invariants(&m);
            assert_gy_matches_oracle(&m);
        }
    }
}
