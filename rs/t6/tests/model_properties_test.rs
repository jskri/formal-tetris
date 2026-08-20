// spec: tests/model_properties_test.rs — `proptest` (§9, `implementation.md`).
//
// Runs on `TestInstanceWide` (`NEXT_LEN = 5`) so traces cross bag boundaries.
// After every step: checks `t5::model::check_invariants` (§4-T6b:
// `T6.Correct = T5.Correct`); for each `rotate_kick_piece` step, diffs the
// result against `oracle_rotate_kick_piece` (`oracle.rs`) from the same
// pre-state snapshot, which doubles as the mutual-exclusivity check (§9).

#[path = "test_instance.rs"]
mod fixture;
#[path = "oracle.rs"]
mod oracle;

use fixture::{Piece, TestInstanceWide};
use proptest::prelude::*;
use t1::model::Params as T1Params;
use t5::model::check_invariants;
use t6::model::{Machine, T6MachineExt};

fn shuffle_bag_det(seed: &mut u64) -> Vec<Piece> {
    // Same xorshift core as t5's shuffle_bag_det — proptest-shrinkable,
    // not the shared Prng fixture.
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

/// Snapshots the pre-kick state, calls `rotate_kick_piece`, and checks the
/// result against `oracle_rotate_kick_piece` computed from that same
/// snapshot.
fn check_kick_against_oracle(m: &mut Machine<TestInstanceWide>, cw: bool) {
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
                "oracle expected a fire, implementation returned false"
            );
            assert_eq!(m.s4.s3.s2.s1.py, ey, "py diverged from oracle");
            assert_eq!(m.s4.s3.s2.s1.px, ex, "px diverged from oracle");
            assert_eq!(m.s4.s3.s2.s1.pr, epr, "pr diverged from oracle");
            assert_eq!(m.s4.s3.s2.s1.p, p0, "p must be untouched by a kick");
            assert_eq!(m.s4.s3.s2.s1.mg, mg0, "mg must be untouched by a kick");
            assert_eq!(
                m.s4.s3.s2.s1.gameover, go0,
                "gameover must be untouched by a successful kick"
            );
        }
        None => {
            assert!(
                !fired,
                "oracle expected no fire, implementation returned true"
            );
            assert_eq!(
                m.s4.s3.s2.s1.py, py0,
                "py must be restored/untouched on a non-firing kick"
            );
            assert_eq!(
                m.s4.s3.s2.s1.px, px0,
                "px must be restored/untouched on a non-firing kick"
            );
            assert_eq!(
                m.s4.s3.s2.s1.pr, pr0,
                "pr must be untouched on a non-firing kick"
            );
            assert_eq!(
                m.s4.s3.s2.s1.mg, mg0,
                "mg must be untouched on a non-firing kick"
            );
            assert_eq!(
                m.s4.s3.s2.s1.gameover, go0,
                "gameover must be untouched on a non-firing kick"
            );
        }
    }
}

proptest! {
    #[test]
    fn invariants_and_kick_oracle_hold_across_random_traces(
        init_seed in any::<u64>(),
        action_seed in any::<u64>(),
        actions in prop::collection::vec(0u8..9, 1..200),
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

        let mut act_seed = action_seed | 1;
        for a in actions {
            if m.s4.s3.s2.s1.gameover {
                break;
            }
            match a % 9 {
                0 => { m.move_piece(0, -1); }
                1 => { m.move_piece(0, 1); }
                2 => { m.rotate_piece(true); }
                3 => { m.rotate_piece(false); }
                4 => { m.fall_step(&shuffle_bag_det(&mut act_seed)); }
                5 => { m.hold_piece(&shuffle_bag_det(&mut act_seed)); }
                6 => { m.drop_piece(&shuffle_bag_det(&mut act_seed)); }
                7 => { check_kick_against_oracle(&mut m, true); }
                _ => { check_kick_against_oracle(&mut m, false); }
            }
            check_invariants(&m);
        }
    }
}
