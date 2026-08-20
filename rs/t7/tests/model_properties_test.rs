// spec: tests/model_properties_test.rs — `proptest` (§9, `implementation.md`).
//
// Pure-function properties for `next_target`/`winner_multi`, plus a
// single-`Machine` randomized trace checking `check_invariants` after
// every action.

#[path = "test_instance.rs"]
mod fixture;
#[path = "oracle.rs"]
mod oracle;

use fixture::{Piece, TestInstance, PLAYER_COUNT};
use proptest::prelude::*;
use t1::model::Params as T1Params;
use t7::model::{
    check_invariants, gen_rem_garbage, generated_garbage, next_target, winner_multi, Machine,
};

// ── next_target / winner_multi: pure-function properties ────────────────

proptest! {
    /// spec: §9, req-multi-target-nonself — `next_target` returns `self_`
    /// only when no other playing index exists; otherwise the result is
    /// playing and `!= self_`.
    #[test]
    fn next_target_never_self_unless_no_alternative(
        player_count in 2usize..8,
        self_ in 0usize..8,
        pl in 0usize..8,
        playing_bits in prop::collection::vec(any::<bool>(), 2..8),
    ) {
        let self_ = self_ % player_count;
        let pl = pl % player_count;
        let playing_bits: Vec<bool> = (0..player_count).map(|i| playing_bits[i % playing_bits.len()]).collect();
        let playing = |pl2: usize| playing_bits[pl2];

        let has_alternative = (0..player_count).any(|pl2| pl2 != self_ && playing(pl2));
        let result = next_target(playing, self_, pl, player_count);

        if has_alternative {
            prop_assert_ne!(result, self_);
            prop_assert!(playing(result));
        } else {
            prop_assert_eq!(result, self_);
        }
    }

    /// `winner_multi` is `ForallPlayers`: true iff `playing_view(pl2) ==
    /// (pl2 == my_index)` for every `pl2`. Checked against a direct
    /// re-derivation from the same arrays, independent of `winner_multi`'s
    /// own loop shape.
    #[test]
    fn winner_multi_matches_direct_definition(
        n in 2usize..8,
        my_index in 0usize..8,
        gameover_bits in prop::collection::vec(any::<bool>(), 2..8),
        connected_bits in prop::collection::vec(any::<bool>(), 2..8),
    ) {
        let my_index = my_index % n;
        let gameover_view: Vec<bool> = (0..n).map(|i| gameover_bits[i % gameover_bits.len()]).collect();
        let connected_view: Vec<bool> = (0..n).map(|i| connected_bits[i % connected_bits.len()]).collect();

        let expected = (0..n).all(|pl2| {
            let playing = !gameover_view[pl2] && connected_view[pl2];
            playing == (pl2 == my_index)
        });

        prop_assert_eq!(winner_multi(&gameover_view, &connected_view, my_index), expected);
    }

    /// `rem_gen_garbage` (`= max(0, genGarbage - garbage)`, at the
    /// `fix_piece` call site) and `rem_garbage` (`gen_rem_garbage`'s own
    /// 2nd component, `= max(0, garbage - genGarbage)`) never both exceed
    /// 0 — they floor at 0 on opposite sides of the same subtraction
    /// (§4-T7b). Not a claim about `gen_rem_garbage`'s own two components,
    /// which can both be positive (e.g. `garbage=19, clearedLines=2` gives
    /// `genGarbage=1, remGarbage=18`).
    #[test]
    fn rem_gen_garbage_and_rem_garbage_at_most_one_nonzero(
        garbage in 0i64..1000,
        cleared_lines in 0i64..20,
        perfect_clear in any::<bool>(),
    ) {
        let (gen_garbage, rem_garbage) = gen_rem_garbage(garbage, cleared_lines, perfect_clear);
        let rem_gen_garbage = (gen_garbage - garbage).max(0);
        prop_assert!(rem_gen_garbage == 0 || rem_garbage == 0);
        prop_assert!(gen_garbage >= 0 && rem_garbage >= 0 && rem_gen_garbage >= 0);
        let expected_gen = generated_garbage(cleared_lines, perfect_clear);
        prop_assert_eq!(gen_garbage, expected_gen);
    }
}

// ── single-Machine randomized trace: invariants hold at every step ──────

fn shuffle_bag_det(seed: &mut u64) -> Vec<Piece> {
    let mut a = TestInstance::piece_all().to_vec();
    for i in (1..a.len()).rev() {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        let j = (*seed as usize) % (i + 1);
        a.swap(i, j);
    }
    a
}

fn holes(y: i64) -> i64 {
    y.rem_euclid(5)
}

/// spec: §9 — differential-oracle check: snapshots the pre-kick state,
/// calls `rotate_kick_piece`, and compares against
/// `oracle::oracle_rotate_kick_piece` (reuses `t6`'s own oracle, §0.1).
fn check_kick_against_oracle(m: &mut Machine<TestInstance>, cw: bool) {
    let s1 = &m.s6.s4.s3.s2.s1;
    let (p0, py0, px0, pr0, go0) = (s1.p, s1.py, s1.px, s1.pr, s1.gameover);
    let mg0 = s1.mg.clone();
    let rot_grids: Vec<Vec<Vec<Option<Piece>>>> = (0..4u8)
        .map(|r| TestInstance::rot_grid(p0, r).clone())
        .collect();
    let expected = oracle::oracle_rotate_kick_piece(cw, &mg0, &rot_grids, py0, px0, pr0, go0);

    let fired = m.rotate_kick_piece(cw);

    match expected {
        Some((ey, ex, epr)) => {
            assert!(
                fired,
                "oracle expected a fire, implementation returned false"
            );
            assert_eq!(m.s6.s4.s3.s2.s1.py, ey);
            assert_eq!(m.s6.s4.s3.s2.s1.px, ex);
            assert_eq!(m.s6.s4.s3.s2.s1.pr, epr);
        }
        None => {
            assert!(
                !fired,
                "oracle expected no fire, implementation returned true"
            );
            assert_eq!(m.s6.s4.s3.s2.s1.py, py0);
            assert_eq!(m.s6.s4.s3.s2.s1.px, px0);
            assert_eq!(m.s6.s4.s3.s2.s1.pr, pr0);
        }
    }
}

proptest! {
    #[test]
    fn invariants_hold_across_random_single_machine_traces(
        my_index in 0usize..PLAYER_COUNT,
        init_seed in any::<u64>(),
        action_seed in any::<u64>(),
        actions in prop::collection::vec(0u8..12, 1..200),
    ) {
        let mut bags_seed = init_seed | 1;
        let mut bags: Vec<Vec<Piece>> = Vec::new();
        let mut bags_fn = move |i: u64| -> Vec<Piece> {
            let i = i as usize;
            while bags.len() <= i {
                bags.push(shuffle_bag_det(&mut bags_seed));
            }
            bags[i].clone()
        };

        let mut m = Machine::<TestInstance>::new(my_index, PLAYER_COUNT, &mut bags_fn, || Piece::Bar);
        check_invariants(&m);

        // A fake "other player" index, distinct from my_index, to feed
        // receive_*'s from parameter — exercises receive_*'s own field
        // updates/guards without a real second Machine (see model_fuzz_test.rs).
        let other = (my_index + 1) % PLAYER_COUNT;

        let mut act_seed = action_seed | 1;
        for a in actions {
            match a % 12 {
                0 => { m.move_piece(0, -1); }
                1 => { m.move_piece(0, 1); }
                2 => { m.rotate_piece(true); }
                3 => { m.rotate_piece(false); }
                4 => { m.fall_step(&shuffle_bag_det(&mut act_seed), holes); }
                5 => { m.hold_piece(&shuffle_bag_det(&mut act_seed)); }
                6 => { m.drop_piece(&shuffle_bag_det(&mut act_seed), holes); }
                7 => { check_kick_against_oracle(&mut m, true); }
                8 => { check_kick_against_oracle(&mut m, false); }
                9 => { m.receive_garbage((act_seed % 5) as i64); }
                10 => { m.receive_gameover(other); }
                _ => { m.receive_disconnect(other); }
            }
            check_invariants(&m);
        }
    }
}
