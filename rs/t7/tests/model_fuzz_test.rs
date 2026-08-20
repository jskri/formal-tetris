// spec: tests/model_fuzz_test.rs — multi-`Machine` harness (§9,
// `implementation.md`): several `Machine`s in one process, each one's
// outgoing values wired directly into the others' `receive_garbage`/
// `receive_gameover`/`receive_disconnect`/`notice_disconnection` calls, no
// socket involved — the same harness shape `net.rs` uses over the wire.
// The harness does not distinguish a `Host` index specially: a "player X's
// link goes down" event is delivered uniformly to every other
// still-connected player.

#[path = "test_instance.rs"]
mod fixture;
#[path = "oracle.rs"]
mod oracle;

use fixture::{Piece, Prng, TestInstance, PLAYER_COUNT};
use t1::model::Params as T1Params;
use t7::model::{check_invariants, Machine};

const SEEDS: u64 = 15;
const STEPS: usize = 250;

fn shuffle_bag(rng: &mut Prng) -> Vec<Piece> {
    let mut a = TestInstance::piece_all().to_vec();
    for i in (1..a.len()).rev() {
        let j = rng.next_below(i + 1);
        a.swap(i, j);
    }
    a
}

fn holes(y: i64) -> i64 {
    y.rem_euclid(5)
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
    Disconnect,
}
const ACTIONS: [Action; 10] = [
    Action::MoveLeft,
    Action::MoveRight,
    Action::RotateCw,
    Action::RotateCcw,
    Action::Fall,
    Action::Hold,
    Action::Drop,
    Action::KickCw,
    Action::KickCcw,
    Action::Disconnect,
];

/// After a call that may have fixed a piece (`fall_step`/`drop_piece`),
/// relays `rem_gen_garbage`/`gameover_view[my_index]` to the other machines
/// synchronously, no queue (§4-T7d/§4-T7e/§9, `implementation.md`).
fn relay_after_fix(
    machines: &mut [Machine<TestInstance>],
    harness_connected: &[bool],
    pl: usize,
    was_gameover_before: bool,
) {
    if !harness_connected[pl] {
        return; // FixPiece's own `if connected s pl then SendMessages ... else messages s` gate
    }
    let rem_gen_garbage = machines[pl].rem_gen_garbage;
    let target = machines[pl].target;
    let now_gameover = machines[pl].gameover_view[pl];

    if rem_gen_garbage > 0 && target != pl && harness_connected[target] {
        machines[target].receive_garbage(rem_gen_garbage);
    }
    if now_gameover && !was_gameover_before {
        for (i, m) in machines.iter_mut().enumerate() {
            if i != pl && harness_connected[i] {
                m.receive_gameover(pl);
            }
        }
    }
}

/// Harness-level stand-in for `DisconnectPlayer pl` (`implementation.md`
/// §4-T7f — no `Machine` method exists for this): flips the harness's own
/// ground truth, has `pl` notice its own disconnection, and relays
/// `DisconnectMessage` to every other still-connected player.
fn disconnect(machines: &mut [Machine<TestInstance>], harness_connected: &mut [bool], pl: usize) {
    if !harness_connected[pl] {
        return;
    }
    harness_connected[pl] = false;
    machines[pl].notice_disconnection();
    for (i, m) in machines.iter_mut().enumerate() {
        if i != pl {
            m.receive_disconnect(pl);
        }
    }
}

#[test]
fn fuzz_multi_machine_invariants_hold() {
    for seed in 1..=SEEDS {
        let mut rng = Prng::new(seed);

        let mut machines: Vec<Machine<TestInstance>> = (0..PLAYER_COUNT)
            .map(|my_index| {
                let mut bags: Vec<Vec<Piece>> = Vec::new();
                let mut seed_rng = Prng::new(seed ^ (0xA5A5_A5A5 + my_index as u64));
                let mut bags_fn = move |i: u64| -> Vec<Piece> {
                    let i = i as usize;
                    while bags.len() <= i {
                        bags.push(shuffle_bag(&mut seed_rng));
                    }
                    bags[i].clone()
                };
                Machine::<TestInstance>::new(my_index, PLAYER_COUNT, &mut bags_fn, || Piece::Bar)
            })
            .collect();
        for m in &machines {
            check_invariants(m);
        }

        let mut harness_connected = vec![true; PLAYER_COUNT];

        for step in 1..=STEPS {
            let pl = rng.next_below(PLAYER_COUNT);
            let was_gameover_before = machines[pl].gameover_view[pl];

            match ACTIONS[rng.next_below(ACTIONS.len())] {
                Action::MoveLeft => {
                    machines[pl].move_piece(0, -1);
                }
                Action::MoveRight => {
                    machines[pl].move_piece(0, 1);
                }
                Action::RotateCw => {
                    machines[pl].rotate_piece(true);
                }
                Action::RotateCcw => {
                    machines[pl].rotate_piece(false);
                }
                Action::Fall => {
                    machines[pl].fall_step(&shuffle_bag(&mut rng), holes);
                    relay_after_fix(&mut machines, &harness_connected, pl, was_gameover_before);
                }
                Action::Hold => {
                    machines[pl].hold_piece(&shuffle_bag(&mut rng));
                }
                Action::Drop => {
                    machines[pl].drop_piece(&shuffle_bag(&mut rng), holes);
                    relay_after_fix(&mut machines, &harness_connected, pl, was_gameover_before);
                }
                Action::KickCw => {
                    machines[pl].rotate_kick_piece(true);
                }
                Action::KickCcw => {
                    machines[pl].rotate_kick_piece(false);
                }
                Action::Disconnect => {
                    disconnect(&mut machines, &mut harness_connected, pl);
                }
            }

            for (i, m) in machines.iter().enumerate() {
                check_invariants(m);
                assert!(
                    m.target < PLAYER_COUNT,
                    "seed {seed} step {step} player {i}: target out of range"
                );
                assert_ne!(
                    m.gameover_view.len(),
                    0,
                    "seed {seed} step {step} player {i}: gameover_view must never be empty"
                );
            }
        }

        // req-multi-target-nonself, sampled post-trace: whenever at least
        // two players are still genuinely playing (truth, not view — the
        // harness knows it), nobody's target should point at herself.
        let truly_playing: Vec<bool> = (0..PLAYER_COUNT)
            .map(|i| !machines[i].s6.s4.s3.s2.s1.gameover && harness_connected[i])
            .collect();
        if truly_playing.iter().filter(|&&p| p).count() >= 2 {
            for (i, m) in machines.iter().enumerate() {
                if truly_playing[i] {
                    assert_ne!(m.target, i, "seed {seed}: TargetNotSelf violated for player {i} while >=2 truly playing");
                }
            }
        }
    }
}
