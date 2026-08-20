// spec: tests/oracle.rs — independent reference oracle for T7 (§9). Reuses
// `t6`'s own oracle for the `s6` portion (§0.1's reuse principle applied to
// testing scope); everything below `include!` — garbage generation/
// cancellation/materialization, target round-robin, playing/winner
// predicates — is hand-rolled independently of `model.rs`.

#![allow(dead_code)]

// A real `mod` (via `#[path]`), not a textual `include!`: `t6/tests/oracle.rs`
// starts with its own inner `#![allow(dead_code)]`, which `include!`-splicing
// cannot host mid-file. `t6/tests/model_unit_test.rs` reaches that oracle the
// same way, which is why that attribute is safe to keep there.
#[path = "../../t6/tests/oracle.rs"]
mod t6_oracle;
// Used by `model_properties_test.rs`'s own `#[path] mod oracle;` copy of
// this file; unused when this file itself compiles as its own (empty)
// integration-test binary.
#[allow(unused_imports)]
pub use t6_oracle::oracle_rotate_kick_piece;

// ── T7-specific: playing/winner/target (§5 of implementation.md) ────────

/// spec: PlayingView s pl pl2, `pl1` implicit (a `Machine` only ever
/// evaluates its own views).
pub fn oracle_playing_view(gameover_view: &[bool], connected_view: &[bool], pl2: usize) -> bool {
    !gameover_view[pl2] && connected_view[pl2]
}

/// spec: WinnerMulti s pl
pub fn oracle_winner_multi(
    gameover_view: &[bool],
    connected_view: &[bool],
    my_index: usize,
) -> bool {
    (0..gameover_view.len())
        .all(|pl2| oracle_playing_view(gameover_view, connected_view, pl2) == (pl2 == my_index))
}

/// spec: NextTargetAux / NextTarget
pub fn oracle_next_target(
    playing: impl Fn(usize) -> bool,
    self_: usize,
    pl: usize,
    player_count: usize,
) -> usize {
    let mut cur = pl;
    for _ in 0..player_count {
        cur = (cur + 1) % player_count;
        if playing(cur) && cur != self_ {
            return cur;
        }
    }
    self_
}

// ── T7-specific: garbage generation/cancellation (§4-T7b) ───────────────

/// spec: GeneratedGarbage
pub fn oracle_generated_garbage(cleared_lines: i64, perfect_clear: bool) -> i64 {
    let normal = if cleared_lines < 4 {
        (cleared_lines - 1).max(0)
    } else {
        cleared_lines
    };
    normal + if perfect_clear { 10 } else { 0 }
}

/// spec: GenRemGarbage
pub fn oracle_gen_rem_garbage(garbage: i64, cleared_lines: i64, perfect_clear: bool) -> (i64, i64) {
    let gen_garbage = oracle_generated_garbage(cleared_lines, perfect_clear);
    (gen_garbage, (garbage - gen_garbage).max(0))
}

// ── T7-specific: materialization (§4-T7c) ────────────────────────────────

/// Independent materialization oracle (§9): rebuilds the grid from scratch
/// by direct index mapping rather than `model.rs`'s in-place shift. Returns
/// `(new_mg, overflow)`; the caller ORs `overflow` with the prior `gameover`
/// and a forbidden-zone recheck to get the final `gameover2` (§4-T7c).
pub fn oracle_materialize<T: Copy + PartialEq>(
    old_mg: &[Vec<Option<T>>],
    rem_garbage: i64,
    holes: impl Fn(i64) -> i64,
    garbage_cell: T,
) -> (Vec<Vec<Option<T>>>, bool) {
    let hm = old_mg.len() as i64;
    let wm = if hm > 0 { old_mg[0].len() as i64 } else { 0 };
    let rem_garbage = rem_garbage.max(0);
    let eff_rem = rem_garbage.min(hm);

    let new_mg: Vec<Vec<Option<T>>> = (0..hm)
        .map(|y| {
            if y < eff_rem {
                let hole = holes(y);
                assert!(
                    0 <= hole && hole < wm,
                    "ValidHoles: hole {hole} outside [0, {wm})"
                );
                (0..wm)
                    .map(|x| if x == hole { None } else { Some(garbage_cell) })
                    .collect()
            } else {
                old_mg[(y - eff_rem) as usize].clone()
            }
        })
        .collect();

    // overflow: an occupied cell of old_mg pushed to y >= hm by the shift,
    // i.e. one of old_mg's top `rem_garbage` rows — or, once rem_garbage >=
    // hm, any occupied cell at all, since then the whole old grid is pushed off.
    let overflow = if rem_garbage >= hm {
        old_mg.iter().flatten().any(|c| c.is_some())
    } else {
        (hm - rem_garbage..hm).any(|y| old_mg[y as usize].iter().any(|c| c.is_some()))
    };

    (new_mg, overflow)
}
