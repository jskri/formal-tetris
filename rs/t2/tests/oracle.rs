//! spec: tests/oracle.rs — §9, `implementation.md`.
//!
//! A literal, from-scratch reimplementation of `T2.v`'s five new fields
//! (`score`/`level`/`combo`/`perfectClear`/`totalClearedLines`), checked
//! against `t2::model`'s own `line_clear_points`/`combo_points`/
//! `perfect_clear_points`/`points`/`empty_gridb`.
//!
//! §9 (oracle scope): the `s1`/grid half is not re-verified here (already
//! covered by `t1`'s own oracle); ground truth is read from `m.s1` per
//! §4-T2a.

#[path = "test_instance.rs"]
mod fixture;

use fixture::{Prng, TestInstance};
use t1::model::Params;
use t2::instance::Tetris;
use t2::model::Machine;

// ── Independent scoring arithmetic (spec: LineClearPoints, ComboPoints, PerfectClearPoints, Points, EmptyGridb) ──

fn rocq_line_clear_points(cleared_lines: u64, level: u64) -> u64 {
    match cleared_lines {
        0 => 0,
        1 => 100 * level,
        2 => 300 * level,
        3 => 500 * level,
        _ => 800 * level,
    }
}

fn rocq_combo_points(level: u64, combo: u64) -> u64 {
    if combo > 0 {
        50 * combo * level
    } else {
        0
    }
}

fn rocq_perfect_clear_points(perfect_clear: bool, cleared_lines: u64, level: u64) -> u64 {
    if !perfect_clear {
        return 0;
    }
    match cleared_lines {
        0 => 0,
        1 => 800 * level,
        2 => 1200 * level,
        3 => 1800 * level,
        _ => 2000 * level,
    }
}

fn rocq_points(cleared_lines: u64, level: u64, combo: u64, perfect_clear: bool) -> u64 {
    rocq_line_clear_points(cleared_lines, level)
        + rocq_combo_points(level, combo)
        + rocq_perfect_clear_points(perfect_clear, cleared_lines, level)
}

fn rocq_empty_grid<Piece>(mg: &[Vec<Option<Piece>>]) -> bool {
    mg.iter().all(|row| row.iter().all(Option::is_none))
}

// ── RocqState2: T2.v's five new fields, tracked independently ────────────

struct RocqState2 {
    score: u64,
    level: u64,
    combo: u64,
    perfect_clear: bool,
    total_cleared_lines: u64,
}

/// spec: Init
fn rocq_init2() -> RocqState2 {
    RocqState2 {
        score: 0,
        level: 1,
        combo: 0,
        perfect_clear: false,
        total_cleared_lines: 0,
    }
}

/// spec: FixPiece; five new-field updates, given a T1 fix already known to
/// have fired. Reads `m.s1` after the inner call, per §4-T2a/§6.4 ordering.
fn rocq_fix2<Piece>(
    s: &RocqState2,
    cleared_lines: u64,
    mg_after: &[Vec<Option<Piece>>],
) -> RocqState2 {
    let combo2 = if cleared_lines == 0 {
        0
    } else {
        s.combo.saturating_add(1)
    };
    let perfect_clear2 = rocq_empty_grid(mg_after);
    let pts = rocq_points(
        cleared_lines,
        s.level,
        combo2.saturating_sub(1),
        perfect_clear2,
    ); // OLD level
    let total2 = s.total_cleared_lines.saturating_add(cleared_lines);
    RocqState2 {
        score: s.score.saturating_add(pts),
        level: 1 + total2 / 10, // NEW total
        combo: combo2,
        perfect_clear: perfect_clear2,
        total_cleared_lines: total2,
    }
}

fn equivalent2<P: Params>(m: &Machine<P>, s: &RocqState2) -> bool {
    m.score == s.score
        && m.level == s.level
        && m.combo == s.combo
        && m.perfect_clear == s.perfect_clear
        && m.total_cleared_lines == s.total_cleared_lines
}

// ── Random-trace differential check ───────────────────────────────────────

fn run_differential<P: Params>(seed: u64, steps: usize) {
    let mut rng = Prng::new(seed);
    let pieces = P::piece_all();
    let start = rng.choose(pieces);

    let mut m = Machine::<P>::new(start, || rng.choose(pieces));
    let mut s = rocq_init2();
    assert!(equivalent2(&m, &s), "diverged at Init");

    for step in 1..=steps {
        let cmd = rng.next_below(7) as u8;
        let piece = rng.choose(pieces);

        match cmd % 7 {
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
                if m.fix_piece(piece) {
                    let cleared_lines = m.s1.cleared_lines as u64;
                    s = rocq_fix2(&s, cleared_lines, &m.s1.mg);
                }
            }
            _ => {
                // spec: FallStep (§6.5) — observes which branch fired
                // directly from move_piece's return value, not inferred
                // after the fact from machine state.
                if !m.move_piece(-1, 0) && m.fix_piece(piece) {
                    let cleared_lines = m.s1.cleared_lines as u64;
                    s = rocq_fix2(&s, cleared_lines, &m.s1.mg);
                }
            }
        }
        assert!(equivalent2(&m, &s), "T2 fields diverged at step {step}");
    }
}

#[test]
fn oracle_matches_random_trace_on_test_instance() {
    run_differential::<TestInstance>(0x0ff1_ce0d_d1ce_5eed, 5_000);
}

#[test]
fn oracle_matches_random_trace_on_real_instance() {
    run_differential::<Tetris>(0xfeed_face_f00d_cafe, 1_000);
}
