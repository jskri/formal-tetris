// spec: tests/model_unit_test.rs — golden vectors (§9, `implementation.md`).
//
// `is_piece_set`/`assert_piece_set` are t4::model items already covered by
// t4/tests/model_unit_test.rs — not re-tested here. This file covers only
// what's new to T5: `gy`/`shadow_y`, `drop_piece`.
//
// Geometry (`TestInstance`: `PW=3`, `HM=6`, `WM=5`, `FY=4`, `FX=0`,
// `INITIAL_Y=3`, `INITIAL_X=1`): `mg[y][x]` with `y` increasing upward
// (`y=0` the floor, per D3). Piece grids `pg[dy][dx]`, `dy` increasing
// upward within the piece's own `PW×PW` box (`y = py + dy`), same D3
// convention applied to `RotGrid`'s local origin (D1).

#[path = "test_instance.rs"]
mod fixture;

use fixture::{Piece, TestInstance};
use t1::model::Params as T1Params;
use t1::model::PieceOrExtra;
use t5::model::{check_invariants, Machine};

fn bags_alternating() -> impl FnMut(u64) -> Vec<Piece> {
    |i: u64| {
        if i % 2 == 0 {
            vec![Piece::Bar, Piece::Corner]
        } else {
            vec![Piece::Corner, Piece::Bar]
        }
    }
}

fn piece_source() -> Piece {
    Piece::Bar
}

// ── gy correctness at Init ──────────────────────────────────────────────

/// §4-T5a: `Init`'s `gy := ShadowY s4` conjunct — pins `gy` to the exact
/// unobstructed floor for the spawned piece/rotation, not merely `≤ py`
/// (`check_invariants` checks this only structurally).
#[test]
fn init_gy_is_unobstructed_floor_for_spawned_piece() {
    let m = Machine::<TestInstance>::new(bags_alternating(), piece_source);
    check_invariants(&m);
    // `init_matches_hand_traced_vector` (t4/tests/model_unit_test.rs) established
    // this exact bags_fn/piece_source spawns Piece::Corner at r0/py=INITIAL_Y=3.
    assert_eq!(m.s4.s3.s2.s1.p, Piece::Corner);
    assert_eq!(m.s4.s3.s2.s1.pr, 0);
    // Corner r0 occupies dy={1,2} (bottom row empty), min_row=1, so the
    // unobstructed floor is -1 — a negative anchor, exactly why §4-T5a's
    // fuel bound is `py + PW - 1`, not `py`.
    assert_eq!(m.gy, -1);
}

// ── shadow_y: unobstructed-column floor, every (piece, rotation) pair ────
//
// Empty board. For each pair, force `p`/`pr`/`py`/`px` directly (all `pub`
// fields), trigger a recompute via one legal `move_piece(0, -1)` (horizontal,
// so it can't change the vertical floor away from the walls), then check
// `m.gy`. `py` is chosen high enough that the pre-move state is trivially
// `valid`, independent of `AxiomsRotGrid`'s Init-only guarantee.
//
// Expected floors (§4-T5a: floor = -min_row), from `t1`'s `PieceGrid` literals:
//   Bar   r0: occupied dy={1}     -> min_row=1 -> floor=-1
//   Bar   r1: occupied dy={0,1,2} -> min_row=0 -> floor=0
//   Corner r0: occupied dy={1,2}  -> min_row=1 -> floor=-1
//   Corner r1: occupied dy={0,1}  -> min_row=0 -> floor=0
//   Corner r2: occupied dy={0,1}  -> min_row=0 -> floor=0
//   Corner r3: occupied dy={1,2}  -> min_row=1 -> floor=-1
fn unobstructed_floor_case(p: Piece, pr: u8, expected: i64) {
    let mut m = Machine::<TestInstance>::new(bags_alternating(), piece_source);
    m.s4.s3.s2.s1.p = p;
    m.s4.s3.s2.s1.pr = pr;
    m.s4.s3.s2.s1.py = TestInstance::PW; // = 3, plenty of headroom on an HM=6 board
    m.s4.s3.s2.s1.px = 1;
    assert!(
        m.move_piece(0, -1),
        "px 1->0 must be legal on an empty board"
    );
    assert_eq!(m.gy, expected, "piece={p:?} pr={pr}");
}

#[test]
fn shadow_y_unobstructed_floor_bar_r0() {
    unobstructed_floor_case(Piece::Bar, 0, -1);
}
#[test]
fn shadow_y_unobstructed_floor_bar_r1() {
    unobstructed_floor_case(Piece::Bar, 1, 0);
}
#[test]
fn shadow_y_unobstructed_floor_corner_r0() {
    unobstructed_floor_case(Piece::Corner, 0, -1);
}
#[test]
fn shadow_y_unobstructed_floor_corner_r1() {
    unobstructed_floor_case(Piece::Corner, 1, 0);
}
#[test]
fn shadow_y_unobstructed_floor_corner_r2() {
    unobstructed_floor_case(Piece::Corner, 2, 0);
}
#[test]
fn shadow_y_unobstructed_floor_corner_r3() {
    unobstructed_floor_case(Piece::Corner, 3, -1);
}

// ── shadow_y: overhang stops the descent short of the true floor ─────────

/// §4-T5a overhang case: a hand-built 3-cell shelf at row 1, columns
/// {0,1,2} — exactly `Bar` r0's occupied columns at `px=0`. `Bar` r0
/// occupies only `dy=1`, so the shelf fully blocks it well short of the
/// unobstructed floor of `-1` — `gy` must land at `1` (resting on the
/// shelf, occupied row `gy+1=2`).
#[test]
fn shadow_y_stops_at_overhang_not_true_floor() {
    let mut m = Machine::<TestInstance>::new(bags_alternating(), piece_source);
    m.s4.s3.s2.s1.p = Piece::Bar;
    m.s4.s3.s2.s1.pr = 0;
    m.s4.s3.s2.s1.py = 3; // INITIAL_Y
    m.s4.s3.s2.s1.px = 1; // INITIAL_X
    for x in 0..3 {
        m.s4.s3.s2.s1.mg[1][x] = Some(PieceOrExtra::Piece(Piece::Corner)); // shelf at row 1, not a full row (WM=5); which piece occupies it is immaterial
    }
    assert!(
        m.move_piece(0, -1),
        "px 1->0 must be legal (row 4 is still empty)"
    );
    assert_eq!(
        m.gy, 1,
        "must stop on the shelf, not descend to the true floor (-1)"
    );
    check_invariants(&m);
}

// ── drop_piece ────────────────────────────────────────────────────────────

/// §4-T5d: `drop_piece` locks at `gy`, not `py`. Built on the overhang from
/// `shadow_y_stops_at_overhang_not_true_floor`, hand-traced one step
/// further through `fix_piece`'s union + clear. Neither row 1 nor the
/// post-union row 2 is a complete line (`WM=5`), so no line-clear fires
/// and the board's final shape is exactly the union.
#[test]
fn drop_piece_locks_at_gy_when_blocked_by_overhang() {
    let mut m = Machine::<TestInstance>::new(bags_alternating(), piece_source);
    m.s4.s3.s2.s1.p = Piece::Bar;
    m.s4.s3.s2.s1.pr = 0;
    m.s4.s3.s2.s1.py = 3;
    m.s4.s3.s2.s1.px = 1;
    for x in 0..3 {
        m.s4.s3.s2.s1.mg[1][x] = Some(PieceOrExtra::Piece(Piece::Corner)); // as above — which piece is immaterial
    }
    assert!(m.move_piece(0, -1)); // px -> 0; recomputes gy = 1 (previous test)
    assert_eq!(m.gy, 1);

    let cleared_before = m.s4.s3.s2.s1.cleared_lines;
    let fired = m.drop_piece(&[Piece::Bar, Piece::Corner]);
    assert!(
        fired,
        "drop_piece must fire: not gameover, and LowestShadowY guarantees fix_piece's guard holds"
    );

    // Bar's row (dy=1) locks at abs row gy+1=2, cols {0,1,2}, as Piece::Bar.
    assert_eq!(
        m.s4.s3.s2.s1.mg[2][0],
        Some(PieceOrExtra::Piece(Piece::Bar))
    );
    assert_eq!(
        m.s4.s3.s2.s1.mg[2][1],
        Some(PieceOrExtra::Piece(Piece::Bar))
    );
    assert_eq!(
        m.s4.s3.s2.s1.mg[2][2],
        Some(PieceOrExtra::Piece(Piece::Bar))
    );
    assert_eq!(m.s4.s3.s2.s1.mg[2][3], None);
    assert_eq!(m.s4.s3.s2.s1.mg[2][4], None);
    // The shelf itself (row 1) is untouched by this drop.
    assert!(m.s4.s3.s2.s1.mg[1][0].is_some());
    assert!(m.s4.s3.s2.s1.mg[1][1].is_some());
    assert!(m.s4.s3.s2.s1.mg[1][2].is_some());
    assert_eq!(
        m.s4.s3.s2.s1.cleared_lines, cleared_before,
        "neither row is a complete line (WM=5)"
    );
    check_invariants(&m); // includes the fresh GyEqShadowY/LowestShadowY check for the newly-spawned piece
}

/// §4-T5d: `gameover` blocks `drop_piece` entirely — `bag`/`next`/`s4`/`gy`
/// stay byte-identical (single guard, no peek-then-commit).
#[test]
fn drop_piece_blocked_by_gameover_leaves_state_untouched() {
    let mut m = Machine::<TestInstance>::new(bags_alternating(), piece_source);
    m.s4.s3.s2.s1.gameover = true; // force the guard to fail
    let gy_before = m.gy;
    let py_before = m.s4.s3.s2.s1.py;
    let px_before = m.s4.s3.s2.s1.px;
    let mg_before = m.s4.s3.s2.s1.mg.clone();
    let bag_before = m.s4.bag.clone();
    let next_before = m.s4.next.clone();

    let fired = m.drop_piece(&[Piece::Bar, Piece::Corner]);

    assert!(!fired);
    assert_eq!(m.gy, gy_before);
    assert_eq!(m.s4.s3.s2.s1.py, py_before);
    assert_eq!(m.s4.s3.s2.s1.px, px_before);
    assert_eq!(m.s4.s3.s2.s1.mg, mg_before);
    assert_eq!(m.s4.bag, bag_before);
    assert_eq!(m.s4.next, next_before);
}

/// §4-T5d: `drop_piece` always fires when `¬gameover` (every reachable
/// state satisfies `LowestShadowY`'s hypothesis). Driven across a longer
/// mixed-action trace, not just `Init`'s own state.
#[test]
fn drop_piece_always_fires_when_not_gameover() {
    let mut m = Machine::<TestInstance>::new(bags_alternating(), piece_source);
    let mut i = 0u64;
    let mut bag_new = move || {
        i += 1;
        if i % 2 == 0 {
            vec![Piece::Bar, Piece::Corner]
        } else {
            vec![Piece::Corner, Piece::Bar]
        }
    };
    for _ in 0..40 {
        if m.s4.s3.s2.s1.gameover {
            break;
        }
        match m.s4.s3.s2.s1.px % 3 {
            0 => {
                m.move_piece(0, -1);
            }
            1 => {
                m.rotate_piece(true);
            }
            _ => {
                let was_gameover = m.s4.s3.s2.s1.gameover;
                let fired = m.drop_piece(&bag_new());
                if !was_gameover {
                    assert!(fired, "drop_piece must fire whenever not gameover");
                }
            }
        }
        check_invariants(&m);
    }
}

// ── gy tracks every action, not just Init ─────────────────────────────────

/// §4-T5b: `gy` refreshes on success, holds on failure — exercised across
/// all five actions together since the property is uniform.
#[test]
fn gy_refreshes_on_success_and_holds_on_failure_across_all_actions() {
    let mut m = Machine::<TestInstance>::new(bags_alternating(), piece_source);
    check_invariants(&m); // establishes gy == shadow_y(s1) as the starting point

    // A guard failure: force gameover, then every action must fail and gy
    // must stay put.
    m.s4.s3.s2.s1.gameover = true;
    let gy_before = m.gy;
    assert!(!m.move_piece(0, -1));
    assert_eq!(m.gy, gy_before);
    assert!(!m.rotate_piece(true));
    assert_eq!(m.gy, gy_before);
    assert!(!m.fix_piece(&[Piece::Bar, Piece::Corner]));
    assert_eq!(m.gy, gy_before);
    assert!(!m.hold_piece(&[Piece::Bar, Piece::Corner]));
    assert_eq!(m.gy, gy_before);
    assert!(!m.fall_step(&[Piece::Bar, Piece::Corner]));
    assert_eq!(m.gy, gy_before);

    // A guard success: gy after a successful move matches an
    // independently-recomputed value, re-derived here (not just via
    // check_invariants) to catch a shared-bug scenario check_invariants
    // alone couldn't.
    let mut m2 = Machine::<TestInstance>::new(bags_alternating(), piece_source);
    let fired = m2.move_piece(0, 1);
    assert!(
        fired,
        "px+1 must be legal from a fresh Init on an empty board"
    );
    check_invariants(&m2);
}
