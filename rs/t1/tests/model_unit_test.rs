//! spec: tests/model_unit_test.rs — §9.1, `implementation.md`.

#[path = "test_instance.rs"]
mod fixture;

use fixture::{Piece as TPiece, TestInstance};
use t1::instance::Tetris;
use t1::model::{self, occupied_inside, valid, Machine, Params, PieceOrExtra};

// ── rot_grid ─────────────────────────────────────────────────────────────

#[test]
fn rot_grid_dims_and_occupancy_real_instance() {
    for &p in Tetris::piece_all() {
        for r in 0..4u8 {
            let g = Tetris::rot_grid(p, r);
            assert_eq!(g.len(), Tetris::PW as usize, "{p:?} r{r}: height");
            for row in g {
                assert_eq!(row.len(), Tetris::PW as usize, "{p:?} r{r}: width");
            }
            // domain fact: every tetromino covers exactly 4 cells
            let occupied = g.iter().flatten().filter(|c| c.is_some()).count();
            assert_eq!(occupied, 4, "{p:?} r{r}: occupied-cell count");
        }
    }
}

#[test]
fn rot_grid_four_rotations_return_to_start() {
    // TestInstance (not Tetris): every rotation is valid from spawn by
    // construction, unlike on the real instance (e.g. vertical `I` needs
    // headroom `HM`/`InitialY` doesn't leave). So this only claims `pr`
    // wraps to 0 after 4 valid rotations, for a fixture where that holds.
    for &p in TestInstance::piece_all() {
        let original = TestInstance::rot_grid(p, 0).clone();
        let mut m = Machine::<TestInstance>::new(p, fixture::piece_source_stub());
        for _ in 0..4 {
            assert!(
                m.rotate_piece(true),
                "{p:?}: rotation should be valid from spawn"
            );
        }
        assert_eq!(
            m.pr, 0,
            "{p:?}: pr should wrap back to 0 after 4 quarter turns"
        );
        assert_eq!(
            TestInstance::rot_grid(p, m.pr),
            &original,
            "{p:?}: grid after a full cycle should match the start"
        );
    }
}

// ── fix_piece line-clearing ──────────────────────────────────────────────
//
// TestInstance's board is 6 rows × 5 columns. Every scenario below rests
// `Bar` (row 0, columns 0..3) on the floor first (`py = -1`, checked
// below: its only occupied local row is `y_local = 1`, so one more step
// down would place it at out-of-bounds `y = -1`), then seeds `mg`'s other
// cells directly. D-Rust2: fields are public, so tests can do this
// without simulating a full drop.

fn bar_at_rest() -> Machine<TestInstance> {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    m.py = -1;
    m.px = 0;
    assert!(!m.gameover);
    assert!(
        !model::can_move_piece(-1, 0, &m),
        "fix_piece's guard requires the piece to be blocked from moving down"
    );
    m
}

fn full_row() -> Vec<Option<PieceOrExtra<TestInstance>>> {
    vec![Some(PieceOrExtra::Piece(TPiece::Corner)); 5]
}

fn empty_row() -> Vec<Option<PieceOrExtra<TestInstance>>> {
    vec![None; 5]
}

#[test]
fn fix_piece_empty_grid_no_clear() {
    let mut m = bar_at_rest(); // mg already all-`None` from Machine::new
    assert!(m.fix_piece(TPiece::Corner));
    assert_eq!(m.cleared_lines, 0);
    // the piece's own 3 cells are locked in, nothing else
    assert_eq!(m.mg[0][0], Some(PieceOrExtra::Piece(TPiece::Bar)));
    assert_eq!(m.mg[0][1], Some(PieceOrExtra::Piece(TPiece::Bar)));
    assert_eq!(m.mg[0][2], Some(PieceOrExtra::Piece(TPiece::Bar)));
    assert_eq!(m.mg[0][3], None);
    assert_eq!(m.mg[0][4], None);
}

#[test]
fn fix_piece_one_full_line_bottom() {
    let mut m = bar_at_rest();
    // pre-fill row 0's two columns the piece doesn't touch
    m.mg[0][3] = Some(PieceOrExtra::Piece(TPiece::Corner));
    m.mg[0][4] = Some(PieceOrExtra::Piece(TPiece::Corner));
    assert!(m.fix_piece(TPiece::Corner));
    assert_eq!(m.cleared_lines, 1);
    // row 0 was cleared; every row shifted down one, a fresh empty row
    // appears at the top (index HM-1 = 5)
    for row in &m.mg {
        assert_eq!(row.len(), 5);
    }
    assert_eq!(m.mg[5], empty_row());
}

#[test]
fn fix_piece_one_full_line_middle() {
    let mut m = bar_at_rest();
    m.mg[2] = full_row(); // untouched by the piece (piece rests on row 0)
    assert!(m.fix_piece(TPiece::Corner));
    assert_eq!(m.cleared_lines, 1);
    assert_eq!(m.mg[5], empty_row());
    // rows above the cleared one shifted down; row 0 (the piece) survives
    assert_eq!(m.mg[0][0], Some(PieceOrExtra::Piece(TPiece::Bar)));
}

#[test]
fn fix_piece_one_full_line_top() {
    let mut m = bar_at_rest();
    m.mg[5] = full_row(); // top row (index HM-1)
    assert!(m.fix_piece(TPiece::Corner));
    assert_eq!(m.cleared_lines, 1);
    assert_eq!(m.mg[5], empty_row());
}

#[test]
fn fix_piece_several_full_lines() {
    let mut m = bar_at_rest();
    m.mg[2] = full_row();
    m.mg[4] = full_row();
    assert!(m.fix_piece(TPiece::Corner));
    assert_eq!(m.cleared_lines, 2);
    assert_eq!(m.mg[4], empty_row());
    assert_eq!(m.mg[5], empty_row());
    assert_eq!(m.mg[0][0], Some(PieceOrExtra::Piece(TPiece::Bar))); // survives, still at the bottom
}

#[test]
fn fix_piece_all_lines_full() {
    let mut m = bar_at_rest();
    for y in 1..6 {
        m.mg[y] = full_row();
    }
    m.mg[0][3] = Some(PieceOrExtra::Piece(TPiece::Corner));
    m.mg[0][4] = Some(PieceOrExtra::Piece(TPiece::Corner)); // completes row 0 once the piece overlays cols 0..3
    assert!(m.fix_piece(TPiece::Corner));
    assert_eq!(m.cleared_lines, 6);
    for row in &m.mg {
        assert_eq!(row, &empty_row());
    }
}

#[test]
fn fix_piece_none_full() {
    let mut m = bar_at_rest();
    m.mg[2][0] = Some(PieceOrExtra::Piece(TPiece::Corner));
    m.mg[2][1] = Some(PieceOrExtra::Piece(TPiece::Corner)); // row 2: 2/5 filled, not full
    m.mg[4][4] = Some(PieceOrExtra::Piece(TPiece::Corner)); // row 4: 1/5 filled, not full
    assert!(m.fix_piece(TPiece::Corner));
    assert_eq!(m.cleared_lines, 0);
    // nothing removed: pre-existing content survives exactly, plus the piece
    assert_eq!(m.mg[2][0], Some(PieceOrExtra::Piece(TPiece::Corner)));
    assert_eq!(m.mg[2][1], Some(PieceOrExtra::Piece(TPiece::Corner)));
    assert_eq!(m.mg[4][4], Some(PieceOrExtra::Piece(TPiece::Corner)));
    assert_eq!(m.mg[0][0], Some(PieceOrExtra::Piece(TPiece::Bar)));
}

// ── intersect/occupied_inside/valid boundary cases ──────────────────────

#[test]
fn occupied_inside_boundaries() {
    // a single-occupied-cell 1x1 grid at origin (0,0)
    let dot = vec![vec![true]];
    let target = vec![vec![false; 3]; 3]; // 3x3 box, content irrelevant to occupied_inside

    // exactly at the low boundary: inside
    assert!(occupied_inside(&dot, 0, 0, &target, 0, 0));
    // exactly at the high boundary (`= H`/`= W`): outside
    assert!(!occupied_inside(&dot, 3, 0, &target, 0, 0));
    assert!(!occupied_inside(&dot, 0, 3, &target, 0, 0));
    // negative offset landing outside: outside, no panic (D9: guard before
    // any `as usize` cast)
    assert!(!occupied_inside(&dot, -1, 0, &target, 0, 0));
    assert!(!occupied_inside(&dot, 0, -1, &target, 0, 0));
    // negative offset that still lands inside a larger/shifted target: inside
    assert!(occupied_inside(&dot, -1, -1, &target, -1, -1));
}

#[test]
fn intersect_boundaries() {
    let dot = vec![vec![true]];
    let one_true_cell = {
        let mut g = vec![vec![false; 3]; 3];
        g[2][2] = true; // bottom-right corner cell of a 3x3 grid at origin (0,0)
        g
    };
    // dot placed exactly on the occupied cell: intersects
    assert!(model::intersect(&dot, 2, 2, &one_true_cell, 0, 0));
    // dot placed one cell off (still in-box): no intersection
    assert!(!model::intersect(&dot, 1, 2, &one_true_cell, 0, 0));
    // dot placed at a negative coordinate entirely outside the target's
    // box: no intersection, no panic
    assert!(!model::intersect(&dot, -5, -5, &one_true_cell, 0, 0));
    // dot placed exactly at the target's high boundary (`= H`, `= W`): no
    // intersection (out of box)
    assert!(!model::intersect(&dot, 3, 0, &one_true_cell, 0, 0));
}

#[test]
fn valid_boundary_at_spawn() {
    let m = Machine::<TestInstance>::new(TPiece::Corner, fixture::piece_source_stub());
    // the spawn position is valid by `Machine::new`'s own postcondition
    assert!(valid::<TestInstance, _>(&m.mg, m.p, m.py, m.px, m.pr));
    // pushed far outside the board on every axis: never valid, never panics
    assert!(!valid::<TestInstance, _>(&m.mg, m.p, -1000, -1000, m.pr));
    assert!(!valid::<TestInstance, _>(&m.mg, m.p, 1000, 1000, m.pr));
}

// ── rem_euclid table (D4) ────────────────────────────────────────────────

#[test]
fn rem_euclid_table() {
    let table: [(i64, i64); 6] = [(-1, 3), (0, 0), (1, 1), (2, 2), (3, 3), (4, 0)];
    for (n, expected) in table {
        assert_eq!(n.rem_euclid(4), expected, "{n}.rem_euclid(4)");
    }
}

// ── move_piece / rotate_piece / fix_piece / fall_step guard + success ────

#[test]
fn move_piece_guard_and_success() {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    let (py0, px0) = (m.py, m.px);

    // invalid direction (not one of the three allowed deltas): guard fails
    assert!(!m.move_piece(1, 0)); // upward is never a legal move
    assert_eq!((m.py, m.px), (py0, px0));

    // valid direction, valid destination: succeeds
    assert!(m.move_piece(0, 1));
    assert_eq!((m.py, m.px), (py0, px0 + 1));

    // walk off the left edge: eventually the guard fails and nothing moves
    let mut m2 = Machine::<TestInstance>::new(TPiece::Corner, fixture::piece_source_stub());
    let mut steps = 0;
    while m2.move_piece(0, -1) {
        steps += 1;
        assert!(steps < 100, "should not be able to move left forever");
    }
    let stuck_px = m2.px;
    assert!(!m2.move_piece(0, -1));
    assert_eq!(m2.px, stuck_px);
}

#[test]
fn move_piece_guard_fails_when_gameover() {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    m.gameover = true;
    let (py0, px0) = (m.py, m.px);
    assert!(!m.move_piece(0, 1));
    assert_eq!((m.py, m.px), (py0, px0));
}

#[test]
fn rotate_piece_guard_and_success() {
    let mut m = Machine::<TestInstance>::new(TPiece::Corner, fixture::piece_source_stub());
    assert!(m.rotate_piece(true));
    assert_eq!(m.pr, 3); // cw: 0 -> (0-1).rem_euclid(4) = 3

    m.gameover = true;
    assert!(!m.rotate_piece(true));
    assert_eq!(m.pr, 3); // unchanged
}

#[test]
fn fix_piece_guard_fails_when_still_movable() {
    // fresh spawn: nothing below it, so it can still move down
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    assert!(!m.fix_piece(TPiece::Corner));
    assert_eq!(m.p, TPiece::Bar); // unchanged
}

#[test]
fn fall_step_moves_then_fixes() {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    let start_py = m.py;
    // first fall_step: should move down one row (mg is empty, floor is far)
    assert!(m.fall_step(TPiece::Corner));
    assert_eq!(m.py, start_py - 1);
    assert_eq!(m.p, TPiece::Bar); // still the same piece: this was a move, not a fix

    // drive it all the way to the floor
    while m.py > -1 {
        assert!(m.fall_step(TPiece::Corner));
    }
    // one more: now blocked, so this call fixes instead of moving
    assert!(m.fall_step(TPiece::Corner));
    assert_eq!(m.p, TPiece::Corner); // fixed and replaced
}
