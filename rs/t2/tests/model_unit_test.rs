//! spec: tests/model_unit_test.rs — §9, `implementation.md`.

#[path = "test_instance.rs"]
mod fixture;

use fixture::{Piece as TPiece, TestInstance};
use t1::model::PieceOrExtra;
use t2::model::{self, Machine};

// ── LineClearPoints / ComboPoints / PerfectClearPoints / Points ──────────

#[test]
fn line_clear_points_table() {
    // (cleared_lines, level) -> expected
    let table: [(u64, u64, u64); 8] = [
        (0, 1, 0),
        (1, 1, 100),
        (2, 1, 300),
        (3, 1, 500),
        (4, 1, 800),
        (5, 1, 800), // saturates at the "_" arm, same as 4
        (1, 3, 300),
        (4, 3, 2400),
    ];
    for (cleared_lines, level, expected) in table {
        assert_eq!(
            model::line_clear_points(cleared_lines, level),
            expected,
            "line_clear_points({cleared_lines}, {level})"
        );
    }
}

#[test]
fn combo_points_table() {
    let table: [(u64, u64, u64); 6] = [
        (1, 0, 0),  // no combo: 0 regardless of level
        (1, 1, 50), // combo=1: the "2-hit" scoring value (§4-T2b)
        (1, 2, 100),
        (3, 1, 150),
        (3, 2, 300),
        (5, 0, 0),
    ];
    for (level, combo, expected) in table {
        assert_eq!(
            model::combo_points(level, combo),
            expected,
            "combo_points({level}, {combo})"
        );
    }
}

#[test]
fn perfect_clear_points_table() {
    let table: [(bool, u64, u64, u64); 8] = [
        (false, 1, 1, 0),
        (false, 4, 5, 0), // never awarded when perfect_clear is false, any level/cleared_lines
        (true, 0, 1, 0),
        (true, 1, 1, 800),
        (true, 2, 1, 1200),
        (true, 3, 1, 1800),
        (true, 4, 1, 2000),
        (true, 1, 3, 2400),
    ];
    for (perfect_clear, cleared_lines, level, expected) in table {
        assert_eq!(
            model::perfect_clear_points(perfect_clear, cleared_lines, level),
            expected,
            "perfect_clear_points({perfect_clear}, {cleared_lines}, {level})"
        );
    }
}

#[test]
fn points_sums_the_three_components() {
    // level=2, cleared_lines=2 (=300*2=600), combo=1 (=50*1*2=100), perfect_clear
    // (=1200*2=2400): 600+100+2400 = 3100
    assert_eq!(model::points(2, 2, 1, true), 3100);
    // no clear, no combo: every component is 0 (LineClearPoints(0,_)=0,
    // ComboPoints(_,0)=0, PerfectClearPoints(_,0,_)=0)
    assert_eq!(model::points(0, 5, 0, true), 0);
    // clear, no combo, no perfect clear
    assert_eq!(model::points(1, 4, 0, false), 400);
}

// ── EmptyGridb ─────────────────────────────────────────────────────────

#[test]
fn empty_gridb_true_for_all_none() {
    let g: Vec<Vec<Option<TPiece>>> = vec![vec![None; 5]; 6];
    assert!(model::empty_gridb(&g));
}

#[test]
fn empty_gridb_false_for_one_occupied_cell() {
    let mut g: Vec<Vec<Option<TPiece>>> = vec![vec![None; 5]; 6];
    g[3][2] = Some(TPiece::Corner);
    assert!(!model::empty_gridb(&g));
}

#[test]
fn empty_gridb_true_for_empty_grid() {
    let g: Vec<Vec<Option<TPiece>>> = vec![];
    assert!(model::empty_gridb(&g));
}

// ── fix_piece: score/level/combo/perfectClear/totalClearedLines ─────────
//
// TestInstance's board is 6 rows × 5 columns, PW=3 (tests/test_instance.rs).
// `Bar`'s r0 occupies the middle local row, so resting it at `py=-1, px=0`
// places its three cells at absolute row 0, columns 0..3 — same
// construction as t1's `bar_at_rest`, via `t2::model::Machine`'s public
// `s1` field (D-Rust2).

fn rest_bar_at_row0(m: &mut Machine<TestInstance>) {
    m.s1.p = TPiece::Bar;
    m.s1.py = -1;
    m.s1.px = 0;
    m.s1.pr = 0;
    assert!(!m.s1.gameover);
    assert!(
        !t1::model::can_move_piece(-1, 0, &m.s1),
        "fix_piece's guard requires the piece to be blocked from moving down"
    );
}

fn bar_at_rest() -> Machine<TestInstance> {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    rest_bar_at_row0(&mut m);
    m
}

#[test]
fn fix_piece_no_clear_no_score_resets_combo() {
    let mut m = bar_at_rest();
    m.combo = 2; // simulate mid-streak (fields are public exactly for this, D-Rust2)
    m.score = 500;
    assert!(m.fix_piece(TPiece::Corner)); // mg is otherwise empty: no full line
    assert_eq!(m.s1.cleared_lines, 0);
    assert_eq!(m.combo, 0, "combo resets on a non-clearing fix");
    assert_eq!(
        m.score, 500,
        "Points(0, ..) == 0 regardless of level/combo/perfectClear"
    );
    assert_eq!(m.total_cleared_lines, 0);
    assert_eq!(m.level, 1);
    assert!(!m.perfect_clear);
}

#[test]
fn fix_piece_single_clear_not_perfect() {
    let mut m = bar_at_rest();
    m.s1.mg[0][3] = Some(PieceOrExtra::Piece(TPiece::Corner));
    m.s1.mg[0][4] = Some(PieceOrExtra::Piece(TPiece::Corner)); // completes row 0 with the bar's 3 cells
    m.s1.mg[2][0] = Some(PieceOrExtra::Piece(TPiece::Corner)); // keeps the board non-empty after the clear
    assert!(m.fix_piece(TPiece::Corner));
    assert_eq!(m.s1.cleared_lines, 1);
    assert!(!m.perfect_clear);
    assert_eq!(
        m.combo, 1,
        "first clear of a streak: stored combo is 1, not yet a displayed combo"
    );
    // LineClearPoints(1,1)=100 + ComboPoints(1, combo'-1=0)=0 + PerfectClearPoints(false,..)=0
    assert_eq!(m.score, 100);
    assert_eq!(m.total_cleared_lines, 1);
    assert_eq!(m.level, 1); // 1 + 1/10
}

#[test]
fn fix_piece_single_clear_perfect() {
    let mut m = bar_at_rest();
    m.s1.mg[0][3] = Some(PieceOrExtra::Piece(TPiece::Corner));
    m.s1.mg[0][4] = Some(PieceOrExtra::Piece(TPiece::Corner)); // nothing else on the board
    assert!(m.fix_piece(TPiece::Corner));
    assert_eq!(m.s1.cleared_lines, 1);
    assert!(m.perfect_clear);
    // LineClearPoints(1,1)=100 + ComboPoints(1,0)=0 + PerfectClearPoints(true,1,1)=800
    assert_eq!(m.score, 900);
}

#[test]
fn fix_piece_combo_streak_across_two_clears() {
    let mut m = bar_at_rest();
    m.s1.mg[0][3] = Some(PieceOrExtra::Piece(TPiece::Corner));
    m.s1.mg[0][4] = Some(PieceOrExtra::Piece(TPiece::Corner));
    m.s1.mg[2][0] = Some(PieceOrExtra::Piece(TPiece::Corner)); // keep the board non-empty throughout
    assert!(m.fix_piece(TPiece::Corner));
    assert_eq!(m.combo, 1);
    assert_eq!(m.score, 100); // first clear: no combo bonus yet

    // second consecutive clearing fix: the shifted board leaves row 0 empty
    // again (its only occupied row was just cleared), so the bar rests
    // there once more.
    rest_bar_at_row0(&mut m);
    m.s1.mg[0][3] = Some(PieceOrExtra::Piece(TPiece::Corner));
    m.s1.mg[0][4] = Some(PieceOrExtra::Piece(TPiece::Corner));
    assert!(m.fix_piece(TPiece::Corner));
    assert_eq!(m.s1.cleared_lines, 1);
    assert_eq!(m.combo, 2, "second consecutive clear");
    // LineClearPoints(1,1)=100 + ComboPoints(1, combo'-1=1)=50
    assert_eq!(m.score, 100 + 150);
    assert_eq!(m.total_cleared_lines, 2);
    assert_eq!(m.level, 1); // 1 + 2/10
}

#[test]
fn fix_piece_guard_fails_when_still_movable() {
    // fresh spawn: nothing below it, so it can still move down — no T2
    // field changes on a guard failure (option_map None ⇒ untouched)
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    assert!(!m.fix_piece(TPiece::Corner));
    assert_eq!(m.score, 0);
    assert_eq!(m.level, 1);
    assert_eq!(m.combo, 0);
    assert!(!m.perfect_clear);
    assert_eq!(m.total_cleared_lines, 0);
}

#[test]
fn level_rises_after_ten_cleared_lines() {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    for i in 0..10 {
        rest_bar_at_row0(&mut m);
        m.s1.mg[0][3] = Some(PieceOrExtra::Piece(TPiece::Corner));
        m.s1.mg[0][4] = Some(PieceOrExtra::Piece(TPiece::Corner));
        assert!(m.fix_piece(TPiece::Corner), "clear #{i}");
        assert_eq!(m.s1.cleared_lines, 1, "clear #{i}");
    }
    assert_eq!(m.total_cleared_lines, 10);
    assert_eq!(m.level, 2); // 1 + 10/10
}

// ── move_piece / rotate_piece: full delegation, T2 fields untouched ─────

#[test]
fn move_and_rotate_leave_t2_fields_untouched() {
    let mut m = Machine::<TestInstance>::new(TPiece::Corner, fixture::piece_source_stub());
    m.score = 42;
    m.level = 3;
    m.combo = 1;
    m.perfect_clear = true;
    m.total_cleared_lines = 9;

    assert!(m.move_piece(0, 1));
    assert!(m.rotate_piece(true));
    // a failing call (invalid direction) must also leave the fields alone
    assert!(!m.move_piece(1, 0));

    assert_eq!(m.score, 42);
    assert_eq!(m.level, 3);
    assert_eq!(m.combo, 1);
    assert!(m.perfect_clear);
    assert_eq!(m.total_cleared_lines, 9);
}

// ── check_invariants (LevelCorrect, delegated t1::model::check_invariants) ─

#[test]
fn check_invariants_passes_on_a_fresh_machine() {
    let m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    model::check_invariants(&m); // must not panic
}

#[test]
#[should_panic]
fn check_invariants_catches_a_broken_level_correct() {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    m.level = 999; // violates LevelCorrect (level == 1 + total_cleared_lines/10)
    model::check_invariants(&m);
}
