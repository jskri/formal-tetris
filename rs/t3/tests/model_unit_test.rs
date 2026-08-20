//! spec: tests/model_unit_test.rs — §9, `implementation.md`.

#[path = "test_instance.rs"]
mod fixture;

use fixture::{Piece as TPiece, TestInstance};
use t1::model::Params;
use t3::model::{self, Machine};

// ── Helpers ────────────────────────────────────────────────────────────
//
// `Machine`'s public fields (D-Rust2's rationale, unchanged through every
// wrapper layer) let tests construct exact scenarios directly rather than
// simulating a full drop.

fn rest_current_piece_at_row0(m: &mut Machine<TestInstance>) {
    m.s2.s1.py = -1;
    m.s2.s1.px = 0;
    m.s2.s1.pr = 0;
    assert!(!m.s2.s1.gameover);
    assert!(
        !t1::model::can_move_piece(-1, 0, &m.s2.s1),
        "fix_piece's guard requires the piece to be blocked from moving down"
    );
}

// ── hold_piece: req-hold-empty ────────────────────────────────────────

#[test]
fn hold_from_empty_uses_p_new() {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    assert_eq!(m.hold, None);
    assert!(m.hold_piece(TPiece::Corner));
    assert_eq!(m.s2.s1.p, TPiece::Corner, "new current piece is p_new");
    assert_eq!(
        m.hold,
        Some(TPiece::Bar),
        "hold becomes the old current piece"
    );
    assert!(m.swapped);
}

// ── hold_piece: req-hold-swap ──────────────────────────────────────────

#[test]
fn hold_when_occupied_swaps() {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    assert!(m.hold_piece(TPiece::Corner)); // hold: None -> Some(Bar); current: Corner; swapped: true
    assert_eq!(m.hold, Some(TPiece::Bar));
    assert_eq!(m.s2.s1.p, TPiece::Corner);

    rest_current_piece_at_row0(&mut m);
    assert!(m.fix_piece(TPiece::Bar)); // resets swapped; new current piece is the fix's p_new
    assert!(!m.swapped);
    assert_eq!(m.s2.s1.p, TPiece::Bar);

    // set up an unambiguous swap: hold=Some(Corner), current=Bar.
    m.hold = Some(TPiece::Corner);
    assert!(m.hold_piece(TPiece::Bar));
    assert_eq!(
        m.s2.s1.p,
        TPiece::Corner,
        "current becomes the previously-held piece"
    );
    assert_eq!(
        m.hold,
        Some(TPiece::Bar),
        "hold becomes the old current piece"
    );
}

// ── hold_piece: req-hold-limit ─────────────────────────────────────────

#[test]
fn second_hold_before_a_fix_fails() {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    assert!(m.hold_piece(TPiece::Corner));
    let (p_before, hold_before, swapped_before) = (m.s2.s1.p, m.hold, m.swapped);
    let mg_before = m.s2.s1.mg.clone();

    assert!(
        !m.hold_piece(TPiece::Bar),
        "a second hold before an intervening fix must stutter"
    );

    assert_eq!(m.s2.s1.p, p_before);
    assert_eq!(m.hold, hold_before);
    assert_eq!(m.swapped, swapped_before);
    assert_eq!(m.s2.s1.mg, mg_before);
}

#[test]
fn a_fix_resets_swapped_and_reenables_hold() {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    assert!(m.hold_piece(TPiece::Corner)); // current piece is now Corner; swapped: true
    rest_current_piece_at_row0(&mut m);
    assert!(m.fix_piece(TPiece::Bar));
    assert!(!m.swapped, "fixing re-enables holding (req-hold-limit)");
    assert!(
        m.hold_piece(TPiece::Corner),
        "hold succeeds again after the fix"
    );
}

// ── hold_piece: blocked by gameover ────────────────────────────────────

#[test]
fn hold_is_blocked_when_gameover() {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    m.s2.s1.gameover = true;
    assert!(!m.hold_piece(TPiece::Corner));
    assert_eq!(m.hold, None);
    assert!(!m.swapped);
}

// ── narrow-blast-radius: a firing hold changes only p/py/px/pr and hold/swapped ──

#[test]
fn firing_hold_changes_only_the_narrow_field_set() {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    m.s2.score = 42;
    m.s2.level = 3;
    m.s2.combo = 1;
    m.s2.perfect_clear = true;
    m.s2.total_cleared_lines = 9;

    let mg_before = m.s2.s1.mg.clone();
    let gameover_before = m.s2.s1.gameover;
    let cleared_lines_before = m.s2.s1.cleared_lines;
    let score_before = m.s2.score;
    let level_before = m.s2.level;
    let combo_before = m.s2.combo;
    let perfect_clear_before = m.s2.perfect_clear;
    let total_before = m.s2.total_cleared_lines;

    assert!(m.hold_piece(TPiece::Corner));

    assert_eq!(m.s2.s1.mg, mg_before, "mg must be byte-identical");
    assert_eq!(
        m.s2.s1.gameover, gameover_before,
        "s1.gameover must be unchanged"
    );
    assert_eq!(
        m.s2.s1.cleared_lines, cleared_lines_before,
        "s1.cleared_lines must be unchanged"
    );
    assert_eq!(m.s2.score, score_before, "score must be unchanged");
    assert_eq!(m.s2.level, level_before, "level must be unchanged");
    assert_eq!(m.s2.combo, combo_before, "combo must be unchanged");
    assert_eq!(
        m.s2.perfect_clear, perfect_clear_before,
        "perfect_clear must be unchanged"
    );
    assert_eq!(
        m.s2.total_cleared_lines, total_before,
        "total_cleared_lines must be unchanged"
    );
}

// ── spawn position after a hold matches a fix's respawn ────────────────

#[test]
fn spawn_position_after_hold_matches_initial_yx() {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    assert!(m.hold_piece(TPiece::Corner));
    assert_eq!(m.s2.s1.py, TestInstance::initial_y(TPiece::Corner));
    assert_eq!(m.s2.s1.px, TestInstance::initial_x(TPiece::Corner));
    assert_eq!(m.s2.s1.pr, 0);
}

// ── check_invariants (SwappedImplyHoldSome, GameoverImplyNotSwapped) ───

#[test]
fn check_invariants_passes_on_a_fresh_machine() {
    let m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    model::check_invariants(&m); // must not panic
}

#[test]
fn check_invariants_passes_after_a_hold() {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    assert!(m.hold_piece(TPiece::Corner));
    model::check_invariants(&m);
}

#[test]
#[should_panic]
fn check_invariants_catches_a_broken_swapped_imply_hold_some() {
    let mut m = Machine::<TestInstance>::new(TPiece::Bar, fixture::piece_source_stub());
    m.swapped = true; // violates SwappedImplyHoldSome: hold is still None
    model::check_invariants(&m);
}
