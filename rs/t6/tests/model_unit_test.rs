// spec: tests/model_unit_test.rs — golden vectors (§9, `implementation.md`).
//
// `t5`'s own mechanics are not re-tested here (`t5/tests/model_unit_test.rs`
// already covers them) — this file covers only what's new to T6:
// `rotate_kick_piece`.
//
// Geometry (`TestInstance`: `PW=3`, `HM=6`, `WM=5`, `FY=4`, `FX=0`,
// `INITIAL_Y=3`, `INITIAL_X=1`): `mg[y][x]`, `y` increasing upward (`y=0`
// the floor); piece grids `pg[dy][dx]` within the piece's own `PW×PW` box
// (`y = py + dy`). `Bar`'s two rotations: `r0`/`r2` (`BAR_R0`) occupy
// `dy=1`, `dx∈{0,1,2}` (horizontal); `r1`/`r3` (`BAR_R1`) occupy
// `dy∈{0,1,2}`, `dx=1` (vertical, always landing on column `px+1`
// regardless of which `px` produced it — what
// `right_kick_uses_original_px_not_chained` below exploits). `cw`
// *decrements* `pr` (wraps `0 -> 3`), per `t1::model::rotate_piece`.

#[path = "test_instance.rs"]
mod fixture;
#[path = "oracle.rs"]
mod oracle;

use fixture::{Piece, TestInstance};
use t1::model::Params as T1Params;
use t1::model::PieceOrExtra;
use t5::model::check_invariants; // t6::model does not re-export this (implementation.md §7)
use t6::model::{Machine, T6MachineExt};

fn bags_alternating() -> impl FnMut(u64) -> Vec<Piece> {
    |i: u64| {
        if i.is_multiple_of(2) {
            vec![Piece::Bar, Piece::Corner]
        } else {
            vec![Piece::Corner, Piece::Bar]
        }
    }
}

fn piece_source() -> Piece {
    Piece::Bar
}

fn fresh() -> Machine<TestInstance> {
    Machine::<TestInstance>::new(bags_alternating(), piece_source)
}

// ── exclusivity: kick never fires (or mutates) when plain rotation would ──

/// `rotate_kick_piece` must return `false` and leave every field untouched
/// whenever a plain `rotate_piece` call from the same state would have
/// fired (`implementation.md` §4-T6b's exclusivity guard, `proofs.md` §5.2).
#[test]
fn kick_does_not_fire_when_plain_rotation_would() {
    // pr=0 (horizontal) -> ccw -> pr2=1 (vertical, BAR_R1), landing column
    // px+1=1 — inside the empty WM=5 board, so plain rotation fires.
    // Reach px via move_piece(0,1) rather than hand-setting it, so gy stays
    // refreshed for that state (same idiom as
    // `t5/tests/model_unit_test.rs`'s `unobstructed_floor_case`).
    let mut probe = fresh();
    probe.s4.s3.s2.s1.p = Piece::Bar;
    probe.s4.s3.s2.s1.pr = 0;
    probe.s4.s3.s2.s1.py = 1;
    probe.s4.s3.s2.s1.px = 1;
    assert!(
        probe.move_piece(0, -1),
        "setup: px 1->0 must be legal on an empty board"
    );
    assert!(
        probe.rotate_piece(false),
        "sanity: plain ccw rotation must be unobstructed here"
    );

    let mut m = fresh();
    m.s4.s3.s2.s1.p = Piece::Bar;
    m.s4.s3.s2.s1.pr = 0;
    m.s4.s3.s2.s1.py = 1;
    m.s4.s3.s2.s1.px = 1;
    assert!(
        m.move_piece(0, -1),
        "setup: px 1->0 must be legal on an empty board"
    );
    let before = (
        m.s4.s3.s2.s1.py,
        m.s4.s3.s2.s1.px,
        m.s4.s3.s2.s1.pr,
        m.s4.s3.s2.s1.mg.clone(),
    );

    let kicked = m.rotate_kick_piece(false);

    assert!(!kicked, "kick must not fire when the plain rotation would");
    assert_eq!(m.s4.s3.s2.s1.py, before.0);
    assert_eq!(m.s4.s3.s2.s1.px, before.1);
    assert_eq!(m.s4.s3.s2.s1.pr, before.2);
    assert_eq!(m.s4.s3.s2.s1.mg, before.3);
    check_invariants(&m);
}

/// `gameover` blocks the kick unconditionally, even in a geometry where the
/// kick would otherwise plainly succeed — `T6.v`'s own `(¬gameover s) ∧ …`
/// guard conjunct, mirrored by the Rust `s1.gameover || …` early return.
#[test]
fn kick_blocked_by_gameover_leaves_state_untouched() {
    let mut m = fresh();
    m.s4.s3.s2.s1.p = Piece::Bar;
    m.s4.s3.s2.s1.pr = 3; // vertical; plain ccw would land horizontal at cols 3,4,5 — out of bounds, so a kick would normally be attempted
    m.s4.s3.s2.s1.py = 2;
    m.s4.s3.s2.s1.px = 3;
    m.s4.s3.s2.s1.gameover = true;
    let before = (
        m.s4.s3.s2.s1.py,
        m.s4.s3.s2.s1.px,
        m.s4.s3.s2.s1.pr,
        m.s4.s3.s2.s1.mg.clone(),
    );

    let kicked = m.rotate_kick_piece(false);

    assert!(!kicked);
    assert_eq!(m.s4.s3.s2.s1.py, before.0);
    assert_eq!(m.s4.s3.s2.s1.px, before.1);
    assert_eq!(m.s4.s3.s2.s1.pr, before.2);
    assert_eq!(m.s4.s3.s2.s1.mg, before.3);
    assert!(m.s4.s3.s2.s1.gameover);
}

// ── left kick fires ─────────────────────────────────────────────────────

/// Wall kick against the right wall: `Bar` at `pr=3` (vertical), `px=3`;
/// rotating ccw targets `pr=0` (horizontal, cols `px..px+2`) — at the
/// original `px=3` that's columns `{3,4,5}`, and `WM=5` only has columns
/// `0..4`, so the plain rotation fails. The left kick (`px=2`) targets
/// columns `{2,3,4}`, entirely in bounds on an empty board, and must fire.
#[test]
fn left_kick_fires_against_right_wall() {
    // Set up one column left of px=3, then move_piece(0,1) into it — reaches
    // the intended px while refreshing gy for that exact state (see the
    // previous test's comment).
    let mut probe = fresh();
    probe.s4.s3.s2.s1.p = Piece::Bar;
    probe.s4.s3.s2.s1.pr = 3;
    probe.s4.s3.s2.s1.py = 2;
    probe.s4.s3.s2.s1.px = 2;
    assert!(
        probe.move_piece(0, 1),
        "setup: px 2->3 must be legal on an empty board"
    );
    assert!(
        !probe.rotate_piece(false),
        "sanity: plain ccw rotation must be blocked by the right wall"
    );

    let mut m = fresh();
    m.s4.s3.s2.s1.p = Piece::Bar;
    m.s4.s3.s2.s1.pr = 3;
    m.s4.s3.s2.s1.py = 2;
    m.s4.s3.s2.s1.px = 2;
    assert!(
        m.move_piece(0, 1),
        "setup: px 2->3 must be legal on an empty board"
    );
    let mg_before = m.s4.s3.s2.s1.mg.clone();

    let kicked = m.rotate_kick_piece(false);

    assert!(kicked, "left kick must fire");
    assert_eq!(m.s4.s3.s2.s1.pr, 0, "rotation actually applied");
    assert_eq!(
        m.s4.s3.s2.s1.px, 2,
        "px moved by exactly -1 from the original 3"
    );
    assert_eq!(m.s4.s3.s2.s1.py, 2, "py untouched");
    assert_eq!(
        m.s4.s3.s2.s1.mg, mg_before,
        "mg untouched by a successful kick"
    );
    check_invariants(&m);
}

// ── right kick fires, computed from the ORIGINAL px, never chained ────────

/// Distinguishes a correct implementation from a *chained* one (right kick
/// computed as "failed left attempt's `px` + 1" instead of "original `px`
/// + 1", `proofs.md` §5.1/§5.4): the vertical target (`pr=3`, `BAR_R1`,
/// column `px_attempt + 1`) is blocked at the plain column (3) and the
/// left-kick column (2), but open at the *correct* right-kick column (4).
/// A chained bug computes `right_px = left_px + 1 = orig_px`, landing back
/// on the already-blocked plain column, so it would wrongly fail here.
#[test]
fn right_kick_uses_original_px_not_chained() {
    let mut m = fresh();
    m.s4.s3.s2.s1.p = Piece::Bar;
    m.s4.s3.s2.s1.pr = 0; // horizontal; cw -> pr2=3 (vertical, BAR_R1)
    m.s4.s3.s2.s1.py = 1;
    // Target (vertical) occupies abs rows py..py+2 = {1,2,3} at col = px_attempt+1.
    // Block plain (px=2 -> col 3) and left (px=1 -> col 2); leave right
    // (px=3 -> col 4) open. Row 2 is left untouched in every locked column
    // — that's where the piece's own pre-rotation horizontal cells sit
    // (abs row py+1=2), and it's also the row the refresh move below
    // traverses.
    m.s4.s3.s2.s1.mg[1][2] = Some(PieceOrExtra::Piece(Piece::Corner));
    m.s4.s3.s2.s1.mg[3][2] = Some(PieceOrExtra::Piece(Piece::Corner));
    m.s4.s3.s2.s1.mg[1][3] = Some(PieceOrExtra::Piece(Piece::Corner));
    m.s4.s3.s2.s1.mg[3][3] = Some(PieceOrExtra::Piece(Piece::Corner));
    m.s4.s3.s2.s1.px = 1; // one column left of the target px=2
    assert!(
        m.move_piece(0, 1),
        "setup: px 1->2 must be legal (row 2 unlocked); also refreshes gy"
    );

    let mut probe = fresh();
    probe.s4.s3.s2.s1.p = Piece::Bar;
    probe.s4.s3.s2.s1.pr = 0;
    probe.s4.s3.s2.s1.py = 1;
    probe.s4.s3.s2.s1.mg[1][2] = Some(PieceOrExtra::Piece(Piece::Corner));
    probe.s4.s3.s2.s1.mg[3][2] = Some(PieceOrExtra::Piece(Piece::Corner));
    probe.s4.s3.s2.s1.mg[1][3] = Some(PieceOrExtra::Piece(Piece::Corner));
    probe.s4.s3.s2.s1.mg[3][3] = Some(PieceOrExtra::Piece(Piece::Corner));
    probe.s4.s3.s2.s1.px = 1;
    assert!(probe.move_piece(0, 1));
    assert!(
        !probe.rotate_piece(true),
        "sanity: plain cw rotation must be blocked (col 3 locked)"
    );

    let mg_before = m.s4.s3.s2.s1.mg.clone();
    let kicked = m.rotate_kick_piece(true);

    assert!(
        kicked,
        "right kick must succeed via the ORIGINAL px+1=3 (abs col 4, open)"
    );
    assert_eq!(
        m.s4.s3.s2.s1.pr, 3,
        "rotation applied (cw: pr wraps 0 -> 3)"
    );
    assert_eq!(
        m.s4.s3.s2.s1.px, 3,
        "px moved by exactly +1 from the ORIGINAL px, not from the failed left attempt's px"
    );
    assert_eq!(m.s4.s3.s2.s1.py, 1);
    assert_eq!(
        m.s4.s3.s2.s1.mg, mg_before,
        "mg untouched by a successful kick"
    );
    check_invariants(&m);
}

// ── both kicks fail: px restored exactly, nothing else mutated ───────────

/// Same column layout as `right_kick_uses_original_px_not_chained`, plus
/// the right-kick column (4) also locked — now all three attempts fail,
/// and `px` must come back to exactly its original value
/// (`implementation.md` §4-T6b's restore step; `proofs.md` §5.5 — not
/// defensive housekeeping, required for the "guard fails ⟹ stutter"
/// correspondence).
#[test]
fn both_kicks_fail_restores_px_exactly() {
    let mut m = fresh();
    m.s4.s3.s2.s1.p = Piece::Bar;
    m.s4.s3.s2.s1.pr = 0;
    m.s4.s3.s2.s1.py = 1;
    for &col in &[2usize, 3, 4] {
        m.s4.s3.s2.s1.mg[1][col] = Some(PieceOrExtra::Piece(Piece::Corner));
        m.s4.s3.s2.s1.mg[3][col] = Some(PieceOrExtra::Piece(Piece::Corner));
    }
    m.s4.s3.s2.s1.px = 1; // one column left of the target px=2
    assert!(
        m.move_piece(0, 1),
        "setup: px 1->2 must be legal (row 2 unlocked); also refreshes gy"
    );

    let before = (
        m.s4.s3.s2.s1.py,
        m.s4.s3.s2.s1.px,
        m.s4.s3.s2.s1.pr,
        m.s4.s3.s2.s1.p,
        m.s4.s3.s2.s1.gameover,
        m.s4.s3.s2.s1.mg.clone(),
    );

    let kicked = m.rotate_kick_piece(true);

    assert!(
        !kicked,
        "all three attempts (plain, left, right) must fail — cols 2, 3, 4 all locked"
    );
    assert_eq!(m.s4.s3.s2.s1.py, before.0);
    assert_eq!(
        m.s4.s3.s2.s1.px, before.1,
        "px must be restored to exactly its original value"
    );
    assert_eq!(m.s4.s3.s2.s1.pr, before.2);
    assert_eq!(m.s4.s3.s2.s1.p, before.3);
    assert_eq!(m.s4.s3.s2.s1.gameover, before.4);
    assert_eq!(m.s4.s3.s2.s1.mg, before.5);
    check_invariants(&m);
}

// ── differential: at least one hand-traced case agrees with oracle.rs ─────

/// Ties `oracle.rs` to a concrete, independently-verifiable case: the same
/// scenario as `left_kick_fires_against_right_wall`, cross-checked against
/// `oracle_rotate_kick_piece`'s own from-scratch computation.
#[test]
fn left_kick_case_matches_independent_oracle() {
    let rot_grids: Vec<Vec<Vec<Option<Piece>>>> = (0..4u8)
        .map(|r| TestInstance::rot_grid(Piece::Bar, r).clone())
        .collect();
    let mg: Vec<Vec<Option<PieceOrExtra<TestInstance>>>> = vec![vec![None; 5]; 6];
    let expected = oracle::oracle_rotate_kick_piece(false, &mg, &rot_grids, 2, 3, 3, false);
    assert_eq!(expected, Some((2, 2, 0)));

    let mut m = fresh();
    m.s4.s3.s2.s1.p = Piece::Bar;
    m.s4.s3.s2.s1.pr = 3;
    m.s4.s3.s2.s1.py = 2;
    m.s4.s3.s2.s1.px = 3;
    assert!(m.rotate_kick_piece(false));
    assert_eq!(
        (m.s4.s3.s2.s1.py, m.s4.s3.s2.s1.px, m.s4.s3.s2.s1.pr),
        expected.unwrap()
    );
}
