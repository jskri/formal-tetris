// spec: tests/model_unit_test.rs — golden vectors (§9, `implementation.md`).
//
// Covers only what's new to T7; `t6`'s own single-player mechanics are
// exercised by `t6/tests/model_unit_test.rs`.
//
// Geometry (`TestInstance`: `PW=3`, `HM=6`, `WM=5`, `FY=4`, `FX=0`,
// `INITIAL_Y=3`, `INITIAL_X=1`): `mg[y][x]`, `y` increasing upward (`y=0`
// the floor). `Bar`'s `r0` occupies local row `dy=1` only, so on an empty
// board it drops all the way to absolute row `0` (`gy = -1`), landing at
// columns `px..px+2`.

#[path = "test_instance.rs"]
mod fixture;
#[path = "oracle.rs"]
mod oracle;

use fixture::{Piece, TestInstance, PLAYER_COUNT};
use t1::model::PieceOrExtra;
use t7::model::{
    check_invariants, gen_rem_garbage, generated_garbage, next_target, Garbage, Machine,
};

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

fn fresh(my_index: usize, player_count: usize) -> Machine<TestInstance> {
    Machine::<TestInstance>::new(my_index, player_count, bags_alternating(), piece_source)
}

fn no_holes() -> impl Fn(i64) -> i64 {
    |_y| 2 // constant hole column, well inside WM=5
}

// ── generated_garbage / gen_rem_garbage: golden truth table ─────────────

#[test]
fn generated_garbage_truth_table() {
    // spec: GeneratedGarbage — req-multi-garbage-gen
    assert_eq!(generated_garbage(0, false), 0); // 0 < 4: 0-1 -> max(0,-1) = 0
    assert_eq!(generated_garbage(1, false), 0); // 1-1 = 0
    assert_eq!(generated_garbage(2, false), 1);
    assert_eq!(generated_garbage(3, false), 2);
    assert_eq!(generated_garbage(4, false), 4); // >= 4: no -1
    assert_eq!(generated_garbage(5, false), 5);
    assert_eq!(generated_garbage(0, true), 10); // perfect clear special garbage
    assert_eq!(generated_garbage(4, true), 14);
}

#[test]
fn gen_rem_garbage_truth_table() {
    // spec: GenRemGarbage — (genGarbage, remGarbage), req-multi-garbage-cancel
    assert_eq!(gen_rem_garbage(0, 0, false), (0, 0));
    assert_eq!(gen_rem_garbage(5, 0, false), (0, 5)); // nothing generated, all of garbage remains
    assert_eq!(gen_rem_garbage(1, 2, false), (1, 0)); // generated (1) exactly cancels pending (1)
    assert_eq!(gen_rem_garbage(0, 2, false), (1, 0)); // nothing pending: remGarbage floors at 0
    assert_eq!(gen_rem_garbage(3, 2, false), (1, 2)); // partial cancellation
    assert_eq!(gen_rem_garbage(0, 0, true), (10, 0));
}

// ── materialization: unobstructed ────────────────────────────────────────

/// `drop_piece` with pending garbage below `HM`, on an otherwise-empty
/// board (no line clear, so `genGarbage = 0` and `remGarbage = garbage`
/// exactly): the fixed piece's own row is shifted up by exactly
/// `remGarbage`, and the bottom `remGarbage` rows become garbage rows with
/// the hole at the configured column.
#[test]
fn materialize_unobstructed_shifts_and_fills_garbage_rows() {
    let mut m = fresh(0, PLAYER_COUNT);
    // Force the piece to Bar r0 (single occupied row, dy=1) so the fixed
    // footprint is exactly row 0, cols 1..3, regardless of bag draw order.
    // py/px already start at INITIAL_Y/INITIAL_X; update_shadow_y refreshes
    // gy for Bar's shape.
    m.s6.s4.s3.s2.s1.p = Piece::Bar;
    m.s6.s4.s3.s2.s1.pr = 0;
    m.s6.update_shadow_y();
    m.garbage = 2;
    let bag = vec![Piece::Bar, Piece::Corner];

    let fired = m.drop_piece(&bag, no_holes());

    assert!(fired);
    let mg = &m.s6.s4.s3.s2.s1.mg;
    // row 2 = the fixed piece's own row (originally row 0), shifted up by 2
    assert_eq!(mg[2][0], None);
    assert_eq!(mg[2][1], Some(PieceOrExtra::Piece(Piece::Bar)));
    assert_eq!(mg[2][2], Some(PieceOrExtra::Piece(Piece::Bar)));
    assert_eq!(mg[2][3], Some(PieceOrExtra::Piece(Piece::Bar)));
    assert_eq!(mg[2][4], None);
    // rows 0, 1 = garbage rows, hole at column 2
    for (y, row) in mg.iter().enumerate().take(2usize) {
        for (x, cell) in row.iter().enumerate().take(5usize) {
            if x == 2 {
                assert_eq!(*cell, None, "row {y} hole");
            } else {
                assert_eq!(
                    *cell,
                    Some(PieceOrExtra::Extra(Garbage)),
                    "row {y} col {x}"
                );
            }
        }
    }
    // rows 3, 4, 5 = untouched, still empty
    for (y, row) in mg.iter().enumerate().take(6usize).skip(3) {
        assert!(row.iter().all(Option::is_none), "row {y} should be empty");
    }
    assert!(!m.s6.s4.s3.s2.s1.gameover);
    assert_eq!(m.garbage, 0); // consumed by materialization
    assert_eq!(m.rem_gen_garbage, 0); // nothing generated (no line cleared)
    check_invariants(&m);
}

// ── materialization: overflow (remGarbage >= HM) ────────────────────────

/// `remGarbage >= HM`: the entire board is pushed off — every row becomes a
/// garbage row and gameover fires unconditionally, no scan needed.
#[test]
fn materialize_overflow_when_remaining_at_least_hm() {
    let mut m = fresh(0, PLAYER_COUNT);
    m.garbage = 8; // >= HM = 6
    let bag = vec![Piece::Bar, Piece::Corner];

    let fired = m.drop_piece(&bag, no_holes());

    assert!(fired);
    let mg = &m.s6.s4.s3.s2.s1.mg;
    for row in mg.iter().take(6usize) {
        for (x, cell) in row.iter().enumerate().take(5usize) {
            if x == 2 {
                assert_eq!(*cell, None);
            } else {
                assert_eq!(*cell, Some(PieceOrExtra::Extra(Garbage)));
            }
        }
    }
    assert!(m.s6.s4.s3.s2.s1.gameover);
    assert!(m.gameover_view[0]);
    check_invariants(&m);
}

// ── materialization: forbidden-zone recheck after a non-overflowing shift ──

/// A pre-existing occupied cell (row 3, outside the falling piece's own
/// columns) is shifted into the forbidden zone (`FY=4`, `FH=2`) by garbage
/// insufficient to overflow the top. Gameover must still fire, via the
/// trailing forbidden-zone recheck on the new grid (§4-T7c).
#[test]
fn materialize_forbidden_zone_recheck_without_overflow() {
    let mut m = fresh(0, PLAYER_COUNT);
    m.s6.s4.s3.s2.s1.mg[3][4] = Some(PieceOrExtra::Piece(Piece::Corner)); // column 4: outside the piece's own cols 1..3
    m.garbage = 2;
    let bag = vec![Piece::Bar, Piece::Corner];

    let fired = m.drop_piece(&bag, no_holes());

    assert!(fired);
    let mg = &m.s6.s4.s3.s2.s1.mg;
    assert_eq!(
        mg[5][4],
        Some(PieceOrExtra::Piece(Piece::Corner)),
        "row 3 shifted to row 5 (3 + 2)"
    );
    assert!(
        m.s6.s4.s3.s2.s1.gameover,
        "forbidden-zone recheck must catch the shifted cell"
    );
    assert!(m.gameover_view[0]);
    check_invariants(&m);
}

// ── drop_piece == an equivalent fall_step sequence ending in a fix ──────

/// `drop_piece` must reach the same materialized result as `move_piece(-1,
/// 0)` stepped to rest, then `fix_piece` directly (§9).
#[test]
fn drop_piece_matches_equivalent_fall_sequence() {
    let bag = vec![Piece::Bar, Piece::Corner];

    let mut dropped = fresh(0, PLAYER_COUNT);
    dropped.garbage = 3;
    assert!(dropped.drop_piece(&bag, no_holes()));

    let mut stepped = fresh(0, PLAYER_COUNT);
    stepped.garbage = 3;
    while stepped.move_piece(-1, 0) {}
    assert!(stepped.fix_piece(&bag, no_holes()));

    assert_eq!(dropped.s6.s4.s3.s2.s1.mg, stepped.s6.s4.s3.s2.s1.mg);
    assert_eq!(
        dropped.s6.s4.s3.s2.s1.gameover,
        stepped.s6.s4.s3.s2.s1.gameover
    );
    assert_eq!(dropped.garbage, stepped.garbage);
    assert_eq!(dropped.rem_gen_garbage, stepped.rem_gen_garbage);
    assert_eq!(dropped.target, stepped.target);
    check_invariants(&dropped);
    check_invariants(&stepped);
}

// ── target round-robin ───────────────────────────────────────────────────

/// `next_target` directly: a 3-player cycle, `self=0`, starting at `pl=0`,
/// skips a not-playing candidate and lands on the next one that is.
#[test]
fn next_target_skips_not_playing_and_self() {
    let playing = |pl2: usize| pl2 != 1; // player 1 not playing
    assert_eq!(next_target(playing, 0, 0, 3), 2); // 0 -> 1 (not playing) -> 2 (playing, != self)
}

/// `next_target` falls back to `self` when nobody else is playing (the
/// winner case — req-multi-target-nonself).
#[test]
fn next_target_falls_back_to_self_when_no_candidate() {
    let playing = |pl2: usize| pl2 == 0; // only self is playing
    assert_eq!(next_target(playing, 0, 0, 3), 0);
}

/// `receive_gameover` redirects `target` away from a now-dead player,
/// walking the 3-player cycle; once no other player remains, `target`
/// falls back to `self` (`T7.v`'s `NextTargetAux` — not a bug).
#[test]
fn receive_gameover_redirects_target_round_robin() {
    let mut m = fresh(0, 3);
    assert_eq!(m.target, 1); // Init: target = PlayerNext(myIndex) = 1

    m.receive_gameover(1);
    assert!(m.gameover_view[1]);
    assert_eq!(
        m.target, 2,
        "target redirects from the now-dead player 1 to player 2"
    );

    m.receive_gameover(2);
    assert!(m.gameover_view[2]);
    assert_eq!(
        m.target, 0,
        "no other player left playing -> falls back to self"
    );
}

// ── receive_* field updates ──────────────────────────────────────────────

#[test]
fn receive_garbage_accumulates() {
    let mut m = fresh(0, PLAYER_COUNT);
    assert_eq!(m.garbage, 0);
    m.receive_garbage(3);
    assert_eq!(m.garbage, 3);
    m.receive_garbage(4);
    assert_eq!(m.garbage, 7);
}

#[test]
fn receive_disconnect_updates_view_and_redirects_target() {
    let mut m = fresh(0, 3);
    assert_eq!(m.target, 1);
    m.receive_disconnect(1);
    assert!(!m.connected_view[1]);
    assert_eq!(
        m.target, 2,
        "target redirects away from the now-disconnected player 1"
    );
}

// ── notice_disconnection: idempotency ────────────────────────────────────

#[test]
fn notice_disconnection_idempotent() {
    let mut m = fresh(0, PLAYER_COUNT);
    assert!(m.connected_view[0]);
    assert!(m.notice_disconnection(), "first call fires");
    assert!(!m.connected_view[0]);
    assert!(
        !m.notice_disconnection(),
        "second call is a no-op — already noticed"
    );
    assert!(!m.connected_view[0]);
}

// ── §4-T7h: drop_piece's winner_multi guard leaves py/px untouched ──────

/// A `WinnerMulti` `drop_piece` must leave `py`/`px` byte-identical, even
/// transiently (§4-T7h).
#[test]
fn drop_piece_winner_multi_guard_leaves_state_untouched() {
    let mut m = fresh(0, 2);
    m.gameover_view[1] = true; // the only other player is gameover -> self is the winner
    assert!(t7::model::winner_multi(
        &m.gameover_view,
        &m.connected_view,
        m.my_index
    ));

    let before = (
        m.s6.s4.s3.s2.s1.py,
        m.s6.s4.s3.s2.s1.px,
        m.s6.s4.s3.s2.s1.mg.clone(),
    );
    let bag = vec![Piece::Bar, Piece::Corner];

    let fired = m.drop_piece(&bag, no_holes());

    assert!(!fired);
    assert_eq!(m.s6.s4.s3.s2.s1.py, before.0);
    assert_eq!(m.s6.s4.s3.s2.s1.px, before.1);
    assert_eq!(m.s6.s4.s3.s2.s1.mg, before.2);
}

// ── differential: one hand-traced materialization case agrees with oracle.rs ──

#[test]
fn materialize_case_matches_independent_oracle() {
    let mut m = fresh(0, PLAYER_COUNT);
    m.s6.s4.s3.s2.s1.p = Piece::Bar; // force a known, single-row footprint — see the test above
    m.s6.s4.s3.s2.s1.pr = 0;
    m.s6.update_shadow_y();
    m.s6.s4.s3.s2.s1.mg[3][4] = Some(PieceOrExtra::Piece(Piece::Corner));
    let old_mg = m.s6.s4.s3.s2.s1.mg.clone();
    m.garbage = 2;
    let bag = vec![Piece::Bar, Piece::Corner];

    assert!(m.drop_piece(&bag, no_holes()));

    // The oracle only models materialization itself, so replay it against
    // the pre-fix grid plus the piece's fixed row (row 0, cols 1..3) to
    // reconstruct `self.s6.fix_piece`'s output just before materialization.
    let mut pre_materialize = old_mg;
    pre_materialize[0][1] = Some(PieceOrExtra::Piece(Piece::Bar));
    pre_materialize[0][2] = Some(PieceOrExtra::Piece(Piece::Bar));
    pre_materialize[0][3] = Some(PieceOrExtra::Piece(Piece::Bar));
    let (expected_mg, expected_overflow) = oracle::oracle_materialize(
        &pre_materialize,
        2,
        no_holes(),
        PieceOrExtra::Extra(Garbage),
    );

    assert_eq!(m.s6.s4.s3.s2.s1.mg, expected_mg);
    assert!(!expected_overflow);
    assert!(
        m.s6.s4.s3.s2.s1.gameover,
        "forbidden-zone recheck still catches the shifted cell"
    );
}
