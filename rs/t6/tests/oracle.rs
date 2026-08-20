// spec: tests/oracle.rs — executable T6.v reference for `RotateKickPiece` only.
// Standalone from t5's oracle by design (§9); `Machine<P>` is `t5::model::Machine`
// (§1), so `s1`..`s4` mechanics are already covered by `t1`-`t5`'s own oracles.
//
// `oracle_rotate_kick_piece` reimplements `Valid`'s occupied/free test and
// `RotatePiece`'s guard directly against the raw grids (no `t1::model` import),
// and computes both kick attempts from the original `px`, never chained off a
// failed attempt's `px` (§4-T6b).

#![allow(dead_code)]

/// spec: `Valid`, reimplemented directly against the raw grids. Every occupied
/// cell of `pg` (the piece's rotated `PW×PW` grid, `dy`/`dx` piece-local),
/// translated to `(py,px)`, must land inside `mg`'s `[0,HM)×[0,WM)` box and on
/// an empty (`None`) cell of `mg`.
fn oracle_valid<T1: Copy + PartialEq, T2: Copy + PartialEq>(
    mg: &[Vec<Option<T1>>],
    pg: &[Vec<Option<T2>>],
    py: i64,
    px: i64,
) -> bool {
    let hm = mg.len() as i64;
    let wm = if hm > 0 { mg[0].len() as i64 } else { 0 };
    let pw = pg.len() as i64;
    for dy in 0..pw {
        for dx in 0..pw {
            if pg[dy as usize][dx as usize].is_none() {
                continue; // exact-sentinel test, not truthiness
            }
            let (y, x) = (py + dy, px + dx);
            if y < 0 || y >= hm || x < 0 || x >= wm {
                return false; // outside the main grid's own box
            }
            if mg[y as usize][x as usize].is_some() {
                return false; // occupied
            }
        }
    }
    true
}

/// spec: `RotatePiece`'s guard, reimplemented independently. `cw` *decrements*
/// `pr` (wraps `0 -> 3`), matching `t1::model::rotate_piece`'s own convention
/// (`t1/proofs.md`'s `L-rem_euclid` table). `rot_grids` is this piece's own
/// four rotation grids, indexed `0..4` by `pr`, supplied by the caller.
fn oracle_rotate_piece<T1: Copy + PartialEq, T2: Copy + PartialEq>(
    cw: bool,
    mg: &[Vec<Option<T1>>],
    rot_grids: &[Vec<Vec<Option<T2>>>],
    py: i64,
    px: i64,
    pr: u8,
    gameover: bool,
) -> Option<u8> {
    let delta: i64 = if cw { -1 } else { 1 };
    let pr2 = ((pr as i64 + delta).rem_euclid(4)) as u8;
    if gameover || !oracle_valid(mg, &rot_grids[pr2 as usize], py, px) {
        None
    } else {
        Some(pr2)
    }
}

/// spec: `RotateKickPiece`, reimplemented independently. `None` on failure is
/// a stutter: the caller must leave its own state untouched (§4-T6b).
pub fn oracle_rotate_kick_piece<T1: Copy + PartialEq, T2: Copy + PartialEq>(
    cw: bool,
    mg: &[Vec<Option<T1>>],
    rot_grids: &[Vec<Vec<Option<T2>>>],
    py: i64,
    px: i64,
    pr: u8,
    gameover: bool,
) -> Option<(i64, i64, u8)> {
    let plain_fires = oracle_rotate_piece(cw, mg, rot_grids, py, px, pr, gameover).is_some();
    if gameover || plain_fires {
        return None; // §4-T6b: exclusive with a plain rotation that would fire
    }
    // left, from the original px
    if let Some(pr2) = oracle_rotate_piece(cw, mg, rot_grids, py, px - 1, pr, gameover) {
        return Some((py, px - 1, pr2));
    }
    // right, also from the original px
    if let Some(pr2) = oracle_rotate_piece(cw, mg, rot_grids, py, px + 1, pr, gameover) {
        return Some((py, px + 1, pr2));
    }
    None
}
