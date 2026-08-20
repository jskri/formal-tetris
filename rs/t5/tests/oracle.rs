// spec: tests/oracle.rs — executable T5.v reference, for `ShadowY`/`gy` only
// (§9). `s4` reuses `t4`'s own oracle — oracle independence for `s4` is
// `t1`–`t4`'s tests' job, not this file's.
//
// `ShadowY` is reimplemented independently here: `oracle_valid` re-tests
// occupied/free directly against the raw grids (no `t1::model::valid`
// import; piece-shape data is still sourced from the caller), and
// `oracle_shadow_y` uses a bounded `for` loop over an explicit index
// rather than `model.rs`'s `while fuel > 0` — same oracle-independence
// discipline as every prior floor (§9 digest). A binary search over
// `valid(y)` is deliberately not used as the alternate shape: an overhang
// can leave open space below an obstruction a piece can never reach, so
// `valid(y)` isn't monotone in `y`, and a binary search over it would be
// unsound, not just differently shaped.
//
// `drop_piece` gets no separate oracle: it's just relocate-to-`gy` then
// `fix_piece`, both already covered by `oracle_shadow_y` and `t1`–`t4`'s
// own oracles.

#![allow(dead_code)]

/// spec: `Valid`, reimplemented directly against the raw grids — every
/// occupied cell of `pg` (rotated `PW×PW` piece grid, local `dy`/`dx`),
/// translated to `(py,px)`, must land inside `mg`'s box and on an empty
/// cell. `mg`/`pg` are independently generic (`T1`/`T2`): only occupancy
/// (`is_some`/`is_none`) is read, so the two never need to share a type.
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

/// spec: `ShadowYImpl` + `ShadowY`, reimplemented independently — bounded
/// `for` loop over an explicit index instead of `model.rs`'s `while fuel >
/// 0` (module header). `pg` is the already-rotated piece grid, supplied by
/// the caller.
pub fn oracle_shadow_y<T1: Copy + PartialEq, T2: Copy + PartialEq>(
    mg: &[Vec<Option<T1>>],
    pg: &[Vec<Option<T2>>],
    py: i64,
    px: i64,
) -> i64 {
    let pw = pg.len() as i64;
    let fuel_max = (py + pw - 1).max(0);
    let mut y = py;
    for _ in 0..fuel_max {
        if !oracle_valid(mg, pg, y - 1, px) {
            break;
        }
        y -= 1;
    }
    y
}
