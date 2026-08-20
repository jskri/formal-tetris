//! spec: tests/oracle.rs — §9.4, `implementation.md`.
//!
//! A literal, *unfused* interpreter of `T1.v`'s grid algebra and state
//! transitions, independent of `model.rs` (which fuses these per D13: grid
//! algebra realized in place, not via fresh allocation). Grids here are
//! materialized densely on their own `[y, y+h) × [x, x+w)` box. Each step of
//! a random trace is applied to both a `Machine<P>` and this oracle's
//! `RocqState<Piece>`, and the two are asserted equivalent.
//!
//! Piece-shape *data* (`P::rot_grid`, etc.) is sourced from the `Params`
//! instance under test rather than reimplemented — already checked by
//! `check_axioms` and `model_unit_test.rs`'s golden vectors. What this file
//! checks independently is the *engine logic*: the grid algebra and the
//! five state transitions.
//!
//! Two representation choices deliberately diverge from `T1.v`'s own shapes:
//! - `L : ℤ → ℤ → bool` is materialized as `Vec<Vec<bool>>` (below), not a
//!   closure: `T1.v`'s grid algebra never reads outside a grid's declared
//!   box, so nothing is lost, while a closure would need `Box<dyn Fn>` for
//!   `union`/`intersect` to return a new grid and would forfeit `Clone`/
//!   `PartialEq`/`Debug`, which `equivalent()` (below) needs to localize a
//!   divergence to a specific cell.
//! - `HW`/`YX`/`pyx` are flattened to named scalar fields (`h,w,y,x` on
//!   `Grid`; `py,px` on `RocqState`), never `(i64,i64)` pairs — D14's
//!   named-field reasoning, applied harder here since this file
//!   reimplements `model.rs`'s same swap-prone shapes from scratch, so a
//!   positional-tuple slip could give both implementations the same
//!   undetectable bug.

#[path = "test_instance.rs"]
mod fixture;

use fixture::{Prng, TestInstance};
use t1::instance::Tetris;
use t1::model::{Machine, Params};

// ── An independent grid algebra (spec: Grid, and §T1.v's grid operators) ──

/// `l`/`h`/`w`/`y`/`x`, not `L: i64->i64->bool` + `HW`/`YX` pairs — see
/// module doc comment above.
#[derive(Clone)]
struct Grid {
    l: Vec<Vec<bool>>, // l[dy][dx], dy in [0,h), dx in [0,w)
    h: i64,
    w: i64,
    y: i64,
    x: i64,
}

fn grid_of(l: Vec<Vec<bool>>, y: i64, x: i64) -> Grid {
    let h = l.len() as i64;
    let w = if h > 0 { l[0].len() as i64 } else { 0 };
    Grid { l, h, w, y, x }
}

fn constant(h: i64, w: i64, y: i64, x: i64, b: bool) -> Grid {
    let h = h.max(0);
    let w = w.max(0);
    Grid {
        l: vec![vec![b; w as usize]; h as usize],
        h,
        w,
        y,
        x,
    }
}

impl Grid {
    /// spec: `L`, total over `ℤ × ℤ` in `T1.v`; `false` outside this grid's
    /// own box. Never exercised outside the box below — every call site
    /// first restricts its `y` range to the grid's own box.
    fn l_at(&self, y: i64, x: i64) -> bool {
        if y < self.y || y >= self.y + self.h || x < self.x || x >= self.x + self.w {
            false
        } else {
            self.l[(y - self.y) as usize][(x - self.x) as usize]
        }
    }

    /// spec: `Full`
    fn full(&self) -> Grid {
        constant(self.h, self.w, self.y, self.x, true)
    }

    /// spec: `GridInclude` (`⊆`)
    fn include(&self, other: &Grid) -> bool {
        for dy in 0..self.h {
            for dx in 0..self.w {
                if self.l[dy as usize][dx as usize] && !other.l_at(self.y + dy, self.x + dx) {
                    return false;
                }
            }
        }
        true
    }

    fn is_empty(&self) -> bool {
        !self.l.iter().any(|row| row.iter().any(|&b| b))
    }

    /// spec: `GridUnion` (`∪`)
    fn union(&self, other: &Grid) -> Grid {
        let min_y = self.y.min(other.y);
        let min_x = self.x.min(other.x);
        let top_max = (self.y + self.h).max(other.y + other.h);
        let right_max = (self.x + self.w).max(other.x + other.w);
        let h = (top_max - min_y).max(0);
        let w = (right_max - min_x).max(0);
        let mut l = vec![vec![false; w as usize]; h as usize];
        for dy in 0..h {
            for dx in 0..w {
                let (y, x) = (min_y + dy, min_x + dx);
                l[dy as usize][dx as usize] = self.l_at(y, x) || other.l_at(y, x);
            }
        }
        Grid {
            l,
            h,
            w,
            y: min_y,
            x: min_x,
        }
    }

    /// spec: `GridIntersect` (`∩`)
    fn intersect(&self, other: &Grid) -> Grid {
        let max_y = self.y.max(other.y);
        let max_x = self.x.max(other.x);
        let top_min = (self.y + self.h).min(other.y + other.h);
        let right_min = (self.x + self.w).min(other.x + other.w);
        let h = (top_min - max_y).max(0);
        let w = (right_min - max_x).max(0);
        let mut l = vec![vec![false; w as usize]; h as usize];
        for dy in 0..h {
            for dx in 0..w {
                let (y, x) = (max_y + dy, max_x + dx);
                l[dy as usize][dx as usize] = self.l_at(y, x) && other.l_at(y, x);
            }
        }
        Grid {
            l,
            h,
            w,
            y: max_y,
            x: max_x,
        }
    }

    /// spec: `GridTranslate` (`⊕`)
    fn translate(&self, dy: i64, dx: i64) -> Grid {
        Grid {
            l: self.l.clone(),
            h: self.h,
            w: self.w,
            y: self.y + dy,
            x: self.x + dx,
        }
    }
}

fn bool_grid_of(g: &[Vec<bool>], y: i64, x: i64) -> Grid {
    grid_of(g.to_vec(), y, x)
}

fn piece_bool_grid<P: Params>(p: P::Piece, r: u8) -> Grid {
    let g = P::rot_grid(p, r);
    let l = g
        .iter()
        .map(|row| row.iter().map(|c| c.is_some()).collect())
        .collect();
    grid_of(l, 0, 0)
}

// ── RocqState and T1.v's five transitions, literally, unfused ────────────

/// `py`/`px` scalars, not a `pyx: (i64,i64)` pair — same D14-style reasoning
/// as `Grid`'s fields above (module doc comment).
#[derive(Clone)]
struct RocqState<Piece> {
    mg: Grid,
    p: Piece,
    py: i64,
    px: i64,
    pr: i64,
    gameover: bool,
    cleared_lines: i64,
}

/// spec: Init
fn rocq_init<P: Params>(p: P::Piece) -> RocqState<P::Piece> {
    let mg = bool_grid_of(P::initial_main_grid(), 0, 0);
    let forbidden = bool_grid_of(P::forbidden_grid(), P::FY, P::FX);
    let gameover = !forbidden.intersect(&mg).is_empty();
    RocqState {
        mg,
        p,
        py: P::initial_y(p),
        px: P::initial_x(p),
        pr: 0,
        gameover,
        cleared_lines: 0,
    }
}

/// spec: Valid
fn rocq_valid<P: Params>(g: &Grid, p: P::Piece, py: i64, px: i64, pr: i64) -> bool {
    let gp = piece_bool_grid::<P>(p, pr as u8).translate(py, px);
    gp.include(&g.full()) && gp.intersect(g).is_empty()
}

/// spec: CanMovePiece
fn rocq_can_move_piece<P: Params>(dy: i64, dx: i64, s: &RocqState<P::Piece>) -> bool {
    ((dy == 0 && dx == -1) || (dy == 0 && dx == 1) || (dy == -1 && dx == 0))
        && rocq_valid::<P>(&s.mg, s.p, s.py + dy, s.px + dx, s.pr)
}

/// spec: MovePiece
fn rocq_move_piece<P: Params>(
    dy: i64,
    dx: i64,
    s: &RocqState<P::Piece>,
) -> Option<RocqState<P::Piece>> {
    if s.gameover || !rocq_can_move_piece::<P>(dy, dx, s) {
        return None;
    }
    Some(RocqState {
        py: s.py + dy,
        px: s.px + dx,
        ..s.clone()
    })
}

/// spec: RotatePiece
fn rocq_rotate_piece<P: Params>(cw: bool, s: &RocqState<P::Piece>) -> Option<RocqState<P::Piece>> {
    let pr2 = (s.pr + if cw { -1 } else { 1 }).rem_euclid(4);
    if s.gameover || !rocq_valid::<P>(&s.mg, s.p, s.py, s.px, pr2) {
        return None;
    }
    Some(RocqState {
        pr: pr2,
        ..s.clone()
    })
}

/// spec: IsFullLineb, restricted to `y` already known to be in `g`'s box
/// (see `Grid::l_at`'s doc comment).
fn rocq_is_full_line(g: &Grid, y: i64) -> bool {
    (g.x..g.x + g.w).all(|x| g.l_at(y, x))
}

/// spec: FilterFullLines + Resize, i.e. `ClearFullLines`: kept rows
/// compacted to the bottom of a fresh `h`-row grid, original order,
/// missing rows filled `false` at the top.
fn rocq_clear_full_lines(g: &Grid) -> Grid {
    let kept: Vec<Vec<bool>> = (g.y..g.y + g.h)
        .filter(|&y| !rocq_is_full_line(g, y))
        .map(|y| (g.x..g.x + g.w).map(|x| g.l_at(y, x)).collect())
        .collect();
    let mut l = vec![vec![false; g.w as usize]; g.h as usize];
    for (i, row) in kept.into_iter().enumerate() {
        l[i] = row;
    }
    Grid {
        l,
        h: g.h,
        w: g.w,
        y: g.y,
        x: g.x,
    }
}

/// spec: FullLineCount
fn rocq_full_line_count(g: &Grid) -> i64 {
    (g.y..g.y + g.h)
        .filter(|&y| rocq_is_full_line(g, y))
        .count() as i64
}

/// spec: FixPiece
fn rocq_fix_piece<P: Params>(
    p_new: P::Piece,
    s: &RocqState<P::Piece>,
) -> Option<RocqState<P::Piece>> {
    if s.gameover || rocq_can_move_piece::<P>(-1, 0, s) {
        return None;
    }
    let pg = piece_bool_grid::<P>(s.p, s.pr as u8).translate(s.py, s.px);
    let u = s.mg.union(&pg).intersect(&s.mg.full());
    let mg2 = rocq_clear_full_lines(&u);
    let forbidden = bool_grid_of(P::forbidden_grid(), P::FY, P::FX);
    let gameover2 = !forbidden.intersect(&mg2).is_empty();
    Some(RocqState {
        mg: mg2,
        p: p_new,
        py: P::initial_y(p_new),
        px: P::initial_x(p_new),
        pr: 0,
        gameover: gameover2,
        cleared_lines: rocq_full_line_count(&u),
    })
}

/// spec: FallStep
fn rocq_fall_step<P: Params>(
    p_new: P::Piece,
    s: &RocqState<P::Piece>,
) -> Option<RocqState<P::Piece>> {
    match rocq_move_piece::<P>(-1, 0, s) {
        Some(s2) => Some(s2),
        None => rocq_fix_piece::<P>(p_new, s),
    }
}

// ── State equivalence (α, restricted to what both sides can express) ─────

fn equivalent<P: Params>(m: &Machine<P>, s: &RocqState<P::Piece>) -> bool {
    if m.p != s.p || m.py != s.py || m.px != s.px || m.pr as i64 != s.pr {
        return false;
    }
    if m.gameover != s.gameover || m.cleared_lines != s.cleared_lines {
        return false;
    }
    if m.mg.len() as i64 != s.mg.h {
        return false;
    }
    for y in 0..s.mg.h {
        if m.mg[y as usize].len() as i64 != s.mg.w {
            return false;
        }
        for x in 0..s.mg.w {
            let expected = s.mg.l_at(s.mg.y + y, s.mg.x + x);
            let actual = m.mg[y as usize][x as usize].is_some();
            if expected != actual {
                return false;
            }
        }
    }
    true
}

// ── Random-trace differential check ───────────────────────────────────────

fn apply_machine<P: Params>(m: &mut Machine<P>, cmd: u8, piece: P::Piece) {
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
            m.fix_piece(piece);
        }
        _ => {
            m.fall_step(piece);
        }
    }
}

fn apply_rocq<P: Params>(s: &mut RocqState<P::Piece>, cmd: u8, piece: P::Piece) {
    let next = match cmd % 7 {
        0 => rocq_move_piece::<P>(0, -1, s),
        1 => rocq_move_piece::<P>(0, 1, s),
        2 => rocq_move_piece::<P>(-1, 0, s),
        3 => rocq_rotate_piece::<P>(true, s),
        4 => rocq_rotate_piece::<P>(false, s),
        5 => rocq_fix_piece::<P>(piece, s),
        _ => rocq_fall_step::<P>(piece, s),
    };
    if let Some(s2) = next {
        *s = s2;
    }
}

fn run_differential<P: Params>(seed: u64, steps: usize) {
    let mut rng = Prng::new(seed);
    let pieces = P::piece_all();
    let start = rng.choose(pieces);

    let mut m = Machine::<P>::new(start, || rng.choose(pieces));
    let mut s = rocq_init::<P>(start);
    assert!(equivalent(&m, &s), "diverged at Init");

    for step in 1..=steps {
        let cmd = rng.next_below(7) as u8;
        let piece = rng.choose(pieces);
        apply_machine(&mut m, cmd, piece);
        apply_rocq::<P>(&mut s, cmd, piece);
        assert!(
            equivalent(&m, &s),
            "Machine and RocqState diverged at step {step}"
        );
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
