// Independent `Params` test fixture (distinct from `instance::Tetris`):
// a 3×3 piece grid (`PW = 3`, vs. the real `4`) on a compact 6×5 board with
// two hand-picked pieces, keeping line-clear and property/fuzz tests small
// and fast to construct.
//
// Included by other `tests/*.rs` via `#[path = "test_instance.rs"] mod
// fixture;`, and by later models' `test_instance.rs` via `include!` (cargo
// also compiles this file as its own empty integration-test binary). Uses
// plain `//` comments and per-item `#[allow(dead_code)]` rather than a
// file-level `//!`/`#![allow(dead_code)]`, since inner doc comments/attributes
// only apply at the literal top of a file/`mod` block, a position `include!`
// doesn't preserve.

use std::sync::LazyLock;
use t1::model::Params;

// ── Scalar parameters ────────────────────────────────────────────────────

#[allow(dead_code)]
pub struct TestInstance;

const PW: i64 = 3;
const FY: i64 = 4;
const FX: i64 = 0;
const INITIAL_Y: i64 = 3;
const INITIAL_X: i64 = 1;

const HM: usize = 6;
const WM: usize = 5;
const FH: usize = 2;
const FW: usize = 5;

/// Both pieces' `r = 0` occupied cells lie within `[FY, FY + FH)` ×
/// `[FX, FX + FW)`, satisfying `AxiomsRotGrid`'s spawn-containment conjunct.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Piece {
    /// A straight 3-cell bar (mirrors the real `I` piece's fold-over: two
    /// distinct rotations, each occurring twice — `r0 = r2`, `r1 = r3`).
    Bar,
    /// An L-tromino (all four rotations distinct).
    Corner,
}

const ALL_PIECES: [Piece; 2] = [Piece::Bar, Piece::Corner];

type PieceGrid = [[Option<Piece>; 3]; 3];

// Bar: r0 occupies the middle row, r1 the middle column; `r2 = r0`,
// `r3 = r1` (symmetric under a half turn).
const BAR_R0: PieceGrid = [
    [None, None, None],
    [Some(Piece::Bar), Some(Piece::Bar), Some(Piece::Bar)],
    [None, None, None],
];
const BAR_R1: PieceGrid = [
    [None, Some(Piece::Bar), None],
    [None, Some(Piece::Bar), None],
    [None, Some(Piece::Bar), None],
];

// Corner: an L-tromino, center (1,1), all four rotations distinct.
const CORNER_R0: PieceGrid = [
    [None, None, None],
    [Some(Piece::Corner), Some(Piece::Corner), None],
    [Some(Piece::Corner), None, None],
];
const CORNER_R1: PieceGrid = [
    [Some(Piece::Corner), Some(Piece::Corner), None],
    [None, Some(Piece::Corner), None],
    [None, None, None],
];
const CORNER_R2: PieceGrid = [
    [None, None, Some(Piece::Corner)],
    [None, Some(Piece::Corner), Some(Piece::Corner)],
    [None, None, None],
];
const CORNER_R3: PieceGrid = [
    [None, None, None],
    [None, Some(Piece::Corner), None],
    [None, Some(Piece::Corner), Some(Piece::Corner)],
];

fn rot_grid_table_entry(p: Piece, r: u8) -> &'static PieceGrid {
    match (p, r) {
        (Piece::Bar, 0) | (Piece::Bar, 2) => &BAR_R0,
        (Piece::Bar, 1) | (Piece::Bar, 3) => &BAR_R1,
        (Piece::Corner, 0) => &CORNER_R0,
        (Piece::Corner, 1) => &CORNER_R1,
        (Piece::Corner, 2) => &CORNER_R2,
        (Piece::Corner, 3) => &CORNER_R3,
        (_, r) => panic!("rotation out of range: {r}"),
    }
}

static INITIAL_MAIN_GRID: LazyLock<Vec<Vec<bool>>> = LazyLock::new(|| vec![vec![false; WM]; HM]);
static FORBIDDEN_GRID: LazyLock<Vec<Vec<bool>>> = LazyLock::new(|| vec![vec![true; FW]; FH]);

type VecPieceGrid = Vec<Vec<Option<Piece>>>;

static ROT_GRID_TABLE: LazyLock<Vec<Vec<VecPieceGrid>>> = LazyLock::new(|| {
    ALL_PIECES
        .iter()
        .map(|&p| {
            (0..4u8)
                .map(|r| {
                    rot_grid_table_entry(p, r)
                        .iter()
                        .map(|row| row.to_vec())
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        })
        .collect()
});

fn piece_index(p: Piece) -> usize {
    match p {
        Piece::Bar => 0,
        Piece::Corner => 1,
    }
}

impl Params for TestInstance {
    type Piece = Piece;
    type CellExtra = std::convert::Infallible;

    const PW: i64 = PW;
    const FY: i64 = FY;
    const FX: i64 = FX;

    fn piece_all() -> &'static [Piece] {
        &ALL_PIECES
    }

    fn initial_main_grid() -> &'static Vec<Vec<bool>> {
        &INITIAL_MAIN_GRID
    }

    fn forbidden_grid() -> &'static Vec<Vec<bool>> {
        &FORBIDDEN_GRID
    }

    fn rot_grid(p: Piece, r: u8) -> &'static Vec<Vec<Option<Piece>>> {
        &ROT_GRID_TABLE[piece_index(p)][r as usize]
    }

    fn initial_y(_p: Piece) -> i64 {
        INITIAL_Y
    }

    fn initial_x(_p: Piece) -> i64 {
        INITIAL_X
    }
}

/// `piece_source` for `Machine::new`, supplying a piece per occupied cell of
/// `InitialMainGrid`. Since that grid here is entirely empty, this is never
/// actually called — any constant closure works.
#[allow(dead_code)]
pub fn piece_source_stub() -> impl FnMut() -> Piece {
    || Piece::Bar
}

// ── Deterministic PRNG ───────────────────────────────────────────────────
//
// Fixed-seed xorshift64 for the property/fuzz/oracle suites, avoiding a
// `rand` dependency for what's just picking among a few small integers;
// the fixed seed keeps runs reproducible.

#[allow(dead_code)]
pub struct Prng(u64);

#[allow(dead_code)]
impl Prng {
    pub fn new(seed: u64) -> Self {
        // avoid the fixed point at 0
        Prng(if seed == 0 { 0x9E3779B97F4A7C15 } else { seed })
    }

    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    /// Uniform in `[0, bound)`. `bound` is always small in these suites
    /// (a handful of action/piece choices), so the modulo bias is
    /// negligible.
    pub fn next_below(&mut self, bound: usize) -> usize {
        (self.next_u64() % bound as u64) as usize
    }

    pub fn choose<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[self.next_below(xs.len())]
    }
}
