// spec: tests/test_instance.rs — test fixture (§2, §9, `implementation.md`).
//
// New fixture (§9): t1's own `TestInstance` pins `CellExtra = Infallible`,
// but `t7::model::Params` needs `Garbage`, so this can't `include!` t1's
// fixture verbatim. Board/piece geometry mirrors t1's own fixture's scale
// (`mg[y][x]`, `y` increasing upward, `y=0` the floor; piece grids
// `pg[dy][dx]` likewise), so hand-traced golden vectors carry over; adds a
// `PLAYER_COUNT = 3` roster for multiplayer test suites.

#![allow(dead_code)]

use std::sync::LazyLock;
use t1::model::Params as T1Params;

// ── Scalar parameters (identical to t1/tests/test_instance.rs's own) ────

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

pub const PLAYER_COUNT: usize = 3;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Piece {
    /// A straight 3-cell bar: two distinct rotations, each occurring twice
    /// (`r0 = r2`, `r1 = r3`).
    Bar,
    /// An L-tromino (all four rotations distinct).
    Corner,
}

const ALL_PIECES: [Piece; 2] = [Piece::Bar, Piece::Corner];

type PieceGrid = [[Option<Piece>; 3]; 3];

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

impl T1Params for TestInstance {
    type Piece = Piece;
    // spec: CellExtra = Garbage per §9 — the one field that must differ
    // from t1's own fixture.
    type CellExtra = t7::model::Garbage;

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

/// spec: NextLen — short, hand-traceable value, matching every prior
/// layer's own `TestInstance` choice.
impl t4::model::Params for TestInstance {
    const NEXT_LEN: i64 = 3;
}

/// spec: `T5.v`/`T6.v` declare no `Parameter` of their own — empty impl,
/// same reasoning `t6/tests/test_instance.rs`'s own header gives.
impl t5::model::Params for TestInstance {}

/// spec: §0.2 — roster fields (`Player`/`Host`/...) are runtime facts, not
/// `Params` items, so this only needs to satisfy the `CellExtra = Garbage`
/// bound, already discharged above.
impl t7::model::Params for TestInstance {}

/// A `piece_source` for `Machine::new`: `TestInstance::initial_main_grid()`
/// is entirely `false`, so this is never actually called.
pub fn piece_source_stub() -> impl FnMut() -> Piece {
    || Piece::Bar
}

// ── Deterministic PRNG (own copy, per every prior layer's own fixture) ──

pub struct Prng(u64);

impl Prng {
    pub fn new(seed: u64) -> Self {
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

    pub fn next_below(&mut self, bound: usize) -> usize {
        (self.next_u64() % bound as u64) as usize
    }

    pub fn choose<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[self.next_below(xs.len())]
    }
}
