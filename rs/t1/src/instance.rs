//! Concrete instantiation of `model::Params` (§13).
//!
//! `T1.v` leaves `Piece`, the grids, `RotGrid`, `InitialYX`, `PW` abstract;
//! this module picks one concrete satisfying assignment (a standard 7-piece
//! Tetris set on a 22×10 board with a 2-row forbidden zone at the top).

use crate::model::Params;
use std::sync::LazyLock;

// ── Scalar parameters ────────────────────────────────────────────────────

pub struct Tetris;

const PW: i64 = 4;
const FY: i64 = 20;
const FX: i64 = 0;
const INITIAL_Y: i64 = 19;
const INITIAL_X: i64 = 3;

// ── Piece set ─────────────────────────────────────────────────────────────

#[derive(Copy, Clone, PartialEq, Eq, Debug, strum::EnumIter)]
pub enum Piece {
    I,
    O,
    T,
    S,
    Z,
    J,
    L,
}

impl Piece {
    pub fn all() -> &'static [Piece] {
        use strum::IntoEnumIterator;
        static ALL: LazyLock<Vec<Piece>> = LazyLock::new(|| Piece::iter().collect());
        ALL.as_slice()
    }
}

/// Piece colours, used by a renderer (not part of `T1.v`'s state or
/// transitions; instance data only).
pub fn piece_color(p: Piece) -> [f32; 4] {
    match p {
        Piece::I => [
            0x83 as f32 / 255.0,
            0xa5 as f32 / 255.0,
            0x98 as f32 / 255.0,
            1.0,
        ],
        Piece::O => [
            0xfa as f32 / 255.0,
            0xbd as f32 / 255.0,
            0x2f as f32 / 255.0,
            1.0,
        ],
        Piece::T => [
            0xd3 as f32 / 255.0,
            0x86 as f32 / 255.0,
            0x9b as f32 / 255.0,
            1.0,
        ],
        Piece::S => [
            0xb8 as f32 / 255.0,
            0xbb as f32 / 255.0,
            0x26 as f32 / 255.0,
            1.0,
        ],
        Piece::Z => [
            0xfb as f32 / 255.0,
            0x49 as f32 / 255.0,
            0x34 as f32 / 255.0,
            1.0,
        ],
        Piece::J => [
            0x45 as f32 / 255.0,
            0x85 as f32 / 255.0,
            0x88 as f32 / 255.0,
            1.0,
        ],
        Piece::L => [
            0xfe as f32 / 255.0,
            0x80 as f32 / 255.0,
            0x19 as f32 / 255.0,
            1.0,
        ],
    }
}

/// `draw_grid` renders per-cell via `Colored`, not a caller-supplied
/// closure; this impl is a thin pass-through to `piece_color`.
impl crate::view::Colored for Piece {
    fn color(&self) -> [f32; 4] {
        piece_color(*self)
    }
}

// ── Grid constants ───────────────────────────────────────────────────────

const HM: usize = 22;
const WM: usize = 10;
const FH: usize = 2;
const FW: usize = 10;

static INITIAL_MAIN_GRID: LazyLock<Vec<Vec<bool>>> = LazyLock::new(|| vec![vec![false; WM]; HM]);
static FORBIDDEN_GRID: LazyLock<Vec<Vec<bool>>> = LazyLock::new(|| vec![vec![true; FW]; FH]);

// ── Rotated piece grids ───────────────────────────────────────────────────
//
// Each piece's four rotations (`r = 0..4`), `g[y][x]`, `y = 0` the bottom
// row (D3). Grids are independent literals, not derived by a rotation
// formula. Every `r = 0` grid occupies `y ∈ {1, 2}`, satisfying
// `AxiomsRotGrid`'s spawn-containment conjunct against `InitialYX = (19,
// 3)` and `ForbiddenGrid` at `(20, 0)`: `19 + y ∈ {20, 21} ⊂ [20, 22)`.

type PieceGrid = [[Option<Piece>; 4]; 4];

// ____
// _xx_
// _xx_
// ____
const O_R0: PieceGrid = [
    [None, None, None, None],
    [None, Some(Piece::O), Some(Piece::O), None],
    [None, Some(Piece::O), Some(Piece::O), None],
    [None, None, None, None],
];

// ____   __x_   ____   _x__
// ____   __x_   xxxx   _x__
// xxxx → __x_ → ____ → _x__
// ____   __x_   ____   _x__
const I_R0: PieceGrid = [
    [None, None, None, None],
    [
        Some(Piece::I),
        Some(Piece::I),
        Some(Piece::I),
        Some(Piece::I),
    ],
    [None, None, None, None],
    [None, None, None, None],
];
const I_R1: PieceGrid = [
    [None, None, Some(Piece::I), None],
    [None, None, Some(Piece::I), None],
    [None, None, Some(Piece::I), None],
    [None, None, Some(Piece::I), None],
];
const I_R2: PieceGrid = [
    [None, None, None, None],
    [None, None, None, None],
    [
        Some(Piece::I),
        Some(Piece::I),
        Some(Piece::I),
        Some(Piece::I),
    ],
    [None, None, None, None],
];
const I_R3: PieceGrid = [
    [None, Some(Piece::I), None, None],
    [None, Some(Piece::I), None, None],
    [None, Some(Piece::I), None, None],
    [None, Some(Piece::I), None, None],
];

// ____   ____   ____   ____
// _x__   _x__   ____   _x__
// xxx_ → xx__ → xxx_ → _xx_
// ____   _x__   _x__   _x__
const T_R0: PieceGrid = [
    [None, None, None, None],
    [Some(Piece::T), Some(Piece::T), Some(Piece::T), None],
    [None, Some(Piece::T), None, None],
    [None, None, None, None],
];
const T_R1: PieceGrid = [
    [None, Some(Piece::T), None, None],
    [Some(Piece::T), Some(Piece::T), None, None],
    [None, Some(Piece::T), None, None],
    [None, None, None, None],
];
const T_R2: PieceGrid = [
    [None, Some(Piece::T), None, None],
    [Some(Piece::T), Some(Piece::T), Some(Piece::T), None],
    [None, None, None, None],
    [None, None, None, None],
];
const T_R3: PieceGrid = [
    [None, Some(Piece::T), None, None],
    [None, Some(Piece::T), Some(Piece::T), None],
    [None, Some(Piece::T), None, None],
    [None, None, None, None],
];

// ____   ____   ____   ____
// _xx_   x___   ____   _x__
// xx__ → xx__ → _xx_ → _xx_
// ____   _x__   xx__   __x_
const S_R0: PieceGrid = [
    [None, None, None, None],
    [Some(Piece::S), Some(Piece::S), None, None],
    [None, Some(Piece::S), Some(Piece::S), None],
    [None, None, None, None],
];

const S_R1: PieceGrid = [
    [None, Some(Piece::S), None, None],
    [Some(Piece::S), Some(Piece::S), None, None],
    [Some(Piece::S), None, None, None],
    [None, None, None, None],
];

const S_R2: PieceGrid = [
    [Some(Piece::S), Some(Piece::S), None, None],
    [None, Some(Piece::S), Some(Piece::S), None],
    [None, None, None, None],
    [None, None, None, None],
];

const S_R3: PieceGrid = [
    [None, None, Some(Piece::S), None],
    [None, Some(Piece::S), Some(Piece::S), None],
    [None, Some(Piece::S), None, None],
    [None, None, None, None],
];

// ____   x___   _xx_   _x__
// _xx_   xx__   xx__   _xx_
// xx__ → _x__ → ____ → __x_
// ____   ____   ____   ____
const Z_R0: PieceGrid = [
    [None, None, None, None],
    [None, Some(Piece::Z), Some(Piece::Z), None],
    [Some(Piece::Z), Some(Piece::Z), None, None],
    [None, None, None, None],
];

const Z_R1: PieceGrid = [
    [Some(Piece::Z), None, None, None],
    [Some(Piece::Z), Some(Piece::Z), None, None],
    [None, Some(Piece::Z), None, None],
    [None, None, None, None],
];

const Z_R2: PieceGrid = [
    [None, Some(Piece::Z), Some(Piece::Z), None],
    [Some(Piece::Z), Some(Piece::Z), None, None],
    [None, None, None, None],
    [None, None, None, None],
];

const Z_R3: PieceGrid = [
    [None, Some(Piece::Z), None, None],
    [None, Some(Piece::Z), Some(Piece::Z), None],
    [None, None, Some(Piece::Z), None],
    [None, None, None, None],
];

// ____   _x__   x___   _xx_
// xxx_   _x__   xxx_   _x__
// __x_ → xx__ → ____ → _x__
// ____   ____   ____   ____
const L_R0: PieceGrid = [
    [None, None, None, None],
    [Some(Piece::L), Some(Piece::L), Some(Piece::L), None],
    [None, None, Some(Piece::L), None],
    [None, None, None, None],
];
const L_R1: PieceGrid = [
    [None, Some(Piece::L), None, None],
    [None, Some(Piece::L), None, None],
    [Some(Piece::L), Some(Piece::L), None, None],
    [None, None, None, None],
];
const L_R2: PieceGrid = [
    [Some(Piece::L), None, None, None],
    [Some(Piece::L), Some(Piece::L), Some(Piece::L), None],
    [None, None, None, None],
    [None, None, None, None],
];
const L_R3: PieceGrid = [
    [None, Some(Piece::L), Some(Piece::L), None],
    [None, Some(Piece::L), None, None],
    [None, Some(Piece::L), None, None],
    [None, None, None, None],
];

// ____   xx__   __x_   _x__
// xxx_   _x__   xxx_   _x__
// x___ → _x__ → ____ → _xx_
// ____   ____   ____   ____
const J_R0: PieceGrid = [
    [None, None, None, None],
    [Some(Piece::J), Some(Piece::J), Some(Piece::J), None],
    [Some(Piece::J), None, None, None],
    [None, None, None, None],
];
const J_R1: PieceGrid = [
    [Some(Piece::J), Some(Piece::J), None, None],
    [None, Some(Piece::J), None, None],
    [None, Some(Piece::J), None, None],
    [None, None, None, None],
];
const J_R2: PieceGrid = [
    [None, None, Some(Piece::J), None],
    [Some(Piece::J), Some(Piece::J), Some(Piece::J), None],
    [None, None, None, None],
    [None, None, None, None],
];
const J_R3: PieceGrid = [
    [None, Some(Piece::J), None, None],
    [None, Some(Piece::J), None, None],
    [None, Some(Piece::J), Some(Piece::J), None],
    [None, None, None, None],
];

fn rot_grid_table_entry(p: Piece, r: u8) -> &'static PieceGrid {
    match (p, r) {
        (Piece::O, _) => &O_R0,
        (Piece::I, 0) => &I_R0,
        (Piece::I, 1) => &I_R1,
        (Piece::I, 2) => &I_R2,
        (Piece::I, 3) => &I_R3,
        (Piece::T, 0) => &T_R0,
        (Piece::T, 1) => &T_R1,
        (Piece::T, 2) => &T_R2,
        (Piece::T, 3) => &T_R3,
        (Piece::S, 0) => &S_R0,
        (Piece::S, 1) => &S_R1,
        (Piece::S, 2) => &S_R2,
        (Piece::S, 3) => &S_R3,
        (Piece::Z, 0) => &Z_R0,
        (Piece::Z, 1) => &Z_R1,
        (Piece::Z, 2) => &Z_R2,
        (Piece::Z, 3) => &Z_R3,
        (Piece::L, 0) => &L_R0,
        (Piece::L, 1) => &L_R1,
        (Piece::L, 2) => &L_R2,
        (Piece::L, 3) => &L_R3,
        (Piece::J, 0) => &J_R0,
        (Piece::J, 1) => &J_R1,
        (Piece::J, 2) => &J_R2,
        (Piece::J, 3) => &J_R3,
        (_, r) => panic!("rotation out of range: {r}"),
    }
}

type VecPieceGrid = Vec<Vec<Option<Piece>>>;

/// Backing table: the 28 piece×rotation literals converted once to
/// `Vec<Vec<Option<Piece>>>` so `Params::rot_grid` returns a `&'static`
/// reference into it, never allocating per call (D-Rust3). The resulting
/// four levels of `Vec` nesting cost extra pointer hops vs. a flat array,
/// but grids are tiny (≤16 cells) and accessed rarely per frame, and
/// `rot_grid`'s `&'static Vec<Vec<_>>` return type already requires this
/// shape at the call boundary since `PW` is a runtime value, not a const
/// generic.
static ROT_GRID_TABLE: LazyLock<Vec<Vec<VecPieceGrid>>> = LazyLock::new(|| {
    Piece::all()
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

/// Index is position within `Piece::all()`'s order, not a hand-written
/// per-variant match — since `ROT_GRID_TABLE` is built by iterating that
/// same slice, this keeps the two in agreement by construction even if
/// variant order changes. The O(7) linear scan is cheap enough not to trade
/// away for a hand-maintained match.
fn piece_index(p: Piece) -> usize {
    Piece::all()
        .iter()
        .position(|&q| q == p)
        .expect("p is a Piece variant, always in Piece::all()")
}

// ── Params impl ───────────────────────────────────────────────────────────

impl Params for Tetris {
    type Piece = Piece;
    type CellExtra = std::convert::Infallible;

    const PW: i64 = PW;
    const FY: i64 = FY;
    const FX: i64 = FX;

    fn piece_all() -> &'static [Piece] {
        Piece::all()
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
