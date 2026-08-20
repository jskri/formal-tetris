//! spec: instance.rs — concrete instantiation (§11, `implementation.md`).
//!
//! A new, distinct `Tetris` marker type is needed (not a further `impl` on
//! `t1::instance::Tetris`) since `CellExtra` must differ here
//! (`crate::model::Garbage`, not `Infallible`) and `Params` bundles every
//! item into one trait (§0.1/§11). Every other item just delegates to
//! `t1::instance::Tetris`'s own values rather than restating them.

use t1::model::Params as T1Params;

/// No `T7.v` counterpart — `Garbage` is unit-valued, so every garbage cell
/// renders identically (§11). Lives here, not in `model.rs`, so `model.rs`
/// stays free of any rendering dependency (`macroquad`).
impl t1::view::Colored for crate::model::Garbage {
    fn color(&self) -> [f32; 4] {
        crate::view::GARBAGE_BLOCK_COLOR
    }
}

/// A new, distinct `Tetris` marker type (not `t1::instance::Tetris` itself)
/// — see this module's own header comment for why.
pub struct Tetris;

impl T1Params for Tetris {
    type Piece = t1::instance::Piece; // the exact same real Piece type — its own Colored impl (t1::instance) already applies, unchanged
    type CellExtra = crate::model::Garbage;

    const PW: i64 = <t1::instance::Tetris as T1Params>::PW;
    const FY: i64 = <t1::instance::Tetris as T1Params>::FY;
    const FX: i64 = <t1::instance::Tetris as T1Params>::FX;

    fn piece_all() -> &'static [t1::instance::Piece] {
        <t1::instance::Tetris as T1Params>::piece_all()
    }
    fn initial_main_grid() -> &'static Vec<Vec<bool>> {
        <t1::instance::Tetris as T1Params>::initial_main_grid()
    }
    fn forbidden_grid() -> &'static Vec<Vec<bool>> {
        <t1::instance::Tetris as T1Params>::forbidden_grid()
    }
    fn rot_grid(p: t1::instance::Piece, r: u8) -> &'static Vec<Vec<Option<t1::instance::Piece>>> {
        <t1::instance::Tetris as T1Params>::rot_grid(p, r)
    }
    fn initial_y(p: t1::instance::Piece) -> i64 {
        <t1::instance::Tetris as T1Params>::initial_y(p)
    }
    fn initial_x(p: t1::instance::Piece) -> i64 {
        <t1::instance::Tetris as T1Params>::initial_x(p)
    }
}

/// spec: `T4.v`'s own `NextLen` — unchanged from `t1::instance::Tetris`'s
/// own value; no parameter beyond `CellExtra` is new to this layer (§13).
impl t4::model::Params for Tetris {
    const NEXT_LEN: i64 = <t1::instance::Tetris as t4::model::Params>::NEXT_LEN;
}

// `T5.v`/`T6.v` declare no `Parameter` of their own — `t5::model::Params`
// is the one remaining distinct trait in the chain (`t6::model::Params` is
// a `pub use` alias of it, `t2`/`t3`'s own traits aren't separately
// nameable items), so no separate impl exists to add for either.
impl t5::model::Params for Tetris {}

/// spec: `T7.v`'s new parameters are runtime roster facts, not `Params`
/// items (§0.2) — this impl only satisfies the `CellExtra` bound
/// `t7::model::Params` adds, already discharged above.
impl crate::model::Params for Tetris {}

/// `piece_color` is **not** re-exported here — `t7::view` takes it as an
/// explicit closure parameter (same convention every prior layer's own
/// `render` uses) rather than hardcoding it inside a function generic over
/// `P: Params`. Callers import `t1::instance::piece_color` directly.
pub use t1::instance::Piece;
