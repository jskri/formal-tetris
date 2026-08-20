//! Concrete instantiation of `t1::model::Params` (§11, `implementation.md`).
//!
//! `T3.v` introduces no abstract parameters beyond `T1.v`'s, so this module
//! re-exports `t2::instance`'s items (themselves a re-export of
//! `t1::instance`'s) rather than restating them.

pub use t2::instance::{piece_color, Piece, Tetris};
