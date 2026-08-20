//! Concrete instantiation of `t1::model::Params` (§11). `T2.v` introduces
//! no new abstract parameters, so this re-exports `t1::instance`'s items
//! rather than restating them.

pub use t1::instance::{piece_color, Piece, Tetris};
