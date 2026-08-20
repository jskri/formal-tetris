//! Concrete instantiation of `model::Params` (§11, §13, `implementation.md`).
//!
//! `T5.v` declares no abstract parameter of its own — this impl's body is empty, the
//! same mechanical shape every other layer's `instance.rs` uses (contrast
//! `t4::instance`'s `NEXT_LEN`). Piece shapes, grid, colours, and `NEXT_LEN` are
//! unchanged from `t1::instance`/`t4::instance`.

pub use t4::instance::{piece_color, Piece, Tetris};

impl crate::model::Params for Tetris {}
