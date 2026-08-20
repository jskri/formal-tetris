//! Concrete instantiation of `model::Params` (§11, §13, `implementation.md`).
//!
//! `T4.v` adds exactly one abstract parameter beyond `T1.v`'s: `NextLen`.
//! Rather than defining a new instance type, this module adds a
//! `t4::model::Params` impl for the existing `t1::instance::Tetris` — legal
//! under Rust's orphan rule, since `Params` is local to this crate. Piece
//! shapes, grid, and colours are unchanged from `t1::instance`/
//! `t3::instance`; only `NEXT_LEN` is genuinely new here.

pub use t3::instance::{piece_color, Piece, Tetris};

impl crate::model::Params for Tetris {
    const NEXT_LEN: i64 = 6;
}
