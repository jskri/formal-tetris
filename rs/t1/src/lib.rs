#![deny(warnings)]
//! Library root, letting `tests/` (separate crates) reach these modules —
//! `main.rs` alone isn't linkable from `tests/`.

pub mod instance;
pub mod misc;
pub mod model;
pub mod view;
