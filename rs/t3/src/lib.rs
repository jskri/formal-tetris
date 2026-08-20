#![deny(warnings)]
//! Library root. Exists so integration tests under `tests/` (separate
//! crates) can reach `model`/`instance`/`view` via `t3::...` — `main.rs`
//! alone cannot be linked against from `tests/`.

pub mod instance;
pub mod misc;
pub mod model;
pub mod view;
