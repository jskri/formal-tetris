#![deny(warnings)]
//! Library root. Exists so integration tests under `tests/` (separate
//! crates) can reach `model`/`instance`/`view` via `t2::...` — `main.rs`
//! alone cannot be linked against from `tests/`.

pub mod instance;
pub mod model;
pub mod view;
