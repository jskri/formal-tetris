//! spec: view.rs — renderer (§14, `implementation.md`).
//!
//! §14: pure re-export, no new state to render — `t5::view::render` already
//! draws the piece generically, not through any rotation-specific path.

pub use t5::view::*;
