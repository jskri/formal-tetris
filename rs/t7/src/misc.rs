//! spec: misc.rs — `Action` shape for `T7.v` (§15.6, `implementation.md`).
//!
//! T7 adds no new *player-facing* action — network events (`Receive`/
//! `Disconnect`/`Notice`) are never player input, dispatched from
//! `net.rs`/`main.rs` instead of a keybinding (`implementation.md` §15.6).

pub use t6::misc::*;
