//! Library root. Every module here is public so another binary can reuse
//! T7's networking (`net`/`session`) and UI (`app`/`text`) layers without
//! reimplementing them (`implementation.md` §0.4); this crate's own
//! `main.rs` is written against exactly this public surface.

pub mod app;
pub mod instance;
pub mod misc;
pub mod model;
pub mod net;
pub mod session;
pub mod text;
pub mod view;
