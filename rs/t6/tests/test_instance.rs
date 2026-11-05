// spec: tests/test_instance.rs — test fixture (§2, §9, `implementation.md`).
//
// `include!`s `t1`'s fixture directly, because nested `#[path]` module
// includes resolve unreliably. `TestInstanceWide` is re-declared below.
//
// Identical to `t5/tests/test_instance.rs`: the `impl t5::model::Params`
// blocks below already satisfy `t6::model::Params` (§6.0). Duplicated
// rather than shared as compiled code (§9's per-crate-fixture convention).

#![allow(dead_code)]

include!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../t1/tests/test_instance.rs"
));

/// `t4`'s own second marker type (`t4/tests/test_instance.rs`), restated
/// here rather than reached through it — module doc comment above.
#[allow(dead_code)]
pub struct TestInstanceWide;

impl t1::model::Params for TestInstanceWide {
    type Piece = Piece; // TestInstance's own Piece enum, from the included fixture
    type CellExtra = std::convert::Infallible;

    const PW: i64 = <TestInstance as t1::model::Params>::PW;
    const FY: i64 = <TestInstance as t1::model::Params>::FY;
    const FX: i64 = <TestInstance as t1::model::Params>::FX;

    fn piece_all() -> &'static [Piece] {
        <TestInstance as t1::model::Params>::piece_all()
    }
    fn initial_main_grid() -> &'static Vec<Vec<bool>> {
        <TestInstance as t1::model::Params>::initial_main_grid()
    }
    fn forbidden_grid() -> &'static Vec<Vec<bool>> {
        <TestInstance as t1::model::Params>::forbidden_grid()
    }
    fn rot_grid(p: Piece, r: u8) -> &'static Vec<Vec<Option<Piece>>> {
        <TestInstance as t1::model::Params>::rot_grid(p, r)
    }
    fn initial_y(p: Piece) -> i64 {
        <TestInstance as t1::model::Params>::initial_y(p)
    }
    fn initial_x(p: Piece) -> i64 {
        <TestInstance as t1::model::Params>::initial_x(p)
    }
}

/// spec: NextLen — short, hand-traceable value, matching `t5/tests/test_instance.rs`'s
/// own choice exactly (so any golden vector hand-traced against that file's
/// doc comments still applies verbatim to `t6`'s `TestInstance` too).
impl t4::model::Params for TestInstance {
    const NEXT_LEN: i64 = 3;
}
/// spec: NextLen — wider value, matching `t5/tests/test_instance.rs`'s own
/// choice exactly, same reasoning as above.
impl t4::model::Params for TestInstanceWide {
    const NEXT_LEN: i64 = 5;
}

/// spec: `T5.v` declares no `Parameter` of its own (§6.0, §11) — both
/// impls below are empty, and also satisfy `t6::model::Params` (module doc
/// comment above).
impl t5::model::Params for TestInstance {}
impl t5::model::Params for TestInstanceWide {}
