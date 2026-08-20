// spec: tests/test_instance.rs — test fixture (§2, §9).
//
// Includes `t1`'s fixture directly rather than nesting through `t4`'s own
// `test_instance.rs`: a third level of `include!`-based `#[path]` nesting
// hit a reproducible `rustc` module-resolution quirk (a nested `#[path]`
// module's own `#[path]` children resolving against an unexpected base
// directory) — sidestepped rather than chased further. `TestInstanceWide`
// is therefore re-declared below (five lines of `t1::model::Params`
// delegation) instead of reached through `t4`'s copy — harmless, since
// every model's own fixture is already a distinct compilation-unit-local
// copy, not shared code.

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

/// spec: NextLen — matches `t4/tests/test_instance.rs`'s value (3),
/// unchanged, so hand-traced golden vectors against it still apply.
impl t4::model::Params for TestInstance {
    const NEXT_LEN: i64 = 3;
}
/// spec: NextLen — matches `t4/tests/test_instance.rs`'s wide value (5),
/// same reasoning.
impl t4::model::Params for TestInstanceWide {
    const NEXT_LEN: i64 = 5;
}

/// spec: `T5.v` declares no `Parameter` of its own (`implementation.md`
/// §6.0, §11) — both impls below are empty.
impl t5::model::Params for TestInstance {}
impl t5::model::Params for TestInstanceWide {}
