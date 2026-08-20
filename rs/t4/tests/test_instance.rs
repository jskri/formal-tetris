// spec: tests/test_instance.rs — test fixture (§2, §9, `implementation.md`).
//
// Splices `t1`'s fixture via `include!` (§2), then adds two
// `t4::model::Params` impls differing only in `NEXT_LEN` (§9):
//
// - `TestInstance` (`NEXT_LEN = 3`): short, hand-traceable, crosses exactly
//   one bag boundary per draw sequence.
// - `TestInstanceWide` (`NEXT_LEN = 5`): crosses at least two bag
//   boundaries per full preview cycle.

#![allow(dead_code)]

include!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../t1/tests/test_instance.rs"
));

/// spec: NextLen — short, hand-traceable value (§9 above).
impl t4::model::Params for TestInstance {
    const NEXT_LEN: i64 = 3;
}

/// Second `Params` marker type, delegating to `TestInstance` for every item
/// but `NEXT_LEN` — not a duplicated fixture (§9).
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

/// spec: NextLen — wider value, crossing multiple bag boundaries per cycle
/// (§9 above).
impl t4::model::Params for TestInstanceWide {
    const NEXT_LEN: i64 = 5;
}
