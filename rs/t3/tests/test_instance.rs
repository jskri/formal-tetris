// spec: tests/test_instance.rs — test fixture (§2, §9, `implementation.md`).
//
// Re-exports t1's fixture verbatim rather than copying it: `T3.v` introduces
// no new abstract parameters (§13), so there is nothing to add. `include!`
// splices the file's content at compile time, so there remains exactly one
// copy of the fixture in the workspace — `t1/tests/test_instance.rs` — this
// file is only a compile-time pointer to it, exactly as `t2/tests/test_instance.rs`
// already does one layer down.
//
// `include!`, not `#[path = "..."] mod fixture;`, because each `tests/*.rs`
// file is its own integration-test binary crate, and `t1`'s fixture lives
// under `t1/tests/`, not in `t1`'s library surface — nothing under `t1/tests/`
// is reachable via `use t1::...` from another crate's test binary. Declaring
// it as a named module from here (`#[path = "../../t1/tests/test_instance.rs"]
// mod inner;`) would work, but nests everything one level deeper
// (`fixture::inner::TestInstance`), breaking the flat `fixture::TestInstance`
// path every model's `model_unit_test.rs`/`model_properties_test.rs`/
// `model_fuzz_test.rs`/`oracle.rs` relies on. `include!` splices the fixture's
// items in directly, so `fixture::TestInstance` resolves identically whether
// `fixture` points at this file (t2, t3) or is the fixture itself (t1).
//
// Like the original, this file is also compiled by cargo as its own (empty)
// integration-test binary, and the included content's own
// `#![allow(dead_code)]` (present at the top of `t1/tests/test_instance.rs`)
// covers that build.

include!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../t1/tests/test_instance.rs"
));
