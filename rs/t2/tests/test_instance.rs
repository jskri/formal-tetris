// spec: tests/test_instance.rs — test fixture (§9). `T2.v` adds no new
// abstract parameters (§13), so this is a compile-time pointer to
// `t1/tests/test_instance.rs` rather than a second copy. The
// `CARGO_MANIFEST_DIR`-anchored path stays correct regardless of the
// directory `cargo test` is invoked from.
//
// Also compiles as its own (empty) integration-test binary, same as the
// included file.

include!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../t1/tests/test_instance.rs"
));
