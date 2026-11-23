# `itoa` annotated for Verus

`src/` is itoa `master` (9339ca9, v1.0.19) with Verus specifications and proofs added in place.
Results, the specification, the trusted base and the audited list of code changes are in
[`../VERIFICATION.md`](../VERIFICATION.md); the full diff against upstream is
[`../upstream.diff`](../upstream.diff).

- `src/lib.rs`, `src/u128_ext.rs`: upstream code, verified (inside `verus! { ... }` blocks):
  all the digit generation (`Unsigned::fmt` for `u8`..`u128`, `enc_16lsd`, `div_rem_1e16`,
  `mulhi`, `divmod100`, the `DECIMAL_PAIRS` table), the signed formatting (`Signed::fmt`) and
  `Buffer::new`/`Default`/`Clone`.
- `src/trusted.rs`: upstream code that is trusted, not verified. Verus skips the module
  (`#[verifier::external]` on its declaration). It holds the two raw-pointer reinterpretations
  (`Buffer::format`, `slice_buffer_to_str`) and the `Integer`/`Sealed` impls whose `write` calls them.
- `src/spec.rs`: the specification (`dec`, `dec_int`, `holds`, ...) and the lemmas. Ghost code only;
  nothing in it is trusted.
- `src/std_ext.rs`: verified stand-ins for `<[T]>::get_unchecked` and
  `<[T]>::get_unchecked_mut(..).write(..)`, which vstd does not specify.
- `tests/`, `benches/`: unchanged from upstream.

Scripts in `../`:
- `negative_controls.py`: injected bugs that Verus must reject.
- `check_trusted.py`: `src/trusted.rs` is verbatim upstream, except the one expected change.

## Reproduce

Verus 0.2026.11.22.1ce6a59 (the bare `verus` binary with its bundled vstd). Run from this directory:

    verus --crate-type=lib --no-cheating src/lib.rs        # 105 verified, 0 errors

Normal build and the upstream tests (ghost code erased; toolchain pinned to 1.100.0 by
`rust-toolchain.toml`):

    cargo build && cargo test && cargo test --release
    cargo build --tests --features no-panic --release
    cargo bench --no-run
