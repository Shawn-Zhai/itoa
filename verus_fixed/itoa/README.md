# `itoa` annotated for Verus (amended)

`src/` is itoa `master` (9339ca9, v1.0.19) with Verus specifications and proofs added in place.
This is the amended version of `../../verus/itoa`, after the review against the developer-written
spec. The review is in [`../SPEC_REVIEW.md`](../SPEC_REVIEW.md). Results, the specification, the
trusted base and the audited list of code changes are in [`../VERIFICATION.md`](../VERIFICATION.md).
The full diff against upstream is [`../upstream.diff`](../upstream.diff).

- `src/lib.rs`, `src/u128_ext.rs`: upstream code, verified (inside `verus! { ... }` blocks).
  - The public API: `Buffer::format`, `Buffer::new`/`Default`/`Clone`, and the `Integer`/`Sealed`
    impls with `write` for all 12 integer types.
  - All the digit generation: `Unsigned::fmt` for `u8`..`u128`, `enc_16lsd`, `div_rem_1e16`, `mulhi`,
    `divmod100`, the `DECIMAL_PAIRS` table.
  - The signed formatting (`Signed::fmt`).
  - The developer's contracts are stated next to Claude's (marked `// Human spec`).
- `src/trusted.rs`: the trusted code. Two `#[verifier::external_body]` functions with explicit
  contracts: `buffer_of` (the raw-pointer cast of `Buffer::format`) and `slice_buffer_to_str`.
- `src/spec.rs`: Claude's specification (`dec`, `dec_int`, `holds`, ...) and its lemmas.
- `src/human_spec.rs`: the developer's spec functions (`decimal_unsigned`, `decimal_signed`,
  `is_decimal_text`, ...), transcribed.
- `src/spec_equiv.rs`: lemmas showing that the two specifications describe the same text.
- `src/verified_examples.rs`: verified clients of `Buffer::format` (compiled only under Verus).
- `src/std_ext.rs`: verified stand-ins for `<[T]>::get_unchecked` and
  `<[T]>::get_unchecked_mut(..).write(..)`, which vstd does not specify.
- `tests/`, `benches/`: unchanged from upstream.

`spec.rs`, `human_spec.rs`, `spec_equiv.rs` and `verified_examples.rs` are ghost code only:
normal builds erase them, and nothing in them is trusted.

Scripts in `../`:
- `negative_controls.py`: injected bugs that Verus must reject.
- `check_trusted.py`: the trusted bodies are upstream code, and the verified shells keep upstream's
  statements.

## Reproduce

Verus 0.2026.05.03.8b81855 (the bare `verus` binary with its bundled vstd). Run from this directory:

    verus --crate-type=lib src/lib.rs                  # 165 verified, 0 errors
    verus --crate-type=lib --no-cheating src/lib.rs    # reports exactly the 2 trusted items

Normal build and the upstream tests (ghost code erased; toolchain pinned to 1.95.0 by
`rust-toolchain.toml`):

    cargo build && cargo test && cargo test --release
    cargo build --tests --features no-panic --release
    cargo bench --no-run
