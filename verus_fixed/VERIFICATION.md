# Verifying `itoa` with Verus (2026-11-09; amended 2026-11-13)

Crate: `itoa` 1.0.19, this fork's `master` @ 9339ca9. Verus 0.2026.05.03.8b81855 (the bare
`verus` binary and its bundled vstd); the normal build uses rustc 1.95.0. Annotated crate:
[`itoa/`](itoa/). Diff against upstream: [`upstream.diff`](upstream.diff). Specifications and
proofs were written by Claude (Opus 5.5) in Claude Code on 2026-11-09, from the crate's
documentation, its tests and the code (first pass: [`../verus/`](../verus/)).

On 2026-11-13 the first pass was reviewed against the developer-written spec in
[`../verus_human_written_spec/`](../verus_human_written_spec/). Claude's verified contracts were
right, but the crate's public API (`Buffer::format`, the `write` methods, `slice_buffer_to_str`)
had been left as trusted code without any contract. This folder is the amended version: `format`
and every `write` are verified against contracts that include the developer's; the trusted code is
two raw-pointer reinterpretations with explicit contracts; and the developer's contracts are stated
and verified on every function they cover. The review, including the mistakes found in the
developer's spec, is in [`SPEC_REVIEW.md`](SPEC_REVIEW.md); every hand edit against `../verus/` is
in [`amendments.diff`](amendments.diff).

## Headline

| | |
|---|---|
| Verus | **165 verified, 0 errors**, about 5 s wall clock |
| Trust markers (`verus --no-cheating`) | **exactly 2**, both `#[verifier::external_body]` in [`trusted.rs`](itoa/src/trusted.rs): `buffer_of` and `slice_buffer_to_str`. No `assume`, `admit`, `assume_specification`, axioms or `uninterp` |
| Verified | the public API: `Buffer::format`, `new`, `Default`, `Clone`, and `write` for all 12 integer types; all digit generation: `Unsigned::fmt` for `u8`..`u128`, `enc_16lsd`, `div_rem_1e16` (including its Granlund–Montgomery constant), `mulhi`, `divmod100`, the `DECIMAL_PAIRS` table; the signed formatting (`Signed::fmt`, 5 types); `MAX_STR_LEN` for all 12 types |
| Trusted, not verified | 4 statements of upstream code: the raw-pointer cast of `Buffer::format` (now `buffer_of`) and the body of `slice_buffer_to_str`, each with a contract Verus checks at every call ([`check_trusted.py`](check_trusted.py) checks that they are upstream's code) |
| Developer's contracts | stated on every function they cover (marked `// Human spec`), all verified; `slice_buffer_to_str`'s is proved from its trusted contract |
| Normal `cargo build` of the annotated crate | passes, 0 warnings; also `--features no-panic --release` and `--no-default-features`; `cargo clippy` with upstream's pedantic flags passes |
| Upstream tests on the annotated crate | 11/11 integration, 2/2 doc (debug and release) |
| Differential test | 8,144,968 values: annotated == upstream == `std`, every integer type, built with `no-panic` |
| Machine code | `Buffer::format` compiles to the same instructions as in the first pass, for all 12 types |
| Negative controls | 28/28 injected bugs rejected ([`negative_controls.py`](negative_controls.py)) |
| Proof stability | same result with SMT seeds 0 to 39, 42 and 1234 |

## The specification

Claude's definitions are in [`itoa/src/spec.rs`](itoa/src/spec.rs) (unchanged from the first pass):

- `dec(n: nat) -> Seq<u8>`: the decimal representation of `n` in ASCII, without leading zeros
  (`"0"` for zero). It is defined through `dec_pad(n, k)`, the `k` low digits of `n` zero-padded,
  and `num_digits(n)`. `lemma_dec_value` shows that it is the usual notation: it consists of the
  bytes `b'0'..=b'9'`, its value (Horner's rule) is `n`, and it has no leading zero unless it is
  `"0"`. These three facts determine it.
- `dec_int(n: int)`: `'-'` followed by `dec(-n)` for negative `n`, otherwise `dec(n)`.
- `holds(buf, start, bytes)`: the `MaybeUninit<u8>` buffer `buf` holds the initialized bytes
  `bytes` at `start..start + bytes.len()` (vstd's `mem_contents() == MemContents::Init(b)`).
- `unchanged_outside(new, old, lo, hi)`: `new` agrees with `old` outside `lo..hi`.

The developer's definitions are in [`itoa/src/human_spec.rs`](itoa/src/human_spec.rs), transcribed
unchanged except for one definition:

- `decimal_unsigned(n: nat) -> Seq<char>`, `decimal_signed(n: int) -> Seq<char>`: the decimal
  representation as chars, which is how vstd views a `&str`.
- `is_decimal_text(s)`: non-empty, digits only, except an optional leading `'-'` followed by at
  least one digit.
- `initialized_ascii_suffix(buf, offset)`: every element of `buf` from `offset` on is initialized
  and below 128. (The developer declared it `uninterp`, so nothing could establish it; see H2 in
  `SPEC_REVIEW.md`.)

[`itoa/src/spec_equiv.rs`](itoa/src/spec_equiv.rs) proves that the two are the same text:
`ascii_chars(dec(n)) == decimal_unsigned(n)` and `ascii_chars(dec_int(n)) == decimal_signed(n)`,
where `ascii_chars` maps each byte to the char with that code. It also connects bytes to strings:
a `&str` whose UTF-8 bytes (vstd's `spec_bytes()`) are ASCII has one char per byte
(`lemma_ascii_str`, from vstd's UTF-8 lemmas).

### Contracts

| Item | Status | Contract |
|---|---|---|
| `Buffer::format<I>(&mut self, i: I) -> &str` | verified | `result@ == decimal_signed(i.spec_int())`: exactly the decimal representation of `i`. Developer's: `is_decimal_text(result@)`, `1 <= result@.len() <= I::MAX_STR_LEN` |
| `Sealed::write(self, buf: &mut Self::Buffer) -> &str` (trait) | verified (12 impls) | `result@ == decimal_signed(self.spec_int())`. Developer's: `is_decimal_text(result@)`, `1 <= result@.len() <= 40` |
| `write` for `u8`..`u128` / `i8`..`i128`, `isize` / `usize` | verified | developer's: `result@ =~= decimal_unsigned(self as nat)` (unsigned) or `decimal_signed(self as int)` (signed, `usize`, `isize`), and `result@.len() <= Self::MAX_STR_LEN` |
| `Buffer::new`, `Default`, `Clone` | verified | developer's: `result.len() == i128::MAX_STR_LEN` (`len` is a closed spec function) |
| `Integer::MAX_STR_LEN` (12 types) | verified | `Integer::lemma_max_str_len`: every value's text fits, and `MAX_STR_LEN <= 40`. The `lemma_max_str_len_*` lemmas: for the 10 fixed-width types, `MAX_STR_LEN` is exactly the length of the longest representation (`T::MAX`, or `T::MIN` with its sign), as documented; `usize`/`isize` equal their primitive's |
| `Unsigned::fmt::<N>(self, buf: &mut [MaybeUninit<u8>; N])` (`u8`..`u128`) | verified | requires `dec(self).len() <= N`. Returns `offset` with `offset + dec(self).len() == N`; `buf[offset..N]` holds `dec(self)`; nothing else in `buf` changes. Developer's: `offset < N`, `N - offset == decimal_unsigned(self).len()` |
| `Signed::fmt::<N>` (`i8`..`i128`) | verified | the same with `dec_int(self)` |
| `enc_16lsd(buf, offset, n)` | verified | requires `n < 10^16`, `offset + 16 <= buf.len()`. `buf[offset..offset + 16]` holds `dec_pad(n, 16)`; nothing else changes. Developer's: the length is unchanged |
| `div_rem_1e16(n)` | verified | returns `(n / 10^16, n % 10^16)` for every `u128`. Developer's: also the bound and `q * 10^16 + r == n` |
| `mulhi(x, y)` | verified | returns `x * y / 2^128` for every pair of `u128` (also in the developer's notation) |
| `divmod100(v)` | verified | requires `v < 10_000` (upstream's `debug_assert!`). Returns `(v / 100, v % 100)`. Developer's: also `r.1 < 100` and `r.0 * 100 + r.1 == v` |
| `DECIMAL_PAIRS` | verified | the table is `decimal_pairs()`: entries `2p` and `2p + 1` are the two digits of `p` |
| `slice_buffer_to_str(buf, offset)` | **trusted** (T3) | requires `offset <= buf.len()` and `initialized_ascii_suffix(buf, offset)` (the developer's precondition); ensures `result.spec_bytes() == suffix_bytes(buf@, offset)`, the initialized bytes `buf[offset..]`. The developer's postcondition (length, ASCII) is proved from it (`lemma_slice_buffer_to_str_human`) |
| `buffer_of::<I>(bytes)` | **trusted** (T1) | no contract needed: `write` accepts any buffer |

`spec_int` (the value of `self`, in `Sealed`) and `lemma_max_str_len` (in `Integer`) are ghost
items: normal builds erase them, so the public API is unchanged. They are what lets the generic
`format` have an exact contract (H4 in `SPEC_REVIEW.md`).

[`itoa/src/verified_examples.rs`](itoa/src/verified_examples.rs) shows the contract in use: Verus
proves that `format(128u64)` is `"128"` and `format(1234i32)` is `"1234"` (upstream's doc examples),
`format(-128i8)` is `"-128"`, `format(0u128)` is `"0"`, and that `i8::MIN` and `u16::MAX` print
exactly `MAX_STR_LEN` chars.

### What the proofs establish about upstream's reasoning

- **Absence of panics, out-of-bounds accesses and undefined behaviour** in all verified code. This
  covers every index that upstream accesses with `get_unchecked(_mut)`, the `expect` calls in the
  `u8`..`u64` loop (never reached for `u8`, always `Ok` otherwise), all arithmetic, and the
  `unreachable_unchecked` in `Buffer::format` (the length check before it never succeeds).
- **Division by multiplication.** `divmod100`'s `(v * 5243) >> 19` is exact for `v < 10^4`.
  `div_rem_1e16`'s `mulhi(n, M_HIGH) >> 51` is exact for every `u128`: with `q = n / 10^16`,
  `n * M_HIGH = q * 2^179 + (q * e + r * M_HIGH)` where `e = M_HIGH * 10^16 - 2^179 = 630438908198912`,
  and the second term stays below `2^179` because `(q + 1) * e < M_HIGH`
  (`lemma_div_1e16_multiplier`). `mulhi` is proved against the exact 256-bit product.
- **The room for the sign.** `i64::MAX_STR_LEN` equals `u64::MAX_STR_LEN` (both 20), so upstream
  formats `|x|` into the whole `i64` buffer and relies on `|i64::MIN| = 2^63` having only 19 digits
  for the `'-'`. `Signed::fmt` proves this, and the analogous fact for the other types.
- **The safety conditions of the trusted code.** Verus proves the precondition of
  `slice_buffer_to_str` at each of its calls: `buf[offset..]` is initialized and ASCII.

No bug was found in the crate.

## Trusted base

All trusted code is in [`itoa/src/trusted.rs`](itoa/src/trusted.rs): two functions marked
`#[verifier::external_body]`. Verus does not check their bodies, but checks every call against
their contracts. `verus --no-cheating` reports exactly these two. Their bodies are upstream's code
(`python3 check_trusted.py` from `verus_fixed/` checks this, and also that the verified `format` and
`write` methods keep upstream's statements).

| id | Item | Upstream code | Why it cannot be verified |
|---|---|---|---|
| T1 | `buffer_of` | the cast in `Buffer::format`: `self.bytes.as_mut_ptr().cast::<I::Buffer>()` and `&mut *buf_ptr` (2 statements) | reinterprets the `[MaybeUninit<u8>; 40]` buffer as `I::Buffer` through a raw pointer. vstd's raw-pointer model needs a `PointsTo` permission, which a `&mut` reference does not provide |
| T3 | `slice_buffer_to_str` | the whole body (2 statements) | reinterprets `&[MaybeUninit<u8>]` as `&[u8]` through a raw pointer, and `get_unchecked(offset..)` is unspecified. (`str::from_utf8_unchecked`, which ends it, is specified by vstd) |

T2 of the first pass (the `Integer`/`Sealed` impls, 82 upstream lines) is verified now.

**Obligations on the trusted code.** These hold by inspection, not by proof:

- T1: for every `I: Integer`, `I::Buffer` is an array of `I::MAX_STR_LEN` elements of
  `MaybeUninit<u8>` (`impl_Integer!`, `impl_Integer_size!`), and Verus proves
  `I::MAX_STR_LEN <= 40` (`Integer::lemma_max_str_len`). So the cast stays inside `self.bytes`, and
  `MaybeUninit<u8>` has no alignment or validity requirement. It needs no contract, since `write`
  accepts any buffer.
- T3: the contract is what the body does. `get_unchecked(offset..)` needs `offset <= buf.len()`.
  Reading the elements as `u8` needs them initialized. `str::from_utf8_unchecked` needs valid UTF-8,
  which ASCII bytes are (`lemma_ascii_str` proves it). Its vstd specification
  (`res.spec_bytes() =~= v@`) is the `ensures`.

**Trusted outside the crate:**

- vstd's specifications of the std items the verified code uses: `MaybeUninit::{new, uninit}` and
  `mem_contents`, array and slice indexing and index assignment, array-to-slice coercion, slice
  `len`, `str::len` and the UTF-8 view of `str` (`spec_bytes`), `hint::unreachable_unchecked`
  (`requires false`), `mem::size_of` with `layout_of_primitives`, `TryInto<u16/u32/u64>` for `i32`,
  `Result::expect`, and `From<u64> for u128`.
- Verus, Z3 and rustc; and the `verus!` macro, trusted to erase only ghost code, as Verus itself
  trusts it.

## Changes to the crate (audit of `upstream.diff`)

- `lib.rs`: 124 lines removed, 874 added. Most additions are contracts, proof blocks, lemmas and
  the `Signed` trait of the first pass.
- `u128_ext.rs`: 1 line changed (`mulhi`'s signature names its result, for the `ensures`), 153
  ghost lines added. Its executable code is unchanged.
- `Cargo.toml`: 2 lines removed, 10 added (unchanged from the first pass, whose report counted 9).
- New files: `spec.rs` (851 lines, ghost), `human_spec.rs` (88, ghost), `spec_equiv.rs` (236, ghost),
  `verified_examples.rs` (50, compiled only under Verus), `std_ext.rs` (55), `trusted.rs` (84),
  `rust-toolchain.toml`.
- `tests/`, `benches/` and the licenses are unchanged.

### Executable code

Every change computes the same result, writes the same bytes at the same positions and returns the
same offset as upstream. The upstream test suite passes unchanged, and the differential test below
compares the annotated crate with upstream on 8.1 million values. Rows marked *(fixed)* are new in
this folder; the others are from the first pass.

| Change | Where | Reason |
|---|---|---|
| *(fixed)* `let buf_ptr = self.bytes.as_mut_ptr().cast::<I::Buffer>();` and `i.write(unsafe { &mut *buf_ptr })` → `i.write(buffer_of::<I>(&mut self.bytes))`, with the two statements in `buffer_of` (`#[inline(always)]`) | `Buffer::format` | isolates the raw-pointer cast, so that the rest of `format`, including its `unreachable_unchecked`, is verified. Same machine code |
| *(fixed)* `const MAX_STR_LEN: usize = $Unsigned::MAX.ilog10() as usize + 1;` (and `+ 2`, and `<$primitive as Integer>::MAX_STR_LEN`) → plain constants `private::U8_MAX_STR_LEN`, ... (the developer's); the buffer types and `Buffer`'s field use them too | `impl_Integer!`, `impl_Integer_size!`, `Buffer`, `Buffer::new` | Verus crashes on an associated constant used as an array length, and cannot evaluate `ilog10`. Compile-time `assert!`s check the constants against upstream's formula; a Verus assertion checks the `usize`/`isize` ones against their primitive's |
| *(fixed)* `impl_Integer!` takes the two constants and two lemma names; `impl_Integer_size!` takes the constant (`impl_Integer_size!(usize as u64, U64_MAX_STR_LEN #[cfg(...)])`) | the macro invocations | to pass the constants and the per-type lemmas |
| *(fixed)* the `Integer`/`Sealed` impls are back in `lib.rs`, inside `verus!`; `mod trusted` is no longer `#[verifier::external]` | `lib.rs`, `trusted.rs` | they are verified now |
| `fn fmt(self, buf: &mut Self::Buffer)` → `fn fmt<const N: usize>(self, buf: &mut [MaybeUninit<u8>; N])` | `trait Unsigned` and its 5 impls | for signed types upstream formats into a subslice of the longer signed buffer, converted with `(&mut buf[offset..]).try_into().unwrap()`. Verus supports neither mutable range indexing nor slice-to-array `try_into`. `fmt` writes right-aligned from `buf.len()` down, so on the whole signed buffer the digits land in the same places |
| the signed formatting moved out of `Sealed::write` into the verified `trait Signed`, whose `fmt` calls `Unsigned::fmt` on the whole buffer, then writes `'-'` | `impl_Signed!`, the signed `write` | the returned offset equals upstream's `(Self::MAX_STR_LEN - $Unsigned::MAX_STR_LEN) + offset_in_subslice` |
| `self.unsigned_abs()` → `if self < 0 { (-(self + 1)) as $Unsigned + 1 } else { self as $Unsigned }` | `Signed::fmt` | vstd does not specify `unsigned_abs`. The expression uses only in-range casts. LLVM proves it identical to `unsigned_abs` and emits a symbol alias (checked for `i8`, `i64`, `i128`) |
| `buf.get_unchecked_mut(i).write(v)` → `write_unchecked(buf, i, v)`; `*DECIMAL_PAIRS.0.get_unchecked(j)` → `*get_unchecked(&DECIMAL_PAIRS.0, j)` | all digit writes in `fmt` | vstd does not specify `get_unchecked(_mut)`. The verified stand-ins in `std_ext.rs` index with a bounds check behind a branch to `unreachable_unchecked` that Verus proves dead, so the optimizer drops the check |
| `buf[i].write(v)` → `buf[i] = MaybeUninit::new(v)` | `enc_16lsd`, the zero case of `u128::fmt` | `MaybeUninit::write` is unspecified; it is `*self = MaybeUninit::new(val)` plus a returned reference that itoa discards |
| `b'0'`, `b'-'` → `48`, `45`; the byte-string table `*b"0001…99"` → a numeric array literal, with each row's string in a comment | `fmt`, `Signed::fmt`, `DECIMAL_PAIRS` | Verus does not support byte literals. Same bytes |
| `static DECIMAL_PAIRS` → `exec static DECIMAL_PAIRS … ensures …` | `DECIMAL_PAIRS` | Verus statics carry their property in `ensures`. Erases to the same `static` |
| `debug_assert!(value < 10_000)` removed | `divmod100` | panic macros are unsupported. It became `requires value < 10_000`, proved at every call site |
| `u128::MAX_STR_LEN` → `N` (5 places), comments `buf[23..39]` → `buf[N-16..N]` | `u128::fmt` | the buffer length, now generic: 39 for `u128` and 40 for `i128` |
| `fn enc_16lsd<const OFFSET: usize>(buf, n)` → `fn enc_16lsd(buf, offset: usize, n)`; `for quad_index in (1..4).rev()` → `let mut quad_index = 4; while quad_index > 1 { quad_index -= 1; … }` | `enc_16lsd` | `OFFSET` would have to be `N - 16`, a generic constant expression, which stable Rust rejects. Verus does not support `Rev`; the loop visits 3, 2, 1 as before |

### Build-only changes

- `Cargo.toml` gains a `vstd` dependency (`default-features = false`, so still `no_std`), which
  provides the `verus!` macro. No vstd function is called at run time.
- `rust-version` goes from 1.68 to 1.95, and `rust-toolchain.toml` pins 1.95.0 (vstd needs it).
- `publish = false`; `unexpected_cfgs` allows `verus_keep_ghost`.
- Ghost-only imports are `#[cfg(verus_keep_ghost)]`; under Verus the developer's spec functions are
  re-exported at the crate root, where the developer defined them.
- A second crate-level `#![allow(...)]` for four clippy lints that only the annotations trigger:
  `semicolon_if_nothing_returned` (erased `proof` blocks), `inline_always` (the stand-ins),
  `too_many_lines` (`u128::fmt`) and `ref_as_ptr` (applied to upstream's `slice_buffer_to_str` once
  `rust-version` is 1.76 or later). Without it, upstream's clippy CI step fails (C4 in
  `SPEC_REVIEW.md`).

### Ghost-only additions

- Contracts on 15 executable items: the first pass's 9 (`get_unchecked`, `write_unchecked`,
  `DECIMAL_PAIRS`, `divmod100`, `Unsigned::fmt`, `enc_16lsd`, `div_rem_1e16`, `Signed::fmt`,
  `mulhi`), and `Buffer::format`, `Buffer::new`, `Default::default`, `Clone::clone`,
  `Sealed::write` and `slice_buffer_to_str`. Invariants on 3 loops; 41 `proof` blocks in
  executable code.
- 63 lemma definitions (51 in the first pass), including the trait lemma
  `Integer::lemma_max_str_len` with its 12 impls, and the 8 lemmas of `spec_equiv.rs`.
- 35 spec functions: the first pass's, the developer's 5, `Buffer::len`, `Sealed::spec_int`,
  `all_ascii`, `ascii_chars` and `suffix_bytes`.
- 4 verified example functions (`verified_examples.rs`, compiled only under Verus).
- One `#[verifier::rlimit(50)]`, on `u128::fmt` (see "Proof engineering").

### Observable differences

- **Relative to the first pass: none.** `Buffer::format` compiles to identical instructions for all
  12 types (release build, x86-64; checked by comparing the assembly of a probe crate against each
  version). The public API is the same; the new trait items are ghost and erased.
- **Relative to upstream** (unchanged from the first pass). `Unsigned::fmt` is generic now, so it is
  instantiated, and usually inlined, in the calling crate. Upstream compiles it once, out of line,
  in itoa. In upstream's criterion benchmark (same machine, rustc 1.95.0, release), the first pass
  was equal or faster in 6 of 7 cases; `u128[0]` took 1.19 ns against 1.04 ns. Code size: one `fmt`
  instance per pair of type and buffer length. Debug builds: the removed `debug_assert!` and the
  overflow checks in the `unsigned_abs` expression cannot fail, by the proof. Dependencies and MSRV
  as listed above.

## Validation beyond the proof

- **Upstream CI steps** on the annotated crate: `cargo build`, `cargo test`, `cargo test --release`,
  `cargo build --no-default-features`, `cargo test --tests --no-default-features` (debug and release),
  `cargo build --tests --features no-panic --release`, `cargo bench --no-run`, and
  `cargo clippy --tests --benches -- -Dclippy::all -Dclippy::pedantic`. All pass with 0 warnings;
  `cargo doc --no-deps` too. Not run: Miri and `cargo docs-rs` (they need a nightly toolchain, which
  is not installed here), `cargo fuzz` and `cargo outdated`.
- **Differential test** (a scratch crate depending on the annotated crate and a renamed copy of
  upstream, both with `no-panic`, release): every `u8`, `i8`, `u16`, `i16`; for the wider types, all
  powers of two and ten and their neighbours, both signs, `MIN`, `MAX` and zero; and 1,000,000 random
  values of random bit length for each of `u32`, `i32`, `u64`, `i64`, `u128`, `i128`, `usize`,
  `isize`. 8,144,968 values, all formatted identically by the annotated crate, upstream and
  `to_string`. `MAX_STR_LEN` agrees for all 12 types.
- **`no-panic`.** The differential test formats `black_box`ed values of all 12 types with the
  feature enabled in release mode and links, so no panic path survives.

## Negative controls (all rejected)

Each mutant is one edit (two for M16/M17) to a scratch copy. A mutant is rejected when verification
fails, or when `--no-cheating` reports a trust marker beyond the expected two. To rerun them all:
`python3 negative_controls.py` from `verus_fixed/`, with `verus` on `PATH` or `VERUS=/path/to/verus`.
M1–M20 are the first pass's (M16/M17 re-anchored, since the constants moved); M21–M28 are new.

| # | Injected bug | Verus error |
|---|---|---|
| M1 | `divmod100` shifts by 18 instead of 19 | arithmetic underflow |
| M2 | `DECIMAL_PAIRS` stores `"07"` as `"70"` | postcondition of the static |
| M3 | `M_HIGH` one too small | postcondition of `div_rem_1e16` |
| M4 | post-shift 50 instead of 51 | assertion in `div_rem_1e16` |
| M5 | `mulhi` drops the second carry `high2` | postcondition of `mulhi` |
| M6 | `mulhi` takes the high half of `m` with `>> 63` | precondition of `lemma_mulhi_algebra` |
| M7 | the two pairs of a 4-digit group written in swapped order | precondition of `lemma_wrote` |
| M8 | two-digit step only above 10 (10 would print as `":"`) | precondition of `lemma_and_15` |
| M9 | no digit for zero (drops `\|\| self == 0`) | postcondition of `fmt` |
| M10 | a 4-digit group moves `offset` by 3 | precondition of `write_unchecked` |
| M11 | `u128::fmt` reports its second block at `N - 15` | loop invariant on entry |
| M12 | `u128::fmt` loses its zero shortcut (zero prints `""`) | loop invariant on entry |
| M13 | `enc_16lsd` stops one 4-digit group early | precondition of `divmod100` |
| M14 | `unsigned_abs` off by one for negative values | precondition of `Unsigned::fmt` |
| M15 | `'-'` written over the first digit | precondition of `lemma_holds_prepend` |
| M16 | `u8::MAX_STR_LEN` is 2, compile-time check removed | postcondition of `lemma_max_str_len_u8` (and `fmt`'s precondition in `write`) |
| M17 | `i64::MAX_STR_LEN` is 19 (no room for the sign), compile-time check removed | postcondition of `lemma_max_str_len_i64` |
| M18 | spec: digits encoded from `b'1'` | postcondition (spec and code disagree) |
| M19 | `assume(false)` in `divmod100` | a third trust marker under `--no-cheating` |
| M20 | `divmod100` made `external_body` | a third trust marker under `--no-cheating` |
| M21 | unsigned `write` returns the string from `offset + 1` (drops the leading digit) | postcondition of `write` |
| M22 | signed `write` returns the string from 0 (the uninitialized prefix) | precondition of `slice_buffer_to_str` (`initialized_ascii_suffix`) |
| M23 | `format`'s length check uses `>=`: `unreachable_unchecked` reachable at full length | precondition of `unreachable_unchecked` |
| M24 | `usize::MAX_STR_LEN` taken from `u32` (10) | postcondition of `write` and of `lemma_max_str_len` |
| M25 | the trusted contract of `slice_buffer_to_str` shifted by one byte | postcondition of `write` |
| M26 | developer's spec: `decimal_digit(7)` is `'8'` | postcondition (code and developer's spec disagree) |
| M27 | developer's spec: `initialized_ascii_suffix` requires nothing | assertion in `lemma_slice_buffer_to_str_human` (the developer's postcondition no longer follows) |
| M28 | `usize::MAX_STR_LEN` taken from `u128` (39): too large | the assertion against upstream's definition |

M21–M23 also show what the first pass missed. Applied to the trusted shells of `../verus/itoa`, all
three verify there (`105 verified, 0 errors`, with `--no-cheating`).

## Proof engineering

- **Stability.** All 165 items verify with SMT seeds 0 to 39, 42 and 1234. Over seeds 0 to 9, the
  most expensive function is still `u128::fmt` (13.2M resource units median, 25.2M max, under its
  `rlimit(50)`); every other function stays at or below 11.5M (`u64`'s `fmt`). The new proofs
  (`write`, `format`, the `spec_equiv` lemmas) each take under 0.3M.
- **Opaque predicates.** `digits_inv`, `holds` and `unchanged_outside` are `#[verifier::opaque]` and
  revealed only inside lemmas; see the first pass for why.
- **Strings.** The `write` proofs never reason about UTF-8 directly: before calling
  `slice_buffer_to_str`, `lemma_str_of_dec_int` gives a quantified fact over every `&str` whose bytes
  are `dec_int(n)`, which the call's postcondition instantiates. The bodies keep upstream's shape.
- **Nonlinear arithmetic** is confined to small lemmas (`lemma_mulhi_algebra`,
  `lemma_div_1e16_multiplier`, the `pow10` lemmas).

### Verus findings

- **An associated constant used as an array length** inside `verus!`
  (`type Buffer = [MaybeUninit<u8>; Self::MAX_STR_LEN]`, or `[_; i128::MAX_STR_LEN]` once the
  `Integer` impls are verified) crashes Verus ("thir_body query … VerusErasureCtxt has not been
  initialized"). Plain constants avoid it (the developer's workaround).
- **A compile-time `assert!` that reads the associated constant of a verified impl**
  (`const _: () = assert!(N == <u64 as Integer>::MAX_STR_LEN)`) crashes Verus in the same way.
  So the `usize`/`isize` constants are checked by a Verus assertion instead.
- **An associated constant defined by projection from another impl**
  (`impl Integer for usize { const MAX_STR_LEN: usize = <u64 as Integer>::MAX_STR_LEN; }`)
  silently stops Verus from unfolding the open spec functions of the impls for `u64`, in every
  trait (`Unsigned::spec_val`, `Signed::spec_val`, `Sealed::spec_int`; likewise `isize` for `i64`).
  The `u64`/`i64` proofs of `fmt` and `write` then fail with "postcondition not satisfied" and no
  hint of the cause. A plain constant avoids it.
- **A verified trait cannot have an unverified supertrait**; an unverified *impl* of a verified
  trait is fine (first pass).
- **Exec statics cannot be read in proof code**, but their `ensures` is available in the exec
  functions that use them (first pass).
- **Byte literals** (`b'0'`) and `debug_assert!` are unsupported; `&mut slice[range]`,
  slice-to-array `try_into`, `Rev`, `MaybeUninit::write` and `get_unchecked(_mut)` have no vstd
  specification (first pass).
- **`--no-cheating` accepts `#[verifier::external]`** (and code outside `verus!`), so unverified
  code without a contract is invisible to it. The first pass used that to keep `--no-cheating`
  clean, at the price of leaving the public API without a contract. This folder makes the trusted
  code `external_body` instead, so that `--no-cheating` lists it and Verus checks its callers.

## Reproduce

From `itoa/`:

    verus --crate-type=lib src/lib.rs                     # 165 verified, 0 errors
    verus --crate-type=lib --no-cheating src/lib.rs       # lists the 2 trusted items
    cargo build && cargo test && cargo test --release
    cargo test --tests --no-default-features --release
    cargo build --tests --features no-panic --release
    cargo bench --no-run
    cargo clippy --tests --benches -- -Dclippy::all -Dclippy::pedantic

From `verus_fixed/`: `python3 negative_controls.py` (28/28 rejected) and
`python3 check_trusted.py` (0 unexpected changes).
