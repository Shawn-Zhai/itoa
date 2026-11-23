# Verifying `itoa` with Verus (2026-11-09; ported to Verus 0.2026.11.22 on 2026-11-23)

Crate: `itoa` 1.0.19, this fork's `master` @ 9339ca9. Verus 0.2026.11.22.1ce6a59 (the bare
`verus` binary and its bundled vstd); the normal build uses rustc 1.100.0. Every Verus run uses
`--no-cheating`. (Written for Verus 0.2026.05.03.8b81855 and rustc 1.95.0; see
[Port to Verus 0.2026.11.22](#port-to-verus-020261122) for what the port changed and what was
rerun.) Annotated crate: [`itoa/`](itoa/). Diff against upstream:
[`upstream.diff`](upstream.diff). Specifications and proofs were written by Claude (Opus 5.5) in
Claude Code on 2026-11-09, from the crate's documentation, its tests and the code. No
human-written spec existed.

## Headline

| | |
|---|---|
| Verus `--no-cheating` | **105 verified, 0 errors**, about 4 s wall clock (3.3 s SMT) |
| `assume`, `admit`, `external_body`, `assume_specification`, axioms, `uninterp` in the crate | **none** (`--no-cheating` rejects them) |
| Verified | all digit generation: `Unsigned::fmt` for `u8`, `u16`, `u32`, `u64`, `u128`, `enc_16lsd`, `div_rem_1e16` (including its Granlund–Montgomery constant), `mulhi`, `divmod100`, the `DECIMAL_PAIRS` table; the signed formatting (`Signed::fmt`, 5 types); `Buffer::new`, `Default`, `Clone` |
| Trusted, not verified | [`trusted.rs`](itoa/src/trusted.rs): `Buffer::format` and `slice_buffer_to_str` (raw-pointer reinterpretations), and the `Integer`/`Sealed` impls whose `write` calls `slice_buffer_to_str`. 15 items, 14 of them verbatim upstream ([`check_trusted.py`](check_trusted.py)) |
| Normal `cargo build` of the annotated crate | passes, 0 warnings; also `--features no-panic --release` |
| Upstream tests on the annotated crate | 11/11 integration, 2/2 doc (debug and release) |
| Differential test | 8,134,557 values: annotated == upstream == `std`, every integer type, built with `no-panic` |
| Negative controls | 20/20 injected bugs rejected ([`negative_controls.py`](negative_controls.py)) |
| Proof stability | same result with SMT seeds 0 to 39, 42 and 1234 |
| Erased code | per function, the code a normal build compiles is identical to upstream's except in the changes listed below (checked on the macro-expanded output) |
| Performance (upstream's criterion benchmark) | equal or faster in all 7 cases with rustc 1.100.0 (with 1.95.0: 6 of 7; `u128[0]` 1.19 ns against 1.04 ns) |

## Port to Verus 0.2026.11.22

On 2026-11-23 the crate was moved from Verus 0.2026.05.03.8b81855 and rustc 1.95.0 to Verus
0.2026.11.22.1ce6a59 and rustc 1.100.0. No specification, contract, proof or trusted item changed.

One thing broke. Verus 0.2026.11.22 rejects `i128::MAX_STR_LEN` as an array length in verified code
(`Buffer`'s field and `Buffer::new`) with "`lib::trusted::impl&%19::MAX_STR_LEN` is not supported",
because the impl that defines the constant is in `trusted.rs`, which Verus skips. 0.2026.05.03
accepted it. The fix names the field's type through a type alias declared outside `verus!` and lets
rustc infer the repeat length in `Buffer::new` (see "Executable code" below). Verus then knows the
length is 40. The other changes are the build pins (`vstd`, `rust-version`, `rust-toolchain.toml`)
and the regenerated `upstream.diff`.

Rerun with the new versions:

| Check | Result |
|---|---|
| `verus --crate-type=lib --no-cheating src/lib.rs` | 105 verified, 0 errors, as before |
| SMT seeds 0 to 39, 42 and 1234 | all verify; the proofs are cheaper (see "Proof engineering") |
| `negative_controls.py` | 20/20 rejected |
| `check_trusted.py` | 15 items, 0 unexpected changes |
| Upstream CI steps (see "Validation beyond the proof") | pass, 0 warnings |
| Differential test | 8,134,557 values: annotated == upstream == `std`, and == `../verus_fixed` |
| Machine code | `Buffer::format` for the 12 types, the out-of-line `fmt` instances, `enc_16lsd` and the `DECIMAL_PAIRS` bytes are identical to `../verus_fixed`'s |
| Criterion benchmark | equal or faster than upstream in all 7 cases (see "Observable differences") |

The findings about Verus below were rechecked too; several no longer hold.

## The specification

All definitions are in [`itoa/src/spec.rs`](itoa/src/spec.rs).

- `dec(n: nat) -> Seq<u8>`: the decimal representation of `n` in ASCII, without leading zeros
  (`"0"` for zero). It is defined through `dec_pad(n, k)`, the `k` low digits of `n` zero-padded,
  and `num_digits(n)`. `lemma_dec_value` shows that it is the usual notation: it consists of the
  bytes `b'0'..=b'9'`, its value (Horner's rule) is `n`, and it has no leading zero unless it is
  `"0"`. These three facts determine it.
- `dec_int(n: int)`: `'-'` followed by `dec(-n)` for negative `n`, otherwise `dec(n)`.
- `holds(buf, start, bytes)`: the `MaybeUninit<u8>` buffer `buf` holds the initialized bytes
  `bytes` at `start..start + bytes.len()` (vstd's `mem_contents() == MemContents::Init(b)`).
- `unchanged_outside(new, old, lo, hi)`: `new` agrees with `old` outside `lo..hi`.

### Contracts

| Item | Status | Contract |
|---|---|---|
| `Unsigned::fmt::<N>(self, buf: &mut [MaybeUninit<u8>; N])` (`u8`..`u128`) | verified | requires `dec(self).len() <= N`. Returns `offset` with `offset + dec(self).len() == N`; `buf[offset..N]` holds `dec(self)`; nothing else in `buf` changes |
| `Signed::fmt::<N>` (`i8`..`i128`) | verified | the same with `dec_int(self)` |
| `enc_16lsd(buf, offset, n)` | verified | requires `n < 10^16`, `offset + 16 <= buf.len()`. `buf[offset..offset + 16]` holds `dec_pad(n, 16)`; nothing else changes |
| `div_rem_1e16(n)` | verified | returns `(n / 10^16, n % 10^16)` for every `u128` |
| `mulhi(x, y)` | verified | returns `x * y / 2^128` for every pair of `u128` |
| `divmod100(v)` | verified | requires `v < 10_000` (upstream's `debug_assert!`). Returns `(v / 100, v % 100)` |
| `DECIMAL_PAIRS` | verified | the table is `decimal_pairs()`: entries `2p` and `2p + 1` are the two digits of `p` |
| `Buffer::new`, `Default`, `Clone` | verified | no contract beyond safety (they only create an uninitialized buffer) |
| `MAX_STR_LEN` (all 10 fixed-width types) | verified through the buffer types | the `lemma_max_str_len_*` lemmas show that `<T as Sealed>::Buffer`, an array of `T::MAX_STR_LEN` bytes, has exactly the length of the longest decimal representation of a `T` (`T::MAX`, or `T::MIN` with its sign), and that every value fits |
| `Buffer::format`, `Sealed::write`, `slice_buffer_to_str` | trusted | see the trusted base |

The precondition of `fmt` (`dec(self).len() <= N`) and the `lemma_max_str_len_*` lemmas together
discharge the call made by each trusted `write`, which passes `buf: &mut Self::Buffer`. Verus
checks the `fmt` bodies against the actual buffer lengths, which rustc computes from upstream's
`ilog10` formula. Making `MAX_STR_LEN` one too small for any type fails verification
(mutants M16 and M17).

### What the proofs establish about upstream's reasoning

- **Absence of panics and of out-of-bounds accesses** in all verified code. This covers every
  index that upstream accessed with `get_unchecked(_mut)`, the `expect` calls in the `u8`..`u64`
  loop (never reached for `u8`, always `Ok` otherwise), and all arithmetic.
- **Division by multiplication.** `divmod100`'s `(v * 5243) >> 19` is exact for `v < 10^4`.
  `div_rem_1e16`'s `mulhi(n, M_HIGH) >> 51` is exact for every `u128`: with `q = n / 10^16`,
  `n * M_HIGH = q * 2^179 + (q * e + r * M_HIGH)` where `e = M_HIGH * 10^16 - 2^179 = 630438908198912`,
  and the second term stays below `2^179` because `(q + 1) * e < M_HIGH`
  (`lemma_div_1e16_multiplier`). `mulhi` is proved against the exact 256-bit product.
- **The room for the sign.** `i64::MAX_STR_LEN` equals `u64::MAX_STR_LEN` (both 20), so upstream
  formats `|x|` into the whole `i64` buffer and relies on `|i64::MIN| = 2^63` having only 19 digits
  for the `'-'`. `Signed::fmt` proves this, and the analogous fact for the other types.

No bug was found in the crate.

## Trusted base

Under `--no-cheating` the crate cannot contain `external_body`, `assume_specification`, `uninterp`
or axioms, so the only way to mark code as trusted is to leave it unverified. All such code is in
[`itoa/src/trusted.rs`](itoa/src/trusted.rs). `lib.rs` declares the module with
`#[cfg_attr(verus_keep_ghost, verifier::external)]`, so Verus skips it, and normal builds compile
it like any other module. The items are upstream's code moved there unchanged, doc comments
included, except the signed `write` (T2). `python3 check_trusted.py` (from `verus/`) checks each
item against upstream `src/lib.rs` and prints the diff of the expected change.

| id | Items | Upstream lines | Why it cannot be verified |
|---|---|---|---|
| T1 | `Buffer::format` | 11 | reinterprets the `[MaybeUninit<u8>; 40]` buffer as `I::Buffer` through a raw-pointer cast (`as_mut_ptr().cast::<I::Buffer>()`, `&mut *buf_ptr`). vstd's raw-pointer model needs a `PointsTo` permission, and a `&mut` reference does not provide one. Also contains upstream's `unreachable_unchecked` length hint |
| T2 | `impl_Integer!`, `impl_Integer_size!` and their invocations: `Integer` (`MAX_STR_LEN`) and `Sealed` (`Buffer`, `write`) for the 12 integer types | 82 | `write` returns a `&str` built by T3. The impls cannot be split, since Verus verifies a trait impl all or nothing. `MAX_STR_LEN` uses `ilog10`, which vstd does not specify; its values are checked through the buffer types (see above) |
| T3 | `slice_buffer_to_str` | 15 | reinterprets `&[MaybeUninit<u8>]` as `&[u8]` through a raw-pointer cast, then calls `str::from_utf8_unchecked` |

**Obligations on the trusted code.** These hold by inspection, not by proof:

- T1: `I::Buffer` is `[MaybeUninit<u8>; I::MAX_STR_LEN]` (or the buffer of the primitive that
  `usize`/`isize` convert to), and `I::MAX_STR_LEN <= 40 = i128::MAX_STR_LEN`, so the cast stays
  inside `self.bytes`, and `MaybeUninit<u8>` has no alignment or validity requirement. The hint
  `string.len() <= I::MAX_STR_LEN` holds because `write` returns `buf[offset..]` of a `buf` of
  that length.
- T2: each `write` passes `buf: &mut Self::Buffer` (rustc checks the type) to the verified
  `Unsigned::fmt` or `Signed::fmt`. Their precondition holds for every value by the verified
  `lemma_max_str_len_*` lemmas. Their postcondition says that `offset <= buf.len()` and that
  `buf[offset..]` holds the initialized bytes `dec(self)` or `dec_int(self)`, which are ASCII: this
  is exactly T3's safety condition. `usize`/`isize` cast to the fixed-width type of the same size
  and call its `write`.
- T3: called only from T2, with that guarantee.

**Trusted outside the crate:**

- vstd's specifications of the std items the verified code uses: `MaybeUninit::{new, uninit}` and
  `mem_contents`, array and slice indexing and index assignment, slice `len`,
  `hint::unreachable_unchecked` (`requires false`), `mem::size_of` with `layout_of_primitives`,
  `TryInto<u16/u32/u64>` for `i32`, `Result::expect`, and `From<u64> for u128`.
- Verus, Z3 and rustc; and the `verus!` macro, trusted to erase only ghost code, as Verus itself
  trusts it.

## Changes to the crate (audit of `upstream.diff`)

- `lib.rs`: 179 lines removed, 665 added (the `-` and `+` lines of `upstream.diff`; 2 and 8 of
  them are from the port). Most removed lines are the items that moved unchanged to `trusted.rs`;
  most additions are contracts, proof blocks, lemmas and the new `Signed` trait.
- `u128_ext.rs`: 1 line changed (`mulhi`'s signature names its result, for the `ensures`), 142
  ghost lines added. Its executable code is unchanged.
- `Cargo.toml`: 2 lines removed, 10 added.
- New files: `spec.rs` (851 lines, ghost), `std_ext.rs` (55), `trusted.rs` (143), `rust-toolchain.toml`.
- `tests/`, `benches/` and the licenses are unchanged.

### Executable code

Every change computes the same result, writes the same bytes at the same positions and returns the
same offset as upstream. The upstream test suite passes unchanged, and the differential test below
compares the annotated crate with upstream on 8.1 million values.

| Change | Where | Reason |
|---|---|---|
| `fn fmt(self, buf: &mut Self::Buffer)` → `fn fmt<const N: usize>(self, buf: &mut [MaybeUninit<u8>; N])` | `trait Unsigned` and its 5 impls | for signed types upstream formats into a subslice of the longer signed buffer, converted with `(&mut buf[offset..]).try_into().unwrap()`. Verus supports neither mutable range indexing nor slice-to-array `try_into`. `fmt` writes right-aligned from `buf.len()` down, so on the whole signed buffer the digits land in the same places |
| the signed formatting moved out of `Sealed::write` into the new verified `trait Signed`, whose `fmt` calls `Unsigned::fmt` on the whole buffer, then writes `'-'` | `impl_Signed!` (new), the signed `write` in `trusted.rs` | `write` builds the `&str` and stays trusted. The returned offset equals upstream's `(Self::MAX_STR_LEN - $Unsigned::MAX_STR_LEN) + offset_in_subslice` |
| `self.unsigned_abs()` → `if self < 0 { (-(self + 1)) as $Unsigned + 1 } else { self as $Unsigned }` | `Signed::fmt` | vstd does not specify `unsigned_abs`. The expression uses only in-range casts. LLVM proves it identical to `unsigned_abs` and emits a symbol alias (checked for `i8`, `i64`, `i128`) |
| `buf.get_unchecked_mut(i).write(v)` → `write_unchecked(buf, i, v)`; `*DECIMAL_PAIRS.0.get_unchecked(j)` → `*get_unchecked(&DECIMAL_PAIRS.0, j)` | all digit writes in `fmt` | vstd does not specify `get_unchecked(_mut)`. The verified stand-ins in `std_ext.rs` index with a bounds check behind a branch to `unreachable_unchecked` that Verus proves dead, so the optimizer drops the check. The `u64` digit loop compiles to the same instructions as upstream's, and the `no-panic` build links |
| `buf[i].write(v)` → `buf[i] = MaybeUninit::new(v)` | `enc_16lsd`, the zero case of `u128::fmt` | `MaybeUninit::write` is unspecified; it is `*self = MaybeUninit::new(val)` plus a returned reference that itoa discards. Checked indexing as upstream |
| `b'0'`, `b'-'` → `48`, `45`; the byte-string table `*b"0001…99"` → a numeric array literal, with each row's string in a comment | `fmt`, `Signed::fmt`, `DECIMAL_PAIRS` | Verus does not support byte literals. Same bytes |
| `static DECIMAL_PAIRS` → `exec static DECIMAL_PAIRS … ensures …` | `DECIMAL_PAIRS` | Verus statics carry their property in `ensures`. Erases to the same `static` |
| `debug_assert!(value < 10_000)` removed | `divmod100` | panic macros are unsupported. It became `requires value < 10_000`, proved at every call site, so a debug build loses only a check that cannot fail |
| `u128::MAX_STR_LEN` → `N` (5 places), comments `buf[23..39]` → `buf[N-16..N]` | `u128::fmt` | the buffer length, now generic: 39 for `u128` and 40 for `i128`. Verus also cannot read a constant whose impl is external |
| `fn enc_16lsd<const OFFSET: usize>(buf, n)` → `fn enc_16lsd(buf, offset: usize, n)`; `for quad_index in (1..4).rev()` → `let mut quad_index = 4; while quad_index > 1 { quad_index -= 1; … }` | `enc_16lsd` | `OFFSET` would have to be `N - 16`, a generic constant expression, which stable Rust rejects. Verus does not support `Rev`; the loop visits 3, 2, 1 as before |
| `bytes: [MaybeUninit<u8>; i128::MAX_STR_LEN]` → `bytes: BufferBytes`, with `type BufferBytes = [MaybeUninit<u8>; i128::MAX_STR_LEN];` declared outside `verus!`; `[MaybeUninit::<u8>::uninit(); i128::MAX_STR_LEN]` → `[MaybeUninit::<u8>::uninit(); _]` | `Buffer`, `Buffer::new` (from the port to Verus 0.2026.11.22) | Verus 0.2026.11.22 rejects `i128::MAX_STR_LEN` as an array length in verified code, because the impl that defines it is in `trusted.rs`, which Verus skips. Through a type alias it accepts the constant, with its value. The type is unchanged: rustc infers `_` from the field and rejects any other length |
| `Buffer`, `Default`, `Copy`, `Clone`, `Buffer::new` inside `verus!` | `lib.rs` | unchanged text, except the array lengths above |

### Build-only changes

- `Cargo.toml` gains a `vstd` dependency (`default-features = false`, so still `no_std`), which
  provides the `verus!` macro. No vstd function is called at run time.
- `rust-version` goes from 1.68 to 1.100, and `rust-toolchain.toml` pins 1.100.0, the toolchain
  of Verus 0.2026.11.22. `vstd` is `=0.0.0-2026-11-22-0344`, the crates.io release of the same day
  (built from Verus commit 8cf39ad; the binary is 1ce6a59). (Before the port: 1.95, 1.95.0 and
  `vstd` `=0.0.0-2026-05-06-1803`.)
- `publish = false`; `unexpected_cfgs` allows `verus_keep_ghost`.
- The ghost-only `use crate::spec::*` is `#[cfg(verus_keep_ghost)]`.

### Ghost-only additions

- Contracts on 9 executable items (`get_unchecked`, `write_unchecked`, `DECIMAL_PAIRS`, `divmod100`,
  `Unsigned::fmt`, `enc_16lsd`, `div_rem_1e16`, `Signed::fmt`, `mulhi`), invariants on 3 loops and
  36 `proof` blocks in executable code.
- 51 lemma definitions (two of them in a macro instantiated for each of the 5 type pairs, so 59
  lemmas in all), 6 bit-vector and 5 nonlinear-arithmetic assertions, and 4 `compute_only`
  assertions (in the `MAX_STR_LEN` lemmas).
- 12 spec functions in `spec.rs`, 5 inlined constants (`b64`, `b128`, `d16`, `m_high`, `b179`) and
  the `spec_val` functions of the two traits.
- One `#[verifier::rlimit(50)]`, on `u128::fmt` (see "Proof engineering").

### Observable differences

- **Performance and code layout.** `Unsigned::fmt` is generic now, so it is instantiated, and
  usually inlined, in the calling crate. Upstream compiles it once, out of line, in itoa. The
  algorithm's machine code is the same. In upstream's criterion benchmark (same machine, release;
  median times, both crates built with the same rustc):

  | case | upstream, rustc 1.95.0 | annotated, rustc 1.95.0 | upstream, rustc 1.100.0 | annotated, rustc 1.100.0 |
  |---|---|---|---|---|
  | `u64[0]` | 1.60 ns | 0.59 ns | 1.74 ns | 0.59 ns |
  | `u64[half]` | 2.29 ns | 2.08 ns | 2.38 ns | 2.22 ns |
  | `u64[max]` | 3.83 ns | 3.81 ns | 4.23 ns | 4.17 ns |
  | `i16[0]` | 1.39 ns | 0.59 ns | 1.52 ns | 0.65 ns |
  | `i16[min]` | 1.37 ns | 1.16 ns | 1.55 ns | 1.31 ns |
  | `u128[0]` | 1.04 ns | 1.19 ns | 0.93 ns | 0.56 ns |
  | `u128[max]` | 10.58 ns | 10.44 ns | 11.45 ns | 11.11 ns |

  The rustc 1.100.0 columns were measured after the port, on 2026-11-23. A tight loop over random
  values of every width, written for this check (rustc 1.95.0; not rerun), gave mixed results
  (`u32` 24% faster, `u64` 31% slower). Its machine code for the digit loops is identical, so
  these are inlining and alignment effects of the surrounding loop.
- **Code size.** One `fmt` instance per pair of type and buffer length, so up to two per unsigned
  type (its own buffer and its signed counterpart's), where upstream has one.
- **Debug builds.** The removed `debug_assert!` and the overflow checks in the `unsigned_abs`
  expression cannot fail, by the proof.
- **Dependencies and MSRV**, as listed above.

## Validation beyond the proof

- **Upstream CI steps** on the annotated crate: `cargo build`, `cargo test`, `cargo test --release`,
  `cargo test --tests --no-default-features --release`, `cargo build --tests --features no-panic
  --release`, `cargo bench --no-run`. All pass. (Miri needs a nightly toolchain, which is not
  installed here.)
- **Differential test** (a scratch crate depending on both the annotated crate and a renamed copy
  of upstream, both with `no-panic`): every `u8`, `i8`, `u16`, `i16`; for the wider types, all
  powers of ten and two and their neighbours, both signs, `MIN` and `MAX`; and 1,000,000 random
  values of random bit length for each of `u32`, `i32`, `u64`, `i64`, `u128`, `i128`, `usize`,
  `isize`. 8,136,116 values, all formatted identically by the annotated crate, upstream and
  `to_string`. `MAX_STR_LEN` agrees for all 12 types. Rerun after the port (rustc 1.100.0, a
  new random sample, `../verus_fixed` added): 8,134,557 values, all identical.
- **`no-panic`.** The differential test formats `black_box`ed values of all 12 types with the
  feature enabled in release mode and links, so no panic path survives in the verified code. (The
  last upstream commit was about exactly this.)

## Negative controls (all rejected)

Each mutant is one edit to a scratch copy, checked with `--no-cheating`. To rerun them all:
`python3 negative_controls.py` from `verus/`, with `verus` on `PATH` or `VERUS=/path/to/verus`.

| # | Injected bug | Verus error |
|---|---|---|
| M1 | `divmod100` shifts by 18 instead of 19 | arithmetic underflow: for 9999 the quotient would be 100 |
| M2 | `DECIMAL_PAIRS` stores `"07"` as `"70"` | postcondition of the static |
| M3 | `M_HIGH` one too small (floor instead of ceiling of 2^179 / 10^16) | postcondition of `div_rem_1e16` |
| M4 | post-shift 50 instead of 51 | assertion in `div_rem_1e16` |
| M5 | `mulhi` drops the second carry `high2` | postcondition of `mulhi` |
| M6 | `mulhi` takes the high half of `m` with `>> 63` | precondition of `lemma_mulhi_algebra` (`high1 == (xl * yh + carry) / 2^64`) |
| M7 | the two pairs of a 4-digit group written in swapped order | precondition of `lemma_wrote`: the bytes written are not the next four digits |
| M8 | two-digit step only above 10 (10 would print as `":"`) | precondition of `lemma_and_15` (`x < 10`): 10 reaches the last-digit step |
| M9 | no digit for zero (drops `\|\| self == 0`) | postcondition of `fmt` |
| M10 | a 4-digit group moves `offset` by 3 | precondition of `write_unchecked` (`index < N`): the group's last byte can land past the buffer |
| M11 | `u128::fmt` reports its second block at `N - 15` | loop invariant on entry |
| M12 | `u128::fmt` loses its zero shortcut (zero prints `""`) | loop invariant on entry |
| M13 | `enc_16lsd` stops one 4-digit group early | precondition of `divmod100` (`value < 10_000`) |
| M14 | `unsigned_abs` off by one for negative values | precondition of `Unsigned::fmt` and underflow of `offset -= 1`: the value passed is not `\|self\|` |
| M15 | `'-'` written over the first digit | precondition of `lemma_holds_prepend`: the sign overlaps the digits |
| M16 | trusted: unsigned `MAX_STR_LEN` is `ilog10() + 0` | assertion in `lemma_max_str_len_*` (the buffer type is too short) |
| M17 | trusted: signed `MAX_STR_LEN` is `ilog10() + 1` (no room for the sign) | postcondition of `lemma_max_str_len_*` |
| M18 | spec: digits encoded from `b'1'` | postcondition (spec and code disagree) |
| M19 | `assume(false)` in `divmod100` | `` `assume`/`admit` not allowed with `--no-cheating` `` |
| M20 | `divmod100` made `external_body` | `` `external_body`/`assume_specification` not allowed with `--no-cheating` `` |

## Proof engineering

- **Stability.** All 105 items verify with SMT seeds 0 to 39, 42 and 1234. The most expensive
  function, `u128::fmt`, takes 9.6M to 33.8M resource units (median 15.2M), which reaches the
  default limit (about 30M) for some seeds, so it carries `#[verifier::rlimit(50)]`, five times the
  default. No other function exceeds 11.3M (the `u64` `fmt`) on any seed, well within the
  default limit. With Verus 0.2026.11.22 all 105 items still verify with the same 42 seeds, and
  the proofs are cheaper: `u128::fmt` takes 4.0M to 9.7M (median 5.3M), so the `rlimit(50)` is no
  longer needed (it was kept, so the proof text is unchanged), and no other function exceeds 8.5M
  (`lemma_mulhi_algebra`).
- **Opaque predicates.** `digits_inv`, `holds` and `unchanged_outside` are `#[verifier::opaque]` and
  revealed only inside lemmas. A first version, with transparent predicates and the effect of each
  write proved by revealing `holds`/`unchanged_outside` in the function bodies, failed for some
  seeds. Each write's effect is now stated through `lemma_wrote`, whose preconditions are cheap to
  prove at the call site. Bisecting `u128::fmt` showed that its cost comes from checking the two
  steps after the loop under the three paths that lead into the loop. Each part alone costs 3M to
  5M units.
- **Nonlinear arithmetic** is confined to small lemmas (`lemma_mulhi_algebra`,
  `lemma_div_1e16_multiplier`, the `pow10` lemmas). Large constants are inlined spec functions
  (`b64`, `b128`, `m_high`, `d16`), so Z3 sees multiplications by literals.

### Verus findings from this pass

Found with Verus 0.2026.05.03. Each was rechecked with 0.2026.11.22 on a minimal example; the
result follows the arrow. The port kept the code's workarounds even where they are no longer needed.

- **An associated constant used as an array length** inside `verus!`
  (`type Buffer = [MaybeUninit<u8>; Self::MAX_STR_LEN]`) crashes Verus ("thir_body query …
  VerusErasureCtxt has not been initialized"). It works when the `impl Integer` defining the
  constant is outside `verus!`. Verified code can then use the constant in types (array lengths,
  const generic arguments), which rustc evaluates, but not as a value. → **Reversed.** The
  constant of a verified impl works, and an array length in verified code that names the constant
  of an impl Verus skips is rejected ("`…::MAX_STR_LEN` is not supported"), unless it goes through
  a type alias. This is the one change the port needed.
- **A verified trait cannot have an unverified supertrait** (`compute_dyn_compatibility: missing
  trait`); an unverified *impl* of a verified trait is fine. → Still crashes Verus.
- **Exec statics cannot be read in proof code**, but their `ensures` is available in the exec
  functions that use them. Stating the table's property as an equation with a spec sequence made
  it usable in proofs. → Unchanged.
- **Out-of-range `as` casts** have no defined value unless proved with a bit-vector lemma;
  `#[verifier::truncate]` only silences the warning. → Unchanged.
- **Byte literals** (`b'0'`) and `debug_assert!` are unsupported; `&mut slice[range]`, slice-to-array
  `try_into`, `Rev`, `MaybeUninit::write` and `get_unchecked(_mut)` have no vstd specification.
  → Byte literals, `debug_assert!` (its condition must be proved), `&mut slice[range]`, `Rev`,
  `MaybeUninit::write` and `get_unchecked(_mut)` are supported now. Slice-to-array `try_into`,
  `unsigned_abs` and `ilog10` are still unsupported.
- **`--no-cheating` accepts `#[verifier::external]`** (and code outside `verus!`), so unverified
  code must be reported separately; here it is confined to `trusted.rs`. → Unchanged. The message
  for a rejected `assume` or `external_body` now puts `` `--no-cheating` `` in backticks.
