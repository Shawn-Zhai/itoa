# Review: Claude's verified spec against the developer's spec (2026-11-13)

**Inputs.** "Claude's spec" is the specifications and proofs in [`../verus/itoa/src/`](../verus/itoa/src/)
(first pass, 2026-11-09). "The developer's spec" is
[`../verus_human_written_spec/itoa/src/`](../verus_human_written_spec/itoa/src/), the compilable version
(commit 5ab36d6). The developer's spec was the reference, and both were read as possibly wrong. Where possible,
disagreements were settled by running Verus rather than by reading. This folder is a copy of `verus/` with the amendments
applied. [`amendments.diff`](amendments.diff) shows every hand edit against `verus/`. `verus/` and
`verus_human_written_spec/` are unchanged.

Tooling: Verus 0.2026.05.03.8b81855 (bare binary, bundled vstd), as in Claude's first pass. The normal build
uses rustc 1.95.0.

## Outcome

**Claude's verified contracts contain no false statement.** Verus proves them, and they agree with the
developer's contracts on every function that both specify. On the internal functions they are as strong or
stronger: `fmt` and `enc_16lsd` describe the bytes written, where the developer's contracts give only lengths.

**But Claude's work left the crate's public API unspecified.** `Buffer::format`, the 12 `write` methods and
`slice_buffer_to_str` were trusted code with no contract at all. The developer's spec specifies all of them. A
verified client could not even call `format`:

```
error: cannot use function `lib::Buffer::format` which is ignored because it is either declared outside the
verus! macro or it is marked as `external`.
```

Bugs in that code also went unnoticed. Mutants M21–M23 below drop a digit, read uninitialized memory and
reach an `unreachable_unchecked`, and Claude's crate still verifies with them: 105 verified, 0 errors, even
under `--no-cheating`.

| # | Problem in Claude's spec | Developer's spec | Amendment |
|---|---|---|---|
| A1 | `format`, `write` (12 impls) and `slice_buffer_to_str` have no contract; 15 trusted items | contracts for all three | `format` and all `write`s are verified. Their contracts are exact and include the developer's clauses. Trusted code is down to two raw-pointer reinterpretations of upstream code, now with explicit contracts |
| A2 | `Buffer::new`, `Default`, `Clone` have no postcondition | `result.len() == i128::MAX_STR_LEN` | added |
| A3 | none: Claude's contracts of the internal functions are as strong or stronger | contracts for `fmt`, `enc_16lsd`, `divmod100`, `div_rem_1e16`, `mulhi` | the developer's clauses are stated next to Claude's, which checks that Claude's imply them |

Separately, Claude's report said that upstream's CI steps all pass, but its crate failed upstream's clippy
step (C4). Fixed with a build-only lint configuration.

**The developer's spec has mistakes too** (H1–H4 below; the folder is unchanged). The most serious is H1:
`enc_16lsd` lacks the precondition `n < 10^16`. Without it, the contract promises safe behaviour on inputs
where the code reads past the end of its lookup table. Also, `format`'s contract does not determine the output
(H4), and no caller can establish the precondition of `slice_buffer_to_str` (H2).

**No executable behaviour changed.** For all 12 integer types, `Buffer::format` compiles to the same machine
code as in Claude's crate. 8,144,968 values format identically in the fixed crate, upstream and `std`.

## Verdicts by function

"Both" in the last column means that the fixed crate states the developer's clauses and Claude's on the
function, and Verus proves both.

| Function | Developer's contract | Claude's (first pass) | Verdict | Fixed crate |
|---|---|---|---|---|
| `Buffer::format` | `is_decimal_text(result@)`, `1 <= result@.len() <= I::MAX_STR_LEN` | none (trusted; not callable from verified code) | **Claude missing** | verified: `result@ == decimal_signed(i.spec_int())` plus the developer's three clauses |
| `Sealed::write` (trait) | decimal text, `1 <= len <= 40` | none | **Claude missing** | verified: exact text plus the developer's clauses |
| `write`, `u8`..`u128` | `result@ =~= decimal_unsigned(self)`, `len <= MAX_STR_LEN` | none | **Claude missing** | verified, developer's contract |
| `write`, `i8`..`i128` | `result@ =~= decimal_signed(self)`, `len <= MAX_STR_LEN` | none | **Claude missing** | verified, developer's contract |
| `write`, `usize`/`isize` | `result@ =~= decimal_signed(self)`, `len <= MAX_STR_LEN` | none | **Claude missing** | verified, developer's contract |
| `slice_buffer_to_str` | requires `offset <= len`, `initialized_ascii_suffix` (uninterpreted, H2); ensures length and ASCII | none | **Claude missing**; developer's precondition unusable | trusted contract: the developer's precondition (now defined), and the result's bytes are the buffer's. The developer's postcondition is proved from it (`lemma_slice_buffer_to_str_human`) |
| `Buffer::new`, `Default`, `Clone` | `result.len() == i128::MAX_STR_LEN` | none | Claude weaker (A2) | developer's contract |
| `Unsigned::fmt` (5 impls) | `offset < MAX_STR_LEN`, `MAX_STR_LEN - offset == decimal_unsigned(self).len()` | offset, the bytes written, rest of `buf` unchanged | Claude stronger | both (developer's clauses generalized to any buffer length `N`) |
| `enc_16lsd` | requires `OFFSET + 16 <= len`; ensures length unchanged | also requires `n < 10^16`; ensures the 16 digits written, rest unchanged | Claude stronger; **developer's precondition insufficient (H1)** | both |
| `divmod100` | quotient, remainder, `r.1 < 100`, `r.0 * 100 + r.1 == value` | quotient, remainder | equivalent | both |
| `div_rem_1e16` | quotient, remainder, bound, recombination | quotient, remainder | equivalent | both |
| `mulhi` | `x * y / 2^128` | `x * y / 2^128` | equivalent | both |
| `DECIMAL_PAIRS` | none | table equals `decimal_pairs()` | Claude only | unchanged |
| `MAX_STR_LEN` | plain constants, compile-time checks against upstream's `ilog10` formula | upstream's formula (trusted), checked through the buffer types | both right | the developer's constants. Claude's lemmas prove them tight; a Verus assertion checks the `usize`/`isize` ones |
| `Signed::fmt` | — (inline in `write`) | verified | Claude only | unchanged |

Text definitions: Claude's `dec`/`dec_int` (bytes) and the developer's `decimal_unsigned`/`decimal_signed`
(chars) are the same text (`spec_equiv.rs`: `ascii_chars(dec(n)) == decimal_unsigned(n)`,
`ascii_chars(dec_int(n)) == decimal_signed(n)`). `decimal_signed(n)` always satisfies the developer's
`is_decimal_text`.

## Findings in Claude's work

### C1. The public API had no specification (fixed: A1)

Claude's `VERIFICATION.md` lists `Buffer::format`, the `Integer`/`Sealed` impls and `slice_buffer_to_str` as
trusted, with obligations that "hold by inspection, not by proof". `Buffer::format` is the crate's main
function: apart from `Buffer::new`, it is the only one a user calls. The cause was the decision to run every check with `--no-cheating`.
That flag rejects `external_body`, so the trusted code went outside `verus!`, where it can have no contract.
Its call into the verified `fmt` was not checked either. Claude also found that an associated constant used as
an array length crashes Verus, so the `Integer`/`Sealed` impls stayed outside `verus!` too. The developer's spec
shows a workaround: plain constants for the lengths, checked against upstream's formula at compile time.

Consequences, each reproduced on Claude's crate:

- A verified client cannot call `format` (error above).
- Bugs in the trusted shells verify. Mutants M21–M23 (an unsigned `write` that drops the leading digit, a signed
  `write` that returns the uninitialized prefix, a reachable `unreachable_unchecked` in `format`) give `105
  verified, 0 errors` with `--no-cheating`. The fixed crate rejects all three.
- Nothing ties the length check in `format` to the proof: `if string.len() > I::MAX_STR_LEN {
  unreachable_unchecked() }` is undefined behaviour if reached, and its safety rested on inspection.

**Fix.**

- The `Integer` and `Sealed` impls (`impl_Integer!`, `impl_Integer_size!`) are back in `lib.rs`, inside `verus!`.
  The lengths are the developer's plain constants (`private::U8_MAX_STR_LEN`, ...). The compile-time
  `assert!`s in the developer's macro keep checking them against upstream's `MAX.ilog10() + 1` (`+ 2` for
  signed types). For `usize`/`isize`, a Verus assertion checks the constant against upstream's
  `<$primitive as Integer>::MAX_STR_LEN`.
- All 12 `write`s are verified, with upstream's bodies (checked by `check_trusted.py`; the signed one calls
  Claude's verified `Signed::fmt`, as in the first pass).
- `format` is verified. Only upstream's cast `self.bytes.as_mut_ptr().cast::<I::Buffer>()` / `&mut *buf_ptr`
  moved into a trusted function `buffer_of`. Verus now proves the `unreachable_unchecked` dead.
- `slice_buffer_to_str` is `external_body` with a contract: the developer's precondition, with
  `initialized_ascii_suffix` defined (H2), and `result.spec_bytes() == suffix_bytes(buf@, offset)`. That is
  vstd's own specification of the `str::from_utf8_unchecked` call that ends the body.
- `Sealed` gets `spec fn spec_int(self) -> int` (the value). `Integer` gets `proof fn lemma_max_str_len`:
  every value fits in `MAX_STR_LEN` bytes, and `MAX_STR_LEN <= 40`. These two make a generic contract for
  `format` possible. Both are ghost items, erased from normal builds, so the public API is unchanged.

**Trust, before and after.** Claude's crate trusted 15 items, 108 upstream lines, none with a contract. The
fixed crate trusts 2 functions: 4 statements of upstream code (the cast in `buffer_of`, the body of
`slice_buffer_to_str`), each with an explicit contract that Verus checks at every call.
`verus --no-cheating` reports exactly these two.

**Evidence.** The developer's contracts of `format` and `write` verify, and so do the exact ones.
[`verified_examples.rs`](itoa/src/verified_examples.rs) proves upstream's doc examples:
`format(128u64)@ == "128"` and `format(1234i32)@ == "1234"`. It also proves `"-128"`, `"0"`, and that
`format(i8::MIN)` and `format(u16::MAX)` have exactly `MAX_STR_LEN` chars.
Negative controls M21–M25 and M28 target the new contracts and are all rejected.

### C2. `Buffer::new`, `Default`, `Clone` had no postcondition (fixed: A2)

The developer's spec adds a closed `Buffer::len()` and ensures `result.len() == i128::MAX_STR_LEN` on all three.
Claude's crate states nothing. The fact is trivial, and no function uses it (see H5), but it is part of the
reference contract, so it is added.

### C3. Documentation (fixed here)

Claude's `VERIFICATION.md` says that the associated-constant crash forces the impls outside `verus!`. The
developer's plain constants avoid it, so the statement is incomplete. `VERIFICATION.md` in this folder is
updated to the fixed crate. Two new Verus findings are recorded there: a projection
`const MAX_STR_LEN = <u64 as Integer>::MAX_STR_LEN` in the `usize` impl silently breaks proofs about `u64`, and a
compile-time `assert!` that reads a verified impl's constant crashes Verus.

### C4. An upstream CI step failed (fixed)

Claude's `VERIFICATION.md` lists six upstream CI steps and says "All pass". Upstream's CI also runs
`cargo clippy --tests --benches -- -Dclippy::all -Dclippy::pedantic`. That passes on upstream with this
toolchain and failed on Claude's crate with 9 errors. Five are `semicolon_if_nothing_returned` on erased
`proof` blocks, two `inline_always` on the `get_unchecked`/`write_unchecked` stand-ins, and one `too_many_lines` on
`u128::fmt`. The last, `ref_as_ptr`, fires on upstream's own `slice_buffer_to_str`, because clippy enables it
once `rust-version` is 1.76 or later and Claude raised it from 1.68 to 1.95. The fixed crate allows these four
lints at the crate level, next to upstream's own `allow` list (a build-only change), and the step passes.

### Checked and correct

- **Contracts.** Claude's contracts imply the developer's for `fmt`, `enc_16lsd`, `divmod100`, `div_rem_1e16` and
  `mulhi`. The fixed crate states both on each function, and both verify. For `divmod100`, `div_rem_1e16` and
  `mulhi` the converse also holds trivially.
- **The extra precondition of `enc_16lsd`** (`n < 10^16`) is necessary (H1).
- **Claude's code changes** (`fmt` generic over the buffer length, the `Signed` trait, the `unsigned_abs`
  expression, the `get_unchecked` stand-ins, the `enc_16lsd` loop) are kept unchanged. The upstream tests and
  the differential test pass.
- **Claude's results reproduce**: 105 verified, 0 errors with `--no-cheating`. Its 20 negative controls are
  rejected on the fixed crate too (M16/M17 re-anchored, since the constants moved).

## Findings in the developer's spec

H1–H4 change what the spec means; H5 and H6 are minor. The placeholder bodies (`assume(false)` 7 times,
`external_body` 15 times) are expected in a file that states specs without proofs, so they are not counted as
mistakes.

| # | Item | Problem |
|---|---|---|
| H1 | `enc_16lsd` | **Missing precondition `n < 10^16`.** The code divides `n` by 10^4 three times, then calls `divmod100` on the rest, which must be below 10^4. For larger `n`, release builds compute pair indices past the end of the 200-byte `DECIMAL_PAIRS` table and read them with `get_unchecked`, which is undefined behaviour. For `n = 10^16` the indices are 200 and 201; for `u64::MAX` they reach 36,044,089 (replayed with upstream's arithmetic). Debug builds panic in `divmod100`'s `debug_assert!`. So no implementation of this code meets the contract. The crate's only callers pass `n % 10^16`, so the crate itself is fine. Claude's contract has the precondition |
| H2 | `slice_buffer_to_str` | **The precondition can never be established.** `initialized_ascii_suffix` is `uninterp`, so no caller can prove it. The developer's `write` bodies therefore use `assume(false)` or `external_body`. The transcription defines it as its comment says: from `offset` on, every element is initialized and below 128 |
| H3 | `Unsigned::fmt`, `slice_buffer_to_str`, `write` | **The contracts do not compose.** `write`'s contract (`result@ =~= decimal_unsigned(self)`) cannot follow from the contracts of what `write` calls. `fmt` promises only the offset, not what is in the buffer, and `slice_buffer_to_str` promises only the length and ASCII-ness of its result, not its content. Claude's `fmt` contract has the content (`holds`), and the fixed `slice_buffer_to_str` contract has the bytes; with them `write` verifies |
| H4 | `Buffer::format`, `Sealed::write` (trait) | **The contract does not determine the output.** It says only "some decimal text of 1 to `MAX_STR_LEN` chars". An implementation that returns `"0"` for every input satisfies it, as does one that returns `"007"`, since `is_decimal_text` allows leading zeros and `"-0"`. It cannot say more: `format` is generic over `I`, and the trait-level contract of `write`, the only one `format` can use, is equally weak. The fixed crate adds `Sealed::spec_int` and states `result@ == decimal_signed(i.spec_int())`, which proves `format(128u64)@ == "128"` |
| H5 | `Buffer::new`, `Default`, `Clone` | (minor) `Buffer::len()` is `closed`, and no function takes a buffer length as a precondition, so a client can do nothing with `result.len() == i128::MAX_STR_LEN`. Harmless; kept |
| H6 | `enc_16lsd` | (minor) The postcondition says only that the slice keeps its length, nothing about the digits written. Weak, not wrong |

Positive: the developer's plain constants for `MAX_STR_LEN`, with compile-time checks against upstream's
formula, work around the Verus crash that made Claude leave the impls trusted. They made A1 possible.

## How the specs were compared

1. Both specs were read against upstream `../src/lib.rs` and the crate's documentation.
2. The developer's definitions are transcribed in [`itoa/src/human_spec.rs`](itoa/src/human_spec.rs), unchanged
   except that `initialized_ascii_suffix` is defined (H2).
3. [`itoa/src/spec_equiv.rs`](itoa/src/spec_equiv.rs) proves that the two text definitions agree, and connects
   bytes in the buffer to the chars of the returned `&str`, using vstd's UTF-8 lemmas.
4. The developer's contracts are stated on Claude's functions, each clause marked `// Human spec`, and verified.
   For `slice_buffer_to_str`, whose contract is trusted, a lemma proves the developer's postcondition from the
   trusted one, so the trusted contract stays minimal.
5. Each new contract was exercised by verified clients ([`verified_examples.rs`](itoa/src/verified_examples.rs))
   and by negative controls (M21–M28).

## Results (fixed crate)

| | |
|---|---|
| Verus | **165 verified, 0 errors**, about 5 s; no warnings or trigger notes |
| `--no-cheating` | exactly 2 trust markers: `buffer_of` and `slice_buffer_to_str` in `trusted.rs` |
| Proof stability | the same result with SMT seeds 0 to 39, 42 and 1234 |
| `cargo build` | passes, 0 warnings; also with `--features no-panic --release` and `--no-default-features` |
| `cargo clippy --tests --benches -- -Dclippy::all -Dclippy::pedantic` | passes (failed on Claude's crate: C4) |
| Upstream tests | 11/11 integration, 2/2 doc (debug and release) |
| Differential test | 8,144,968 values: fixed == upstream == `std`, all 12 types, with `no-panic`; `MAX_STR_LEN` agrees for all 12 |
| Machine code | `Buffer::format` identical to Claude's crate for all 12 types |
| Negative controls | 28/28 rejected (`negative_controls.py`) |
| `check_trusted.py` | trusted bodies are upstream code; verified shells keep upstream's statements |

Details, the full contract table and the trusted base are in [`VERIFICATION.md`](VERIFICATION.md).
