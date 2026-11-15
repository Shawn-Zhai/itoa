// Proofs for the obligations that compare_specs.py generates for itoa: the verified crate
// (verus_fixed/itoa) against the developer's spec (verus_human_written_spec/itoa).
//
// This file holds only proof code, checked by Verus:
//   * lemmas (`proof fn`, helper `spec fn`), placed in the generated module, where the gold
//     definitions are `gold_defs::..` and the verified crate's are `crate::..`;
//   * hints: a `proof { ... }` block after a marker line
//         // @hint <obligation> before|after
//     inserted into that obligation's wrapper before or after the call it checks (`*`: every
//     obligation). In a wrapper, `slf` is the receiver and `ret` the result;
//   * notes: comment lines after `// @note <obligation>`, explaining why that obligation stays
//     unproved (the specs differ). The report shows them next to the failure; they are not checked;
//   * `// @interpret <name>`: a definition for a gold `uninterp` placeholder (a modeling choice);
//   * `// @call <obligation> <expression>`: how the wrapper calls the function, when the two
//     signatures differ (a modeling choice).
// assume, admit, external_body, axioms and other trusted constructs are rejected.

// ===================================================== the two transcriptions agree
// The verified crate has its own transcription of the developer's spec functions
// (`crate::human_spec`). The generated module has the developer's, copied unchanged
// (`gold_defs`). They are the same text, but two functions to Verus; these lemmas connect them.

broadcast proof fn lemma_decimal_digit_same(d: nat)
    ensures
        #[trigger] gold_defs::decimal_digit(d) == crate::human_spec::decimal_digit(d),
{
}

broadcast proof fn lemma_decimal_unsigned_same(n: nat)
    ensures
        #[trigger] gold_defs::decimal_unsigned(n) == crate::human_spec::decimal_unsigned(n),
    decreases n,
{
    lemma_decimal_digit_same(n);
    lemma_decimal_digit_same(n % 10);
    if n >= 10 {
        lemma_decimal_unsigned_same(n / 10);
    }
}

broadcast proof fn lemma_decimal_signed_same(n: int)
    ensures
        #[trigger] gold_defs::decimal_signed(n) == crate::human_spec::decimal_signed(n),
{
    if n < 0 {
        lemma_decimal_unsigned_same((-n) as nat);
    } else {
        lemma_decimal_unsigned_same(n as nat);
    }
}

broadcast proof fn lemma_is_decimal_text_same(s: Seq<char>)
    ensures
        #[trigger] gold_defs::is_decimal_text(s) == crate::human_spec::is_decimal_text(s),
{
}

broadcast group group_same {
    lemma_decimal_digit_same,
    lemma_decimal_unsigned_same,
    lemma_decimal_signed_same,
    lemma_is_decimal_text_same,
}

// ===================================================== the developer's placeholder
// `initialized_ascii_suffix` is `uninterp` in the developer's spec, so no caller could establish
// the precondition of `slice_buffer_to_str`. Read as its comment says ("buffer content starting
// from `offset` index must be initialized and ascii characters").

// @interpret initialized_ascii_suffix
spec fn initialized_ascii_suffix(buf: &[MaybeUninit<u8>], offset: usize) -> bool {
    forall|i: int|
        offset <= i < buf@.len() ==> {
            &&& (#[trigger] buf@[i]).mem_contents().is_init()
            &&& buf@[i].mem_contents().value() < 128
        }
}

// ===================================================== hints

// @hint * before
proof {
    broadcast use group_same;
}

// `fmt` (`buf: &mut Self::Buffer`): the buffer has room for every value (the verified `fmt`
// requires it for its generic buffer length).
// @hint claude_implies_gold__u8__Unsigned__fmt before
proof {
    crate::lemma_max_str_len_u8();
}

// @hint claude_implies_gold__u16__Unsigned__fmt before
proof {
    crate::lemma_max_str_len_u16();
}

// @hint claude_implies_gold__u32__Unsigned__fmt before
proof {
    crate::lemma_max_str_len_u32();
}

// @hint claude_implies_gold__u64__Unsigned__fmt before
proof {
    crate::lemma_max_str_len_u64();
}

// @hint claude_implies_gold__u128__Unsigned__fmt before
proof {
    crate::lemma_max_str_len_u128();
}

// The verified contract gives the bytes of the result; the developer's asks for its length and
// that it is ASCII.
// @hint claude_implies_gold__slice_buffer_to_str after
proof {
    crate::spec_equiv::lemma_slice_buffer_to_str_human(buf, offset, ret);
}

// ===================================================== calls

// The developer's `enc_16lsd` takes the offset as the const generic `OFFSET` (as upstream does);
// the verified one takes it as an argument.
// @call claude_implies_gold__enc_16lsd crate::enc_16lsd(buf, OFFSET, n)

// ===================================================== notes

// @note claude_implies_gold__enc_16lsd
// The developer's precondition lacks `n < 10^16`, which the verified `enc_16lsd` requires
// (finding H1 in SPEC_REVIEW.md). For larger `n` the code reads past the end of the 200-byte
// DECIMAL_PAIRS table, so the developer's contract cannot be met.

// @note gold_implies_claude__enc_16lsd
// The developer's signature has the offset as a const generic, the verified one as a run-time
// argument, so a function with the verified signature cannot call one with the developer's.
// The developer's postcondition also says nothing about the digits written (H6).

// @note gold_implies_claude__Buffer__format
// The developer's `format` contract does not determine the output: any decimal text of the right
// length satisfies it (H4). The verified contract states the exact text, `decimal_signed(i)`.

// @note gold_implies_claude__slice_buffer_to_str
// The developer's postcondition gives only the result's length and that it is ASCII, not which
// bytes it holds (H3); the verified contract says they are the buffer's.

// @note gold_implies_claude__u8__Unsigned__fmt
// The developer's `fmt` takes the exact buffer type of the integer (`&mut Self::Buffer`); the
// verified `fmt` takes any long-enough array (`[_; N]`), so the developer's contract cannot stand
// in for it. It also says nothing about the bytes written (H3).

// @note gold_implies_claude__u16__Unsigned__fmt
// As for u8: the developer's `fmt` covers only `N == MAX_STR_LEN` and not the bytes written (H3).

// @note gold_implies_claude__u32__Unsigned__fmt
// As for u8: the developer's `fmt` covers only `N == MAX_STR_LEN` and not the bytes written (H3).

// @note gold_implies_claude__u64__Unsigned__fmt
// As for u8: the developer's `fmt` covers only `N == MAX_STR_LEN` and not the bytes written (H3).

// @note gold_implies_claude__u128__Unsigned__fmt
// As for u8: the developer's `fmt` covers only `N == MAX_STR_LEN` and not the bytes written (H3).
