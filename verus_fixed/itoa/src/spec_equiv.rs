//! The two specifications agree. Claude's (`spec.rs`) describes the output as bytes (`dec`,
//! `dec_int`); the developer's (`human_spec.rs`) describes it as chars (`decimal_unsigned`,
//! `decimal_signed`), as the view of the returned `&str`. These lemmas show that they are the
//! same text, and connect the bytes in the buffer to the chars of the returned `&str`.
//!
//! Ghost code only: `verus!` erases all of it from normal builds. Nothing here is trusted.

#![allow(unused_imports)]
use crate::human_spec::*;
use crate::spec::*;
#[cfg(verus_keep_ghost)]
use crate::trusted::suffix_bytes;
use core::mem::MaybeUninit;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::raw_ptr::MemContents;
#[cfg(verus_keep_ghost)]
use vstd::string::{is_ascii, StringSliceAdditionalSpecFns};
#[cfg(verus_keep_ghost)]
use vstd::utf8::{
    encode_utf8, encode_utf8_decode_utf8, encode_utf8_valid_utf8, is_ascii_chars,
    is_ascii_chars_encode_utf8, valid_utf8,
};

verus! {

/// Every byte of `bytes` is ASCII (below 128).
pub open spec fn all_ascii(bytes: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < bytes.len() ==> #[trigger] bytes[i] < 128
}

/// The chars of the bytes `bytes`, one char per byte.
pub open spec fn ascii_chars(bytes: Seq<u8>) -> Seq<char> {
    Seq::new(bytes.len(), |i: int| bytes[i] as char)
}

// ===== Digits =====

/// Claude's digit byte (`digit`) is the developer's digit char (`decimal_digit`).
pub proof fn lemma_digit_char(d: nat)
    requires
        d < 10,
    ensures
        digit(d) as char == decimal_digit(d),
        48 <= digit(d) <= 57,
{
    assert(d == 0 || d == 1 || d == 2 || d == 3 || d == 4 || d == 5 || d == 6 || d == 7 || d == 8
        || d == 9);
}

/// `dec` and `decimal_unsigned` are the same text.
pub proof fn lemma_dec_chars(n: nat)
    ensures
        ascii_chars(dec(n)) == decimal_unsigned(n),
    decreases n,
{
    lemma_digit_char(n % 10);
    if n < 10 {
        lemma_dec_pad_1(n);
        assert(ascii_chars(dec(n)) =~= decimal_unsigned(n));
    } else {
        lemma_dec_chars(n / 10);
        assert(dec(n) == dec(n / 10).push(digit(n % 10)));
        lemma_dec_len(n / 10);
        assert(ascii_chars(dec(n)) =~= ascii_chars(dec(n / 10)).push(digit(n % 10) as char));
    }
}

/// `decimal_unsigned(n)` has as many chars as `dec(n)` has bytes, and at least one.
pub proof fn lemma_dec_len_human(n: nat)
    ensures
        decimal_unsigned(n).len() == dec(n).len(),
        1 <= dec(n).len(),
{
    lemma_dec_chars(n);
    lemma_dec_value(n);
}

/// `dec_int` and `decimal_signed` are the same text, which is ASCII, has at least one char and
/// is decimal text in the developer's sense (`is_decimal_text`).
pub proof fn lemma_dec_int_text(n: int)
    ensures
        all_ascii(dec_int(n)),
        ascii_chars(dec_int(n)) == decimal_signed(n),
        is_decimal_text(decimal_signed(n)),
        is_ascii_chars(decimal_signed(n)),
        1 <= decimal_signed(n).len() == dec_int(n).len(),
{
    let m: nat = if n < 0 {
        (-n) as nat
    } else {
        n as nat
    };
    lemma_dec_value(m);
    lemma_dec_chars(m);
    let s = decimal_signed(n);
    if n < 0 {
        assert(ascii_chars(dec_int(n)) =~= seq!['-'].add(decimal_unsigned(m)));
        assert forall|i: int| 0 <= i < dec_int(n).len() implies #[trigger] dec_int(n)[i] < 128 by {
            if i > 0 {
                assert(dec_int(n)[i] == dec(m)[i - 1]);
            }
        }
        assert forall|k: int| 0 <= k < s.len() implies (s[k] >= '0' && s[k] <= '9') || (k == 0
            && s[k] == '-') by {
            if k > 0 {
                assert(s[k] == dec(m)[k - 1] as char);
            }
        }
    } else {
        assert forall|k: int| 0 <= k < s.len() implies (s[k] >= '0' && s[k] <= '9') || (k == 0
            && s[k] == '-') by {
            assert(s[k] == dec(m)[k] as char);
        }
    }
    assert forall|k: int| 0 <= k < s.len() implies '\0' <= #[trigger] s[k] <= '\u{7f}' by {
        assert(s[k] == dec_int(n)[k] as char);
    }
}

// ===== From bytes to `&str` =====

/// A `&str` whose UTF-8 bytes are all ASCII has one char per byte, and these bytes are valid
/// UTF-8 (the precondition of `str::from_utf8_unchecked`).
pub proof fn lemma_ascii_str(s: &str, bytes: Seq<u8>)
    requires
        s.spec_bytes() == bytes,
        all_ascii(bytes),
    ensures
        s@ == ascii_chars(bytes),
        is_ascii(s),
        valid_utf8(bytes),
{
    let cs = ascii_chars(bytes);
    assert forall|i: int| 0 <= i < cs.len() implies '\0' <= #[trigger] cs[i] <= '\u{7f}' by {
        assert(bytes[i] < 128);
    }
    is_ascii_chars_encode_utf8(cs);
    assert forall|i: int| 0 <= i < cs.len() implies #[trigger] encode_utf8(cs)[i] == bytes[i] by {
        assert(cs[i] as u8 == encode_utf8(cs)[i]);
        assert(bytes[i] < 128);
    }
    assert(encode_utf8(cs) =~= bytes);
    encode_utf8_valid_utf8(cs);
    encode_utf8_decode_utf8(cs);
    encode_utf8_decode_utf8(s@);
}

/// The `&str` whose UTF-8 bytes are `dec_int(n)` is the developer's `decimal_signed(n)`.
pub proof fn lemma_str_of_dec_int(n: int)
    ensures
        valid_utf8(dec_int(n)),
        forall|s: &str|
            #[trigger] s.spec_bytes() == dec_int(n) ==> {
                &&& s@ == decimal_signed(n)
                &&& is_ascii(s)
                &&& is_decimal_text(s@)
                &&& 1 <= s@.len() == dec_int(n).len()
            },
{
    lemma_dec_int_text(n);
    assert forall|s: &str| #[trigger] s.spec_bytes() == dec_int(n) implies {
        &&& s@ == decimal_signed(n)
        &&& is_ascii(s)
        &&& is_decimal_text(s@)
        &&& 1 <= s@.len() == dec_int(n).len()
    } by {
        lemma_ascii_str(s, dec_int(n));
    }
    if dec_int(n).len() >= 0 {
        // `valid_utf8(dec_int(n))`, from `lemma_ascii_str` applied to any string with these bytes.
        let cs = ascii_chars(dec_int(n));
        assert forall|i: int| 0 <= i < cs.len() implies '\0' <= #[trigger] cs[i] <= '\u{7f}' by {
            assert(dec_int(n)[i] < 128);
        }
        is_ascii_chars_encode_utf8(cs);
        assert forall|i: int| 0 <= i < cs.len() implies #[trigger] encode_utf8(cs)[i] == dec_int(n)[i] by {
            assert(cs[i] as u8 == encode_utf8(cs)[i]);
            assert(dec_int(n)[i] < 128);
        }
        assert(encode_utf8(cs) =~= dec_int(n));
        encode_utf8_valid_utf8(cs);
    }
}

/// When `buf[offset..]` holds exactly `bytes`, all ASCII, the precondition of the trusted
/// `slice_buffer_to_str` holds (`initialized_ascii_suffix`), and the bytes it reads are `bytes`.
pub proof fn lemma_holds_suffix(buf: Seq<MaybeUninit<u8>>, offset: int, bytes: Seq<u8>)
    requires
        holds(buf, offset, bytes),
        offset + bytes.len() == buf.len(),
        all_ascii(bytes),
    ensures
        forall|i: int|
            offset <= i < buf.len() ==> {
                &&& (#[trigger] buf[i]).mem_contents().is_init()
                &&& buf[i].mem_contents().value() < 128
            },
        suffix_bytes(buf, offset) == bytes,
{
    reveal(holds);
    assert forall|i: int| offset <= i < buf.len() implies {
        &&& (#[trigger] buf[i]).mem_contents().is_init()
        &&& buf[i].mem_contents().value() < 128
    } by {
        assert(buf[i].mem_contents() == MemContents::Init(bytes[i - offset]));
    }
    assert forall|i: int| 0 <= i < bytes.len() implies #[trigger] suffix_bytes(buf, offset)[i] == bytes[i] by {
        assert(buf[offset + i].mem_contents() == MemContents::Init(bytes[(offset + i) - offset]));
    }
    assert(suffix_bytes(buf, offset) =~= bytes);
}

// ===== The trusted contract of `slice_buffer_to_str` =====

/// The trusted contract of `slice_buffer_to_str` (`trusted.rs`) implies the developer's
/// postcondition for it: under the developer's precondition, the result has `buf.len() - offset`
/// chars and is ASCII. (The trusted contract also fixes the content: the bytes of the result
/// are the bytes in the buffer.)
pub proof fn lemma_slice_buffer_to_str_human(buf: &[MaybeUninit<u8>], offset: usize, result: &str)
    requires
        offset <= buf.len(),
        initialized_ascii_suffix(buf, offset),
        result.spec_bytes() == suffix_bytes(buf@, offset as int),
    ensures
        result@.len() == buf.len() - offset,
        result.is_ascii(),
{
    let bytes = suffix_bytes(buf@, offset as int);
    assert forall|i: int| 0 <= i < bytes.len() implies #[trigger] bytes[i] < 128 by {
        assert(buf@[offset + i].mem_contents().value() < 128);
    }
    lemma_ascii_str(result, bytes);
}

} // verus!
