//! TRUSTED code: the two raw-pointer reinterpretations that Verus cannot verify.
//!
//! Each item is `#[verifier::external_body]`: Verus does not check its body, but it checks every
//! call against the contract stated here, so these contracts are the whole trusted interface.
//! `verus --no-cheating` lists exactly these two items. Everything else in the crate is verified,
//! including the `write` methods and `Buffer::format`, which call these.
//!
//! | id | item | upstream code | why trusted |
//! |----|------|---------------|-------------|
//! | T1 | `buffer_of` | the cast in `Buffer::format` | reinterprets the `[MaybeUninit<u8>; 40]` buffer as `I::Buffer` through a raw pointer, which needs a `PointsTo` permission in Verus |
//! | T3 | `slice_buffer_to_str` | the whole function | reinterprets `&[MaybeUninit<u8>]` as `&[u8]` through a raw pointer; `get_unchecked(offset..)` is unspecified |
//!
//! (T2, the `Integer` and `Sealed` impls, was trusted in Claude's first pass. It is verified now.)
//!
//! Obligations, checked by inspection (see `SPEC_REVIEW.md`):
//!
//! - T1: for every `I: Integer`, `I::Buffer` is an array of `I::MAX_STR_LEN` elements of
//!   `MaybeUninit<u8>` (`lib.rs`, `impl_Integer!` and `impl_Integer_size!`), and Verus proves
//!   `I::MAX_STR_LEN <= 40` (`Integer::lemma_max_str_len`). So the cast stays inside `bytes`, and
//!   `MaybeUninit<u8>` has no alignment or validity requirement. No contract is needed: `write`
//!   accepts any buffer.
//! - T3: the contract is the body's meaning. `get_unchecked(offset..)` needs `offset <= buf.len()`;
//!   reading the elements as `u8` needs them initialized; `str::from_utf8_unchecked` needs valid
//!   UTF-8, which ASCII bytes are (`spec_equiv::lemma_ascii_str` proves it), and vstd specifies
//!   its result by `res.spec_bytes() == v@`, which is the `ensures` below.

#![allow(unused_imports)]
#[cfg(verus_keep_ghost)]
use crate::human_spec::initialized_ascii_suffix;
use crate::{private, Integer};
use core::mem::MaybeUninit;
use core::str;
#[cfg(feature = "no-panic")]
use no_panic::no_panic;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// The initialized bytes `buf[offset..]`.
pub open spec fn suffix_bytes(buf: Seq<MaybeUninit<u8>>, offset: int) -> Seq<u8> {
    Seq::new((buf.len() - offset) as nat, |i: int| buf[offset + i].mem_contents().value())
}

// ===== T1 =====

/// `bytes` reinterpreted as `I::Buffer`. This is upstream's cast from `Buffer::format`
/// (`self.bytes.as_mut_ptr().cast::<I::Buffer>()` and `&mut *buf_ptr`), moved into its own
/// function so that the rest of `format` is verified.
#[verifier::external_body]
#[inline(always)]
pub(crate) fn buffer_of<I: Integer>(bytes: &mut [MaybeUninit<u8>; private::I128_MAX_STR_LEN]) -> &mut I::Buffer {
    let buf_ptr = bytes.as_mut_ptr().cast::<I::Buffer>();
    unsafe { &mut *buf_ptr }
}

// ===== T3 =====

/// This function converts a slice of ascii characters into a `&str` starting
/// from `offset`.
///
/// # Safety
///
/// `buf` content starting from `offset` index MUST BE initialized and MUST BE
/// ascii characters.
#[cfg_attr(feature = "no-panic", no_panic)]
#[verifier::external_body]
pub(crate) unsafe fn slice_buffer_to_str(buf: &[MaybeUninit<u8>], offset: usize) -> (result: &str)
    requires
        // Human spec
        offset <= buf.len(),
        initialized_ascii_suffix(buf, offset),
    ensures
        result.spec_bytes() == suffix_bytes(buf@, offset as int),
{
    // SAFETY: `offset` is always included between 0 and `buf`'s length.
    let written = unsafe { buf.get_unchecked(offset..) };
    // SAFETY: (`assume_init_ref`) All buf content since offset is set.
    // SAFETY: (`from_utf8_unchecked`) Writes use ASCII from the lookup table exclusively.
    unsafe { str::from_utf8_unchecked(&*(written as *const [MaybeUninit<u8>] as *const [u8])) }
}

} // verus!
