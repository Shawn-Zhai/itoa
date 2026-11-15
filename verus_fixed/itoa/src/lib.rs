//! [![github]](https://github.com/dtolnay/itoa)&ensp;[![crates-io]](https://crates.io/crates/itoa)&ensp;[![docs-rs]](https://docs.rs/itoa)
//!
//! [github]: https://img.shields.io/badge/github-8da0cb?style=for-the-badge&labelColor=555555&logo=github
//! [crates-io]: https://img.shields.io/badge/crates.io-fc8d62?style=for-the-badge&labelColor=555555&logo=rust
//! [docs-rs]: https://img.shields.io/badge/docs.rs-66c2a5?style=for-the-badge&labelColor=555555&logo=docs.rs
//!
//! <br>
//!
//! This crate provides a fast conversion of integer primitives to decimal
//! strings. The implementation comes straight from [libcore] but avoids the
//! performance penalty of going through [`core::fmt::Formatter`].
//!
//! See also [`zmij`] for printing floating point primitives.
//!
//! [libcore]: https://github.com/rust-lang/rust/blob/1.92.0/library/core/src/fmt/num.rs#L190-L253
//! [`zmij`]: https://github.com/dtolnay/zmij
//!
//! # Example
//!
//! ```
//! fn main() {
//!     let mut buffer = itoa::Buffer::new();
//!     let printed = buffer.format(128u64);
//!     assert_eq!(printed, "128");
//! }
//! ```
//!
//! # Performance
//!
//! The [itoa-benchmark] compares this library and other Rust integer formatting
//! implementations across a range of integer sizes. The vertical axis in this
//! chart shows nanoseconds taken by a single execution of
//! `itoa::Buffer::new().format(value)` so a lower result indicates a faster
//! library.
//!
//! [itoa-benchmark]: https://github.com/dtolnay/itoa-benchmark
//!
//! ![performance](https://raw.githubusercontent.com/dtolnay/itoa/master/itoa-benchmark.png)

#![doc(html_root_url = "https://docs.rs/itoa/1.0.19")]
#![no_std]
#![allow(
    clippy::cast_lossless,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::expl_impl_clone_on_copy,
    clippy::identity_op,
    clippy::items_after_statements,
    clippy::must_use_candidate,
    clippy::needless_doctest_main,
    clippy::unreadable_literal
)]
// Lints that only the Verus annotations trigger: erased `proof` blocks at the end of a block
// (`semicolon_if_nothing_returned`), the `#[inline(always)]` stand-ins (`inline_always`), the
// annotated `u128::fmt` (`too_many_lines`), and `ref_as_ptr`, which clippy applies to upstream's
// `slice_buffer_to_str` once `rust-version` is 1.76 or later (upstream: 1.68).
#![allow(
    clippy::inline_always,
    clippy::ref_as_ptr,
    clippy::semicolon_if_nothing_returned,
    clippy::too_many_lines
)]

// The developer's specification, transcribed (ghost code only).
mod human_spec;
mod spec;
// Lemmas relating Claude's specification to the developer's (ghost code only).
mod spec_equiv;
mod std_ext;
// The code that is trusted rather than verified: two `external_body` functions.
mod trusted;
mod u128_ext;
// Verified clients of `Buffer::format` (only compiled under Verus).
#[cfg(verus_keep_ghost)]
mod verified_examples;

// The developer's spec functions (`decimal_signed`, `is_decimal_text`, ...) are at the crate root
// in their file; so they are here, for Verus clients. (Ghost code: nothing in normal builds.)
#[cfg(verus_keep_ghost)]
pub use crate::human_spec::*;
#[cfg(verus_keep_ghost)]
use crate::spec::*;
#[cfg(verus_keep_ghost)]
use crate::spec_equiv::*;
use crate::std_ext::{get_unchecked, write_unchecked};
use crate::trusted::{buffer_of, slice_buffer_to_str};
use core::hint;
use core::mem::{self, MaybeUninit};
#[cfg(feature = "no-panic")]
use no_panic::no_panic;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::utf8::is_ascii_chars_encode_utf8;

verus! {

/// A correctly sized stack allocation for the formatted integer to be written
/// into.
///
/// # Example
///
/// ```
/// let mut buffer = itoa::Buffer::new();
/// let printed = buffer.format(1234);
/// assert_eq!(printed, "1234");
/// ```
pub struct Buffer {
    // (Upstream: `i128::MAX_STR_LEN`, the same constant. Verus crashes on an associated constant
    // used as an array length, so array lengths use the plain constants of `private`.)
    bytes: [MaybeUninit<u8>; private::I128_MAX_STR_LEN],
}

impl Default for Buffer {
    #[inline]
    fn default() -> (result: Buffer)
        ensures
            // Human spec
            result.len() == i128::MAX_STR_LEN,
    {
        Buffer::new()
    }
}

impl Copy for Buffer {}

#[allow(clippy::non_canonical_clone_impl)]
impl Clone for Buffer {
    #[inline]
    fn clone(&self) -> (result: Self)
        ensures
            // Human spec
            result.len() == i128::MAX_STR_LEN,
    {
        Buffer::new()
    }
}

impl Buffer {
    /// The length of the underlying byte array (`bytes` is private). (From the developer's spec.)
    pub closed spec fn len(&self) -> usize {
        self.bytes.len()
    }

    /// This is a cheap operation; you don't need to worry about reusing buffers
    /// for efficiency.
    #[inline]
    #[cfg_attr(feature = "no-panic", no_panic)]
    pub fn new() -> (result: Buffer)
        ensures
            // Human spec
            result.len() == i128::MAX_STR_LEN,
    {
        let bytes = [MaybeUninit::<u8>::uninit(); private::I128_MAX_STR_LEN];
        Buffer { bytes }
    }

    /// Print an integer into this buffer and return a reference to its string
    /// representation within the buffer.
    #[cfg_attr(feature = "no-panic", no_panic)]
    pub fn format<I: Integer>(&mut self, i: I) -> (result: &str)
        ensures
            // The decimal representation of `i`.
            result@ == decimal_signed(i.spec_int()),
            // Human spec
            is_decimal_text(result@),
            1 <= result@.len(),
            result@.len() <= I::MAX_STR_LEN,
    {
        // (Upstream: `let buf_ptr = self.bytes.as_mut_ptr().cast::<I::Buffer>();` and
        // `i.write(unsafe { &mut *buf_ptr })`. The cast is the trusted `buffer_of`.)
        let string = i.write(buffer_of::<I>(&mut self.bytes));
        proof {
            i.lemma_max_str_len();
            lemma_dec_int_text(i.spec_int());
            is_ascii_chars_encode_utf8(string@);
        }
        if string.len() > I::MAX_STR_LEN {
            unsafe { hint::unreachable_unchecked() };
        }
        string
    }
}

/// An integer that can be written into an [`itoa::Buffer`][Buffer].
///
/// This trait is sealed and cannot be implemented for types outside of itoa.
pub trait Integer: private::Sealed {
    /// The maximum length of string that formatting an integer of this type can
    /// produce on the current target platform.
    const MAX_STR_LEN: usize;

    /// Every value of the type fits in `MAX_STR_LEN` bytes, and `MAX_STR_LEN` fits in a
    /// `Buffer`. (The `lemma_max_str_len_*` lemmas below also show that `MAX_STR_LEN` is the
    /// length of the longest decimal representation, as documented.)
    proof fn lemma_max_str_len(self)
        ensures
            decimal_signed(self.spec_int()).len() <= Self::MAX_STR_LEN,
            Self::MAX_STR_LEN <= private::I128_MAX_STR_LEN,
    ;
}

// Seal to prevent downstream implementations of the Integer trait.
mod private {
    #[cfg(verus_keep_ghost)]
    use crate::human_spec::*;
    #[cfg(verus_keep_ghost)]
    use vstd::prelude::*;

    // `MAX_STR_LEN` of each type, as a plain constant: Verus crashes on an associated constant
    // used as an array length (see `SPEC_REVIEW.md`). `impl_Integer!` checks each one against
    // upstream's definition (`MAX.ilog10() + 1`, or `+ 2` for the signed types) at compile time.
    pub const U8_MAX_STR_LEN: usize = 3;
    pub const I8_MAX_STR_LEN: usize = 4;
    pub const U16_MAX_STR_LEN: usize = 5;
    pub const I16_MAX_STR_LEN: usize = 6;
    pub const U32_MAX_STR_LEN: usize = 10;
    pub const I32_MAX_STR_LEN: usize = 11;
    pub const U64_MAX_STR_LEN: usize = 20;
    pub const I64_MAX_STR_LEN: usize = 20;
    pub const U128_MAX_STR_LEN: usize = 39;
    pub const I128_MAX_STR_LEN: usize = 40;

    #[doc(hidden)]
    pub trait Sealed: Copy {
        #[doc(hidden)]
        type Buffer: 'static;

        /// The value of `self`.
        spec fn spec_int(self) -> int;

        fn write(self, buf: &mut Self::Buffer) -> (result: &str)
            ensures
                // The decimal representation of `self`.
                result@ == decimal_signed(self.spec_int()),
                // Human spec
                is_decimal_text(result@),
                1 <= result@.len(),
                result@.len() <= I128_MAX_STR_LEN,
        ;
    }
}

} // verus!

macro_rules! impl_Integer {
    ($Signed:ident, $Unsigned:ident, $signed_len:ident, $unsigned_len:ident, $signed_lemma:ident, $unsigned_lemma:ident) => {
        const _: () = {
            assert!($Signed::MIN < 0, "need signed");
            assert!($Unsigned::MIN == 0, "need unsigned");
            assert!($Signed::BITS == $Unsigned::BITS, "need counterparts");
            // The lengths are plain constants (see `private`); upstream's definitions:
            assert!(private::$unsigned_len == $Unsigned::MAX.ilog10() as usize + 1, "wrong unsigned length");
            assert!(private::$signed_len == $Signed::MAX.ilog10() as usize + 2, "wrong signed length");
        };

        verus! {

        impl Integer for $Unsigned {
            const MAX_STR_LEN: usize = private::$unsigned_len;

            proof fn lemma_max_str_len(self) {
                $unsigned_lemma();
                lemma_dec_int_text(self as int);
            }
        }

        impl private::Sealed for $Unsigned {
            type Buffer = [MaybeUninit<u8>; private::$unsigned_len];

            open spec fn spec_int(self) -> int {
                self as int
            }

            #[inline]
            #[cfg_attr(feature = "no-panic", no_panic)]
            fn write(self, buf: &mut Self::Buffer) -> (result: &str)
                ensures
                    // Human spec
                    result@ =~= decimal_unsigned(self as nat),
                    result@.len() <= Self::MAX_STR_LEN,
            {
                proof {
                    $unsigned_lemma();
                    lemma_dec_int_text(self as int);
                    lemma_str_of_dec_int(self as int);
                }
                let offset = Unsigned::fmt(self, buf);
                proof {
                    lemma_holds_suffix(buf@, offset as int, dec(self as nat));
                }
                // SAFETY: Starting from `offset`, all elements of the slice have been set.
                unsafe { slice_buffer_to_str(buf, offset) }
            }
        }

        impl Integer for $Signed {
            const MAX_STR_LEN: usize = private::$signed_len;

            proof fn lemma_max_str_len(self) {
                $signed_lemma();
                lemma_dec_int_text(self as int);
            }
        }

        impl private::Sealed for $Signed {
            type Buffer = [MaybeUninit<u8>; private::$signed_len];

            open spec fn spec_int(self) -> int {
                self as int
            }

            #[inline]
            #[cfg_attr(feature = "no-panic", no_panic)]
            fn write(self, buf: &mut Self::Buffer) -> (result: &str)
                ensures
                    // Human spec
                    result@ =~= decimal_signed(self as int),
                    result@.len() <= Self::MAX_STR_LEN,
            {
                proof {
                    $signed_lemma();
                    lemma_dec_int_text(self as int);
                    lemma_str_of_dec_int(self as int);
                }
                // The formatting (upstream's body of this method, up to here) is in the
                // verified `Signed::fmt`.
                let offset = Signed::fmt(self, buf);
                proof {
                    lemma_holds_suffix(buf@, offset as int, dec_int(self as int));
                }
                // SAFETY: Starting from `offset`, all elements of the slice have been set.
                unsafe { slice_buffer_to_str(buf, offset) }
            }
        }

        } // verus!
    };
}

impl_Integer!(i8, u8, I8_MAX_STR_LEN, U8_MAX_STR_LEN, lemma_max_str_len_i8, lemma_max_str_len_u8);
impl_Integer!(i16, u16, I16_MAX_STR_LEN, U16_MAX_STR_LEN, lemma_max_str_len_i16, lemma_max_str_len_u16);
impl_Integer!(i32, u32, I32_MAX_STR_LEN, U32_MAX_STR_LEN, lemma_max_str_len_i32, lemma_max_str_len_u32);
impl_Integer!(i64, u64, I64_MAX_STR_LEN, U64_MAX_STR_LEN, lemma_max_str_len_i64, lemma_max_str_len_u64);
impl_Integer!(i128, u128, I128_MAX_STR_LEN, U128_MAX_STR_LEN, lemma_max_str_len_i128, lemma_max_str_len_u128);

macro_rules! impl_Integer_size {
    ($t:ty as $primitive:ident, $len:ident #[cfg(target_pointer_width = $width:literal)]) => {
        verus! {

        #[cfg(target_pointer_width = $width)]
        impl Integer for $t {
            // (Upstream: `<$primitive as Integer>::MAX_STR_LEN`, which is `private::$len`. Defined
            // through the projection, it stops Verus from unfolding the spec functions of the
            // impls for `$primitive`; see `SPEC_REVIEW.md`.)
            const MAX_STR_LEN: usize = private::$len;

            proof fn lemma_max_str_len(self) {
                // Upstream's definition.
                assert(Self::MAX_STR_LEN == <$primitive as Integer>::MAX_STR_LEN);
                (self as $primitive).lemma_max_str_len();
            }
        }

        #[cfg(target_pointer_width = $width)]
        impl private::Sealed for $t {
            type Buffer = <$primitive as private::Sealed>::Buffer;

            open spec fn spec_int(self) -> int {
                self as int
            }

            #[inline]
            #[cfg_attr(feature = "no-panic", no_panic)]
            fn write(self, buf: &mut Self::Buffer) -> (result: &str)
                ensures
                    // Human spec
                    result@ =~= decimal_signed(self as int),
                    result@.len() <= Self::MAX_STR_LEN,
            {
                (self as $primitive).write(buf)
            }
        }

        } // verus!
    };
}

impl_Integer_size!(isize as i16, I16_MAX_STR_LEN #[cfg(target_pointer_width = "16")]);
impl_Integer_size!(usize as u16, U16_MAX_STR_LEN #[cfg(target_pointer_width = "16")]);
impl_Integer_size!(isize as i32, I32_MAX_STR_LEN #[cfg(target_pointer_width = "32")]);
impl_Integer_size!(usize as u32, U32_MAX_STR_LEN #[cfg(target_pointer_width = "32")]);
impl_Integer_size!(isize as i64, I64_MAX_STR_LEN #[cfg(target_pointer_width = "64")]);
impl_Integer_size!(usize as u64, U64_MAX_STR_LEN #[cfg(target_pointer_width = "64")]);

verus! {

#[repr(C, align(2))]
struct DecimalPairs([u8; 200]);

// The string of all two-digit numbers in range 00..99 is used as a lookup table.
// (Upstream writes it as a byte string literal, which Verus does not support.)
#[rustfmt::skip]
exec static DECIMAL_PAIRS: DecimalPairs
    ensures
        DECIMAL_PAIRS.0@ == decimal_pairs(),
{
    DecimalPairs([
        48, 48, 48, 49, 48, 50, 48, 51, 48, 52, 48, 53, 48, 54, 48, 55, 48, 56, 48, 57, // "00010203040506070809"
        49, 48, 49, 49, 49, 50, 49, 51, 49, 52, 49, 53, 49, 54, 49, 55, 49, 56, 49, 57, // "10111213141516171819"
        50, 48, 50, 49, 50, 50, 50, 51, 50, 52, 50, 53, 50, 54, 50, 55, 50, 56, 50, 57, // "20212223242526272829"
        51, 48, 51, 49, 51, 50, 51, 51, 51, 52, 51, 53, 51, 54, 51, 55, 51, 56, 51, 57, // "30313233343536373839"
        52, 48, 52, 49, 52, 50, 52, 51, 52, 52, 52, 53, 52, 54, 52, 55, 52, 56, 52, 57, // "40414243444546474849"
        53, 48, 53, 49, 53, 50, 53, 51, 53, 52, 53, 53, 53, 54, 53, 55, 53, 56, 53, 57, // "50515253545556575859"
        54, 48, 54, 49, 54, 50, 54, 51, 54, 52, 54, 53, 54, 54, 54, 55, 54, 56, 54, 57, // "60616263646566676869"
        55, 48, 55, 49, 55, 50, 55, 51, 55, 52, 55, 53, 55, 54, 55, 55, 55, 56, 55, 57, // "70717273747576777879"
        56, 48, 56, 49, 56, 50, 56, 51, 56, 52, 56, 53, 56, 54, 56, 55, 56, 56, 56, 57, // "80818283848586878889"
        57, 48, 57, 49, 57, 50, 57, 51, 57, 52, 57, 53, 57, 54, 57, 55, 57, 56, 57, 57, // "90919293949596979899"
    ])
}

// Returns {value / 100, value % 100} correct for values of up to 4 digits.
fn divmod100(value: u32) -> (r: (u32, u32))
    requires
        value < 10_000,
    ensures
        r.0 == value / 100,
        r.1 == value % 100,
        // Human spec
        r.1 < 100,
        (r.0 as nat) * 100 + r.1 as nat == value as nat,
{
    const EXP: u32 = 19; // 19 is faster or equal to 12 even for 3 digits.
    const SIG: u32 = (1 << EXP) / 100 + 1;
    proof {
        assert(1u32 << 19u32 == 524288) by (bit_vector);
        assert(((value * 5243) as u32) >> 19u32 == value / 100) by (bit_vector)
            requires
                value < 10_000,
        ;
    }
    let div = (value * SIG) >> EXP; // value / 100
    (div, value - div * 100)
}

} // verus!

// `slice_buffer_to_str` is in `trusted.rs`.

verus! {

broadcast use vstd::layout::layout_of_primitives;

proof fn lemma_and_15(x: u8)
    requires
        x < 10,
    ensures
        x & 15 == x,
{
    assert(x & 15u8 == x) by (bit_vector)
        requires
            x < 10u8,
    ;
}

trait Unsigned: Integer {
    /// The value of `self`.
    spec fn spec_val(self) -> nat;

    /// Writes the decimal representation of `self` at the end of `buf` and returns the index of
    /// its first byte. (Upstream takes `buf: &mut Self::Buffer`. Taking an array of any large
    /// enough length lets `Signed::fmt` format into the longer buffer of the signed type, where
    /// upstream converts a subslice of that buffer to `&mut Self::Buffer` with `try_into`, which
    /// Verus does not support.)
    fn fmt<const N: usize>(self, buf: &mut [MaybeUninit<u8>; N]) -> (offset: usize)
        requires
            dec(self.spec_val()).len() <= N,
        ensures
            offset + dec(self.spec_val()).len() == N,
            holds(final(buf)@, offset as int, dec(self.spec_val())),
            unchanged_outside(final(buf)@, old(buf)@, offset as int, N as int),
            // Human spec (stated there for `buf: &mut Self::Buffer`, that is `N == Self::MAX_STR_LEN`)
            offset < N,
            N - offset == decimal_unsigned(self.spec_val()).len(),
    ;
}

macro_rules! impl_Unsigned {
    ($Unsigned:ident) => {
        verus! {
        impl Unsigned for $Unsigned {
            spec fn spec_val(self) -> nat {
                self as nat
            }

            #[cfg_attr(feature = "no-panic", no_panic)]
            fn fmt<const N: usize>(self, buf: &mut [MaybeUninit<u8>; N]) -> (offset: usize) {
                let ghost v = self as nat;
                proof {
                    lemma_digits_start(v, N as nat, buf@);
                    lemma_dec_len_human(v);
                }
                // Count the number of bytes in buf that are not initialized.
                let mut offset = buf.len();
                // Consume the least-significant decimals from a working copy.
                let mut remain = self;

                // Format per four digits from the lookup table.
                // Four digits need a 16-bit $Unsigned or wider.
                while mem::size_of::<Self>() > 1
                    && remain
                        > 999
                            .try_into()
                            .expect("branch is not hit for types that cannot fit 999 (u8)")
                    invariant
                        v == self as nat,
                        digits_inv(v, N as nat, offset as nat, remain as nat, buf@, old(buf)@),
                    decreases remain,
                {
                    let ghost (offset0, remain0, buf0) = (offset as nat, remain as nat, buf@);
                    proof {
                        lemma_pow10_values();
                        lemma_digits_room(v, N as nat, offset0, remain0, buf0, old(buf)@, 4);
                    }
                    offset -= 4;

                    // pull two pairs
                    let scale: Self = 1_00_00
                        .try_into()
                        .expect("branch is not hit for types that cannot fit 1E4 (u8)");
                    let quad = remain % scale;
                    remain /= scale;
                    let (pair1, pair2) = divmod100(quad as u32);
                    write_unchecked(buf, offset + 0, *get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 0));
                    write_unchecked(buf, offset + 1, *get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 1));
                    write_unchecked(buf, offset + 2, *get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 0));
                    write_unchecked(buf, offset + 3, *get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 1));
                    proof {
                        lemma_chunk_4(remain0, pair1 as int, pair2 as int);
                        lemma_wrote(buf0, buf@, offset as int, dec_pad(remain0, 4));
                        lemma_digits_step(v, N as nat, offset0, remain0, 4, 10000, buf0, buf@, old(buf)@);
                    }
                }

                // Format per two digits from the lookup table.
                if remain > 9 {
                    let ghost (offset0, remain0, buf0) = (offset as nat, remain as nat, buf@);
                    proof {
                        lemma_pow10_values();
                        lemma_digits_room(v, N as nat, offset0, remain0, buf0, old(buf)@, 2);
                    }
                    offset -= 2;

                    let (last, pair) = divmod100(remain as u32);
                    remain = last as Self;
                    write_unchecked(buf, offset + 0, *get_unchecked(&DECIMAL_PAIRS.0, pair as usize * 2 + 0));
                    write_unchecked(buf, offset + 1, *get_unchecked(&DECIMAL_PAIRS.0, pair as usize * 2 + 1));
                    proof {
                        lemma_chunk_2(remain0, pair as int);
                        lemma_wrote(buf0, buf@, offset as int, dec_pad(remain0, 2));
                        lemma_digits_step(v, N as nat, offset0, remain0, 2, 100, buf0, buf@, old(buf)@);
                    }
                }

                // Format the last remaining digit, if any.
                let ghost (offset0, remain0, buf0) = (offset as nat, remain as nat, buf@);
                if remain != 0 || self == 0 {
                    proof {
                        lemma_pow10_values();
                        if remain0 != 0 {
                            lemma_digits_room(v, N as nat, offset0, remain0, buf0, old(buf)@, 1);
                        } else {
                            lemma_digits_zero(N as nat, offset0, buf0, old(buf)@);
                        }
                    }
                    offset -= 1;

                    // Either the compiler sees that remain < 10, or it prevents
                    // a boundary check up next.
                    let last = remain as u8 & 15;
                    proof {
                        lemma_and_15(remain as u8);
                    }
                    write_unchecked(buf, offset, 48 + last); // b'0' + last
                    // not used: remain = 0;
                    proof {
                        lemma_chunk_1(remain0);
                        lemma_wrote(buf0, buf@, offset as int, dec_pad(remain0, 1));
                        if remain0 != 0 {
                            lemma_digits_step(v, N as nat, offset0, remain0, 1, 10, buf0, buf@, old(buf)@);
                            lemma_digits_done(v, N as nat, offset as nat, buf@, old(buf)@);
                        } else {
                            lemma_dec_zero();
                        }
                    }
                }
                proof {
                    if !(remain0 != 0 || v == 0) {
                        lemma_digits_done(v, N as nat, offset as nat, buf@, old(buf)@);
                    }
                }

                offset
            }
        }
        }
    };
}

impl_Unsigned!(u8);
impl_Unsigned!(u16);
impl_Unsigned!(u32);
impl_Unsigned!(u64);

impl Unsigned for u128 {
    spec fn spec_val(self) -> nat {
        self as nat
    }

    // The largest proof in the crate: three paths into the loop, then the two steps after it.
    // Over 42 SMT seeds it takes 10M to 34M resource units, around the default limit (about
    // 30M), so it gets a higher one.
    #[verifier::rlimit(50)]
    #[cfg_attr(feature = "no-panic", no_panic)]
    fn fmt<const N: usize>(self, buf: &mut [MaybeUninit<u8>; N]) -> (offset: usize) {
        let ghost v = self as nat;
        proof {
            lemma_digits_start(v, N as nat, buf@);
            lemma_dec_len_human(v);
        }
        // Optimize common-case zero, which would also need special treatment due to
        // its "leading" zero.
        if self == 0 {
            let offset = buf.len() - 1;
            buf[offset] = MaybeUninit::new(48); // b'0'
            proof {
                lemma_dec_zero();
                lemma_wrote(old(buf)@, buf@, offset as int, dec(0));
            }
            return offset;
        }
        // Take the 16 least-significant decimals.
        let (quot_1e16, mod_1e16) = div_rem_1e16(self);
        // (Upstream writes `u128::MAX_STR_LEN` for `N`, the length of `buf`; here `buf` may be the
        // longer buffer of `i128`.)
        let (mut remain, mut offset) = if quot_1e16 == 0 {
            proof {
                lemma_u128_no_block(v, N as nat, mod_1e16 as nat, buf@);
            }
            (mod_1e16, N)
        } else {
            proof {
                lemma_u128_room(v, N as nat, 16);
            }
            // Write digits at buf[N-16..N].
            enc_16lsd(buf, N - 16, mod_1e16);
            let ghost buf1 = buf@;

            // Take another 16 decimals.
            let (quot2, mod2) = div_rem_1e16(quot_1e16);
            if quot2 == 0 {
                proof {
                    lemma_u128_one_block(
                        v,
                        N as nat,
                        quot_1e16 as nat,
                        mod_1e16 as nat,
                        mod2 as nat,
                        buf@,
                        old(buf)@,
                    );
                }
                (mod2, N - 16)
            } else {
                proof {
                    lemma_u128_room(v, N as nat, 32);
                }
                // Write digits at buf[N-32..N-16].
                enc_16lsd(buf, N - 32, mod2);
                proof {
                    lemma_u128_two_blocks(
                        v,
                        N as nat,
                        quot_1e16 as nat,
                        mod_1e16 as nat,
                        quot2 as nat,
                        mod2 as nat,
                        buf1,
                        buf@,
                        old(buf)@,
                    );
                }
                // Quot2 has at most 7 decimals remaining after two 1e16 divisions.
                (quot2 as u64, N - 32)
            }
        };

        // Format per four digits from the lookup table.
        while remain > 999
            invariant
                v == self as nat,
                0 < v,
                digits_inv(v, N as nat, offset as nat, remain as nat, buf@, old(buf)@),
            decreases remain,
        {
            let ghost (offset0, remain0, buf0) = (offset as nat, remain as nat, buf@);
            proof {
                lemma_pow10_values();
                lemma_digits_room(v, N as nat, offset0, remain0, buf0, old(buf)@, 4);
            }
            offset -= 4;

            // pull two pairs
            let quad = remain % 1_00_00;
            remain /= 1_00_00;
            let (pair1, pair2) = divmod100(quad as u32);
            write_unchecked(buf, offset + 0, *get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 0));
            write_unchecked(buf, offset + 1, *get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 1));
            write_unchecked(buf, offset + 2, *get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 0));
            write_unchecked(buf, offset + 3, *get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 1));
            proof {
                lemma_chunk_4(remain0, pair1 as int, pair2 as int);
                lemma_wrote(buf0, buf@, offset as int, dec_pad(remain0, 4));
                lemma_digits_step(v, N as nat, offset0, remain0, 4, 10000, buf0, buf@, old(buf)@);
            }
        }

        // Format per two digits from the lookup table.
        if remain > 9 {
            let ghost (offset0, remain0, buf0) = (offset as nat, remain as nat, buf@);
            proof {
                lemma_pow10_values();
                lemma_digits_room(v, N as nat, offset0, remain0, buf0, old(buf)@, 2);
            }
            offset -= 2;

            let (last, pair) = divmod100(remain as u32);
            remain = last as u64;
            write_unchecked(buf, offset + 0, *get_unchecked(&DECIMAL_PAIRS.0, pair as usize * 2 + 0));
            write_unchecked(buf, offset + 1, *get_unchecked(&DECIMAL_PAIRS.0, pair as usize * 2 + 1));
            proof {
                lemma_chunk_2(remain0, pair as int);
                lemma_wrote(buf0, buf@, offset as int, dec_pad(remain0, 2));
                lemma_digits_step(v, N as nat, offset0, remain0, 2, 100, buf0, buf@, old(buf)@);
            }
        }

        // Format the last remaining digit, if any.
        let ghost (offset0, remain0, buf0) = (offset as nat, remain as nat, buf@);
        if remain != 0 {
            proof {
                lemma_pow10_values();
                lemma_digits_room(v, N as nat, offset0, remain0, buf0, old(buf)@, 1);
            }
            offset -= 1;

            // Either the compiler sees that remain < 10, or it prevents
            // a boundary check up next.
            let last = remain as u8 & 15;
            proof {
                lemma_and_15(remain as u8);
            }
            write_unchecked(buf, offset, 48 + last); // b'0' + last
            // not used: remain = 0;
            proof {
                lemma_chunk_1(remain0);
                lemma_wrote(buf0, buf@, offset as int, dec_pad(remain0, 1));
                lemma_digits_step(v, N as nat, offset0, remain0, 1, 10, buf0, buf@, old(buf)@);
            }
        }
        proof {
            lemma_digits_done(v, N as nat, offset as nat, buf@, old(buf)@);
        }
        offset
    }
}

/// `u128::fmt` writes a 16-digit block at `N - j` only when `v >= 10^j`, so there is room.
proof fn lemma_u128_room(v: nat, n: nat, j: nat)
    requires
        v < pow10(n),
        j == 16 || j == 32,
        j == 16 ==> v / 1_0000_0000_0000_0000 != 0,
        j == 32 ==> (v / 1_0000_0000_0000_0000) / 1_0000_0000_0000_0000 != 0,
    ensures
        j < n,
{
    lemma_pow10_16_32();
    if j == 32 {
        lemma_div_pow10_step(v, 16, 16);
    }
    lemma_pow10_lt_inv(j, n);
}

/// The state of `u128::fmt` when `v < 10^16`: nothing written yet.
proof fn lemma_u128_no_block(v: nat, n: nat, r1: nat, buf: Seq<MaybeUninit<u8>>)
    requires
        v < pow10(n),
        buf.len() == n,
        v / 1_0000_0000_0000_0000 == 0,
        r1 == v % 1_0000_0000_0000_0000,
    ensures
        digits_inv(v, n, n, r1, buf, buf),
{
    reveal(digits_inv);
    reveal(holds);
    reveal(unchanged_outside);
    lemma_pow10_16_32();
    vstd::arithmetic::div_mod::lemma_small_mod(v, pow10(16));
    assert(pow10(0) == 1);
    assert(v / pow10(0) == v);
    assert(dec_pad(v, 0) =~= Seq::<u8>::empty());
}

/// The state of `u128::fmt` once it has written the 16 low digits of `v`, when fewer than 16
/// digits are left above them.
proof fn lemma_u128_one_block(
    v: nat,
    n: nat,
    q1: nat,
    r1: nat,
    r2: nat,
    buf: Seq<MaybeUninit<u8>>,
    old_buf: Seq<MaybeUninit<u8>>,
)
    requires
        v < pow10(n),
        buf.len() == n,
        16 < n,
        q1 == v / 1_0000_0000_0000_0000,
        r1 == v % 1_0000_0000_0000_0000,
        q1 != 0,
        q1 / 1_0000_0000_0000_0000 == 0,
        r2 == q1 % 1_0000_0000_0000_0000,
        holds(buf, n - 16, dec_pad(r1, 16)),
        unchanged_outside(buf, old_buf, n - 16, n as int),
    ensures
        digits_inv(v, n, (n - 16) as nat, r2, buf, old_buf),
{
    reveal(digits_inv);
    reveal(holds);
    reveal(unchanged_outside);
    lemma_pow10_16_32();
    lemma_dec_pad_mod(v, 16);
    vstd::arithmetic::div_mod::lemma_small_mod(q1, pow10(16));
    lemma_pow10_le(15, 16);
    assert((n - (n - 16)) as nat == 16);
    assert((16 - 1) as nat == 15);
}

/// The state of `u128::fmt` once it has written the 32 low digits of `v`.
proof fn lemma_u128_two_blocks(
    v: nat,
    n: nat,
    q1: nat,
    r1: nat,
    q2: nat,
    r2: nat,
    buf1: Seq<MaybeUninit<u8>>,
    buf2: Seq<MaybeUninit<u8>>,
    old_buf: Seq<MaybeUninit<u8>>,
)
    requires
        v < pow10(n),
        v < u128_ext::b128(),
        buf2.len() == n,
        32 < n,
        q1 == v / 1_0000_0000_0000_0000,
        r1 == v % 1_0000_0000_0000_0000,
        q2 == q1 / 1_0000_0000_0000_0000,
        r2 == q1 % 1_0000_0000_0000_0000,
        q2 != 0,
        holds(buf1, n - 16, dec_pad(r1, 16)),
        unchanged_outside(buf1, old_buf, n - 16, n as int),
        holds(buf2, n - 32, dec_pad(r2, 16)),
        unchanged_outside(buf2, buf1, n - 32, n - 16),
    ensures
        digits_inv(v, n, (n - 32) as nat, q2, buf2, old_buf),
        q2 < 0x1_0000_0000_0000_0000,
{
    reveal(digits_inv);
    reveal(holds);
    reveal(unchanged_outside);
    lemma_pow10_16_32();
    lemma_dec_pad_len(r1, 16);
    lemma_dec_pad_len(r2, 16);
    lemma_holds_frame(buf1, buf2, n - 16, dec_pad(r1, 16), n - 32, n - 16);
    lemma_holds_prepend(buf1, buf2, n - 32, dec_pad(r2, 16), dec_pad(r1, 16));
    lemma_dec_pad_split(v, 16, 16);
    lemma_dec_pad_mod(v, 16);
    lemma_dec_pad_mod(q1, 16);
    lemma_div_pow10_step(v, 16, 16);
    lemma_pow10_le(31, 32);
    assert((n - (n - 32)) as nat == 32);
    assert((32 - 1) as nat == 31);
    assert(16 + 16 == 32);
    assert(dec_pad(v, 32) == dec_pad(r2, 16) + dec_pad(r1, 16));
    assert(q2 == v / 1_0000_0000_0000_0000_0000_0000_0000_0000);
}

proof fn lemma_pow10_16_32()
    ensures
        pow10(16) == 1_0000_0000_0000_0000,
        pow10(32) == 1_0000_0000_0000_0000_0000_0000_0000_0000,
{
    reveal_with_fuel(pow10, 33);
}

// Encodes the 16 least-significant decimals of n into `buf[offset..offset + 16]`.
// (Upstream takes the offset as a const generic `OFFSET`, which cannot depend on the length
// of `buf` now that `Unsigned::fmt` is generic over it.)
#[cfg_attr(feature = "no-panic", no_panic)]
fn enc_16lsd(buf: &mut [MaybeUninit<u8>], offset: usize, n: u64)
    requires
        offset + 16 <= old(buf)@.len(),
        n < 1_0000_0000_0000_0000,
    ensures
        final(buf)@.len() == old(buf)@.len(),
        holds(final(buf)@, offset as int, dec_pad(n as nat, 16)),
        unchanged_outside(final(buf)@, old(buf)@, offset as int, offset + 16),
        // Human spec
        final(buf).len() == old(buf).len(),
{
    // Consume the least-significant decimals from a working copy.
    let mut remain = n;
    proof {
        // The length of a slice is a `usize`.
        assert(buf.len() == buf@.len());
        lemma_pow10_values();
        assert(n as nat / pow10(0) == n as nat);
        assert(dec_pad(n as nat, 0) =~= Seq::<u8>::empty());
        lemma_holds_empty(buf@, offset + 16);
        lemma_unchanged_refl(buf@, offset + 16);
    }

    // Format per four digits from the lookup table.
    // (Upstream: `for quad_index in (1..4).rev()`; Verus does not support `Rev`.)
    let mut quad_index = 4;
    while quad_index > 1
        invariant
            1 <= quad_index <= 4,
            offset + 16 <= buf@.len() <= usize::MAX,
            buf@.len() == old(buf)@.len(),
            n < 1_0000_0000_0000_0000,
            remain as nat == n as nat / pow10((16 - 4 * quad_index) as nat),
            holds(buf@, offset + 4 * quad_index, dec_pad(n as nat, (16 - 4 * quad_index) as nat)),
            unchanged_outside(buf@, old(buf)@, offset + 4 * quad_index, offset + 16),
        decreases quad_index,
    {
        quad_index -= 1;
        let ghost (remain0, buf0) = (remain as nat, buf@);
        // pull two pairs
        let quad = remain % 1_00_00;
        remain /= 1_00_00;
        let (pair1, pair2) = divmod100(quad as u32);
        buf[quad_index * 4 + offset + 0] = MaybeUninit::new(*get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 0));
        buf[quad_index * 4 + offset + 1] = MaybeUninit::new(*get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 1));
        buf[quad_index * 4 + offset + 2] = MaybeUninit::new(*get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 0));
        buf[quad_index * 4 + offset + 3] = MaybeUninit::new(*get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 1));
        proof {
            let k = (16 - 4 * (quad_index + 1)) as nat;
            let start = offset + 4 * quad_index;
            lemma_chunk_4(remain0, pair1 as int, pair2 as int);
            lemma_pow10_values();
            lemma_wrote(buf0, buf@, start, dec_pad(remain0, 4));
            lemma_dec_pad_len(remain0, 4);
            lemma_holds_prepend(buf0, buf@, start, dec_pad(remain0, 4), dec_pad(n as nat, k));
            lemma_unchanged_extend(old(buf)@, buf0, buf@, start, start + 4, offset + 16);
            lemma_dec_pad_split(n as nat, 4, k);
            lemma_dec_pad_mod(n as nat / pow10(k), 4);
            lemma_div_pow10_step(n as nat, k, 4);
            assert((16 - 4 * quad_index) as nat == 4 + k);
            assert(k + 4 == 4 + k);
        }
    }

    // final two pairs
    let ghost (remain0, buf0) = (remain as nat, buf@);
    proof {
        lemma_pow10_le(12, 16);
        lemma_div_pow10_step(n as nat, 12, 4);
        lemma_pow10_values();
        lemma_pow10_16_32();
        lemma_pow10_add(12, 4);
        vstd::arithmetic::div_mod::lemma_multiply_divide_lt(n as int, pow10(12) as int, 10000);
    }
    let (pair1, pair2) = divmod100(remain as u32);
    buf[offset + 0] = MaybeUninit::new(*get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 0));
    buf[offset + 1] = MaybeUninit::new(*get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 1));
    buf[offset + 2] = MaybeUninit::new(*get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 0));
    buf[offset + 3] = MaybeUninit::new(*get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 1));
    proof {
        lemma_chunk_4(remain0, pair1 as int, pair2 as int);
        lemma_wrote(buf0, buf@, offset as int, dec_pad(remain0, 4));
        lemma_dec_pad_len(remain0, 4);
        lemma_holds_prepend(buf0, buf@, offset as int, dec_pad(remain0, 4), dec_pad(n as nat, 12));
        lemma_unchanged_extend(old(buf)@, buf0, buf@, offset as int, offset + 4, offset + 16);
        lemma_dec_pad_split(n as nat, 4, 12);
    }
}

/// 10^16, the divisor of `div_rem_1e16`.
#[verifier::inline]
spec fn d16() -> int {
    1_0000_0000_0000_0000
}

/// `M_HIGH` of `div_rem_1e16`: the smallest integer above 2^179 / 10^16.
#[verifier::inline]
spec fn m_high() -> int {
    76624777043294442917917351357515459181
}

/// 2^179 = 2^(128 + SH_POST).
#[verifier::inline]
spec fn b179() -> int {
    u128_ext::b128() * 0x8_0000_0000_0000
}

/// For every 128-bit `n`, `n * M_HIGH / 2^179 == n / 10^16`: the multiplier of
/// `div_rem_1e16` is exact on the whole range. With `q = n / 10^16` and `r = n % 10^16`,
/// `n * M_HIGH = q * 2^179 + (q * e + r * M_HIGH)` where `e = M_HIGH * 10^16 - 2^179`, and the
/// second term is below 2^179 because `(q + 1) * e < M_HIGH`.
proof fn lemma_div_1e16_multiplier(n: int)
    requires
        0 <= n < u128_ext::b128(),
    ensures
        (n * m_high()) / b179() == n / d16(),
{
    let q = n / d16();
    let r = n % d16();
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n, d16());
    assert(m_high() * d16() == b179() + 630438908198912);
    assert(0 <= q <= 34028236692093846346337);
    assert(0 <= r < d16());
    assert(n * m_high() == q * b179() + (q * 630438908198912 + r * m_high()));
    assert(0 <= q * 630438908198912 + r * m_high() < b179());
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        n * m_high(),
        b179(),
        q,
        q * 630438908198912 + r * m_high(),
    );
}

// Euclidean division plus remainder with constant 1E16 basically consumes 16
// decimals from n.
//
// The integer division algorithm is based on the following paper:
//
//   T. Granlund and P. Montgomery, “Division by Invariant Integers Using Multiplication”
//   in Proc. of the SIGPLAN94 Conference on Programming Language Design and
//   Implementation, 1994, pp. 61–72
//
#[cfg_attr(feature = "no-panic", no_panic)]
fn div_rem_1e16(n: u128) -> (r: (u128, u64))
    ensures
        r.0 == n / 1_0000_0000_0000_0000,
        r.1 == n % 1_0000_0000_0000_0000,
        // Human spec
        r.1 < 10_000_000_000_000_000u64,
        (r.0 as nat) * 10_000_000_000_000_000nat + (r.1 as nat) == (n as nat),
{
    const D: u128 = 1_0000_0000_0000_0000;
    // The check inlines well with the caller flow.
    if n < D {
        return (0, n as u64);
    }

    // These constant values are computed with the CHOOSE_MULTIPLIER procedure
    // from the Granlund & Montgomery paper, using N=128, prec=128 and d=1E16.
    const M_HIGH: u128 = 76624777043294442917917351357515459181;
    const SH_POST: u8 = 51;

    proof {
        assert forall|v: u128| #[trigger] (v >> SH_POST) == v / 0x8_0000_0000_0000u128 by {
            assert(v >> 51u8 == v / 0x8_0000_0000_0000u128) by (bit_vector);
        }
    }
    // n.widening_mul(M_HIGH).1 >> SH_POST
    let quot = u128_ext::mulhi(n, M_HIGH) >> SH_POST;
    proof {
        vstd::arithmetic::div_mod::lemma_div_denominator(
            n as int * m_high(),
            u128_ext::b128(),
            0x8_0000_0000_0000,
        );
        lemma_div_1e16_multiplier(n as int);
    }
    let rem = n - quot * D;
    (quot, rem as u64)
}

/// The signed counterpart of `Unsigned`. Upstream formats signed integers inline in
/// `Sealed::write`; that method is trusted here (it builds the `&str`), so the formatting
/// moved into this verified trait, which `write` calls.
trait Signed: Integer {
    /// The value of `self`.
    spec fn spec_val(self) -> int;

    /// Writes the decimal representation of `self`, with a leading `'-'` if negative, at the
    /// end of `buf` and returns the index of its first byte.
    fn fmt<const N: usize>(self, buf: &mut [MaybeUninit<u8>; N]) -> (offset: usize)
        requires
            dec_int(self.spec_val()).len() <= N,
        ensures
            offset + dec_int(self.spec_val()).len() == N,
            holds(final(buf)@, offset as int, dec_int(self.spec_val())),
            unchanged_outside(final(buf)@, old(buf)@, offset as int, N as int),
    ;
}

macro_rules! impl_Signed {
    ($Signed:ident, $Unsigned:ident) => {
        verus! {
        impl Signed for $Signed {
            spec fn spec_val(self) -> int {
                self as int
            }

            #[inline]
            #[cfg_attr(feature = "no-panic", no_panic)]
            fn fmt<const N: usize>(self, buf: &mut [MaybeUninit<u8>; N]) -> (offset: usize) {
                // `self.unsigned_abs()`, which vstd does not specify, with in-range casts only:
                // `-(self + 1)` cannot overflow, and neither can adding the 1 back.
                let unsigned_abs = if self < 0 {
                    (-(self + 1)) as $Unsigned + 1
                } else {
                    self as $Unsigned
                };
                // Upstream formats into `buf[Self::MAX_STR_LEN - $Unsigned::MAX_STR_LEN..]`,
                // which ends where `buf` ends, so the digits land in the same place.
                let mut offset = Unsigned::fmt(unsigned_abs, buf);
                if self < 0 {
                    let ghost buf0 = buf@;
                    offset -= 1;
                    write_unchecked(buf, offset, 45); // b'-'
                    proof {
                        lemma_wrote(buf0, buf@, offset as int, seq![45u8]);
                        lemma_holds_prepend(
                            buf0,
                            buf@,
                            offset as int,
                            seq![45u8],
                            dec(unsigned_abs as nat),
                        );
                        lemma_unchanged_extend(old(buf)@, buf0, buf@, offset as int, offset + 1, N as int);
                    }
                }
                offset
            }
        }
        }
    };
}

impl_Signed!(i8, u8);
impl_Signed!(i16, u16);
impl_Signed!(i32, u32);
impl_Signed!(i64, u64);
impl_Signed!(i128, u128);

// ===== MAX_STR_LEN =====
//
// The `write` methods pass `buf: &mut Self::Buffer`, an array of length `Self::MAX_STR_LEN`,
// to `Unsigned::fmt` and `Signed::fmt`. For each type, these lemmas show that this length is the
// length of the longest decimal representation of the type, so the precondition of `fmt` holds
// for every value, and `MAX_STR_LEN` is exactly what its documentation says. (`usize` and
// `isize` use the buffer of the fixed-size type they convert to.)

macro_rules! lemmas_max_str_len {
    ($unsigned_lemma:ident, $Unsigned:ident, $unsigned_len:literal, $signed_lemma:ident, $Signed:ident, $signed_len:literal) => {
        verus! {
        proof fn $unsigned_lemma()
            ensures
                <$Unsigned as Integer>::MAX_STR_LEN == $unsigned_len,
                forall|buf: <$Unsigned as private::Sealed>::Buffer| #[trigger] buf@.len() == $unsigned_len,
                $unsigned_len == dec($Unsigned::MAX as nat).len(),
                forall|x: $Unsigned| #[trigger] dec(x as nat).len() <= $unsigned_len,
        {
            assert(pow10(($unsigned_len - 1) as nat) <= $Unsigned::MAX as nat) by (compute_only);
            assert(($Unsigned::MAX as nat) < pow10($unsigned_len)) by (compute_only);
            lemma_num_digits($Unsigned::MAX as nat, $unsigned_len);
            lemma_dec_len($Unsigned::MAX as nat);
            assert forall|x: $Unsigned| #[trigger] dec(x as nat).len() <= $unsigned_len by {
                lemma_dec_len(x as nat);
                lemma_num_digits_le(x as nat, $unsigned_len);
            }
        }

        proof fn $signed_lemma()
            ensures
                <$Signed as Integer>::MAX_STR_LEN == $signed_len,
                forall|buf: <$Signed as private::Sealed>::Buffer| #[trigger] buf@.len() == $signed_len,
                $signed_len == dec_int($Signed::MIN as int).len(),
                forall|x: $Signed| #[trigger] dec_int(x as int).len() <= $signed_len,
        {
            let m = -($Signed::MIN as int);
            assert(pow10(($signed_len - 2) as nat) <= -($Signed::MIN as int)) by (compute_only);
            assert(-($Signed::MIN as int) < pow10(($signed_len - 1) as nat)) by (compute_only);
            lemma_num_digits(m as nat, ($signed_len - 1) as nat);
            lemma_dec_len(m as nat);
            assert forall|x: $Signed| #[trigger] dec_int(x as int).len() <= $signed_len by {
                if x < 0 {
                    lemma_dec_len((-x) as nat);
                    lemma_num_digits_le((-x) as nat, ($signed_len - 1) as nat);
                } else {
                    lemma_dec_len(x as nat);
                    lemma_num_digits_le(x as nat, ($signed_len - 1) as nat);
                }
            }
        }
        }
    };
}

lemmas_max_str_len!(lemma_max_str_len_u8, u8, 3, lemma_max_str_len_i8, i8, 4);
lemmas_max_str_len!(lemma_max_str_len_u16, u16, 5, lemma_max_str_len_i16, i16, 6);
lemmas_max_str_len!(lemma_max_str_len_u32, u32, 10, lemma_max_str_len_i32, i32, 11);
lemmas_max_str_len!(lemma_max_str_len_u64, u64, 20, lemma_max_str_len_i64, i64, 20);
lemmas_max_str_len!(lemma_max_str_len_u128, u128, 39, lemma_max_str_len_i128, i128, 40);

} // verus!
