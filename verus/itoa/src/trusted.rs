//! TRUSTED code: the parts of itoa that Verus does not verify.
//!
//! Verus skips this module (`#[cfg_attr(verus_keep_ghost, verifier::external)]` on `mod trusted`
//! in `lib.rs`); normal builds compile it like any other module. The items are upstream's code,
//! moved here unchanged, except the `write` method for the signed types (T2), whose formatting
//! logic moved into the verified `Signed::fmt`.
//!
//! | id | items | why trusted |
//! |----|-------|-------------|
//! | T1 | `Buffer::format` | reinterprets the `[MaybeUninit<u8>; 40]` buffer as `I::Buffer` through a raw pointer cast; Verus cannot reason about a cast between array types |
//! | T2 | `impl_Integer!`, `impl_Integer_size!`: the `Integer` and `Sealed` impls (`MAX_STR_LEN`, `Buffer`, `write`) | `write` calls `slice_buffer_to_str` (T3); `MAX_STR_LEN` uses `ilog10`, which vstd does not specify (its value is checked by Verus through the `Buffer` types, see the `lemma_max_str_len_*` lemmas in `lib.rs`) |
//! | T3 | `slice_buffer_to_str` | reinterprets `&[MaybeUninit<u8>]` as `&[u8]` through a raw pointer cast, then calls `str::from_utf8_unchecked` |
//!
//! Obligations, checked by inspection (see `VERIFICATION.md`, "Trusted base"):
//!
//! - T1: `I::Buffer` is `[MaybeUninit<u8>; I::MAX_STR_LEN]` and `I::MAX_STR_LEN <= 40`, so the
//!   cast stays within `self.bytes`; `string.len() <= I::MAX_STR_LEN` holds because `write`
//!   returns `buf[offset..]` of a `buf` of that length.
//! - T2: each `write` passes `buf: &mut Self::Buffer` to the verified `Unsigned::fmt` or
//!   `Signed::fmt`, whose precondition holds for every value by the verified
//!   `lemma_max_str_len_*` lemmas; their postcondition says that `buf[offset..]` is initialized
//!   with the decimal representation of `self`, which is ASCII, as T3 requires.
//! - T3: called only from T2, with that guarantee.

use crate::{private, Buffer, Integer, Signed, Unsigned};
use core::hint;
use core::mem::MaybeUninit;
use core::str;
#[cfg(feature = "no-panic")]
use no_panic::no_panic;

// ===== T1 =====

impl Buffer {
    /// Print an integer into this buffer and return a reference to its string
    /// representation within the buffer.
    #[cfg_attr(feature = "no-panic", no_panic)]
    pub fn format<I: Integer>(&mut self, i: I) -> &str {
        let buf_ptr = self.bytes.as_mut_ptr().cast::<I::Buffer>();
        let string = i.write(unsafe { &mut *buf_ptr });
        if string.len() > I::MAX_STR_LEN {
            unsafe { hint::unreachable_unchecked() };
        }
        string
    }
}

// ===== T2 =====

macro_rules! impl_Integer {
    ($Signed:ident, $Unsigned:ident) => {
        const _: () = {
            assert!($Signed::MIN < 0, "need signed");
            assert!($Unsigned::MIN == 0, "need unsigned");
            assert!($Signed::BITS == $Unsigned::BITS, "need counterparts");
        };

        impl Integer for $Unsigned {
            const MAX_STR_LEN: usize = $Unsigned::MAX.ilog10() as usize + 1;
        }

        impl private::Sealed for $Unsigned {
            type Buffer = [MaybeUninit<u8>; Self::MAX_STR_LEN];

            #[inline]
            #[cfg_attr(feature = "no-panic", no_panic)]
            fn write(self, buf: &mut Self::Buffer) -> &str {
                let offset = Unsigned::fmt(self, buf);
                // SAFETY: Starting from `offset`, all elements of the slice have been set.
                unsafe { slice_buffer_to_str(buf, offset) }
            }
        }

        impl Integer for $Signed {
            const MAX_STR_LEN: usize = $Signed::MAX.ilog10() as usize + 2;
        }

        impl private::Sealed for $Signed {
            type Buffer = [MaybeUninit<u8>; Self::MAX_STR_LEN];

            #[inline]
            #[cfg_attr(feature = "no-panic", no_panic)]
            fn write(self, buf: &mut Self::Buffer) -> &str {
                // The formatting (upstream's body of this method, up to here) is in the
                // verified `Signed::fmt`.
                let offset = Signed::fmt(self, buf);
                // SAFETY: Starting from `offset`, all elements of the slice have been set.
                unsafe { slice_buffer_to_str(buf, offset) }
            }
        }
    };
}

impl_Integer!(i8, u8);
impl_Integer!(i16, u16);
impl_Integer!(i32, u32);
impl_Integer!(i64, u64);
impl_Integer!(i128, u128);

macro_rules! impl_Integer_size {
    ($t:ty as $primitive:ident #[cfg(target_pointer_width = $width:literal)]) => {
        #[cfg(target_pointer_width = $width)]
        impl Integer for $t {
            const MAX_STR_LEN: usize = <$primitive as Integer>::MAX_STR_LEN;
        }

        #[cfg(target_pointer_width = $width)]
        impl private::Sealed for $t {
            type Buffer = <$primitive as private::Sealed>::Buffer;

            #[inline]
            #[cfg_attr(feature = "no-panic", no_panic)]
            fn write(self, buf: &mut Self::Buffer) -> &str {
                (self as $primitive).write(buf)
            }
        }
    };
}

impl_Integer_size!(isize as i16 #[cfg(target_pointer_width = "16")]);
impl_Integer_size!(usize as u16 #[cfg(target_pointer_width = "16")]);
impl_Integer_size!(isize as i32 #[cfg(target_pointer_width = "32")]);
impl_Integer_size!(usize as u32 #[cfg(target_pointer_width = "32")]);
impl_Integer_size!(isize as i64 #[cfg(target_pointer_width = "64")]);
impl_Integer_size!(usize as u64 #[cfg(target_pointer_width = "64")]);

// ===== T3 =====

/// This function converts a slice of ascii characters into a `&str` starting
/// from `offset`.
///
/// # Safety
///
/// `buf` content starting from `offset` index MUST BE initialized and MUST BE
/// ascii characters.
#[cfg_attr(feature = "no-panic", no_panic)]
unsafe fn slice_buffer_to_str(buf: &[MaybeUninit<u8>], offset: usize) -> &str {
    // SAFETY: `offset` is always included between 0 and `buf`'s length.
    let written = unsafe { buf.get_unchecked(offset..) };
    // SAFETY: (`assume_init_ref`) All buf content since offset is set.
    // SAFETY: (`from_utf8_unchecked`) Writes use ASCII from the lookup table exclusively.
    unsafe { str::from_utf8_unchecked(&*(written as *const [MaybeUninit<u8>] as *const [u8])) }
}
