//! Verified stand-ins for `<[T]>::get_unchecked` and `<[T]>::get_unchecked_mut(..).write(..)`,
//! which vstd does not specify.
//!
//! Each stand-in takes the safety condition of the unchecked accessor (`index` in bounds) as its
//! precondition, which Verus proves at every call site. The body indexes with a bounds check, but
//! behind a branch to `hint::unreachable_unchecked` that Verus proves dead (vstd specifies it with
//! `requires false`). The optimizer therefore drops the bounds check, as with the unchecked
//! accessor, and the `no-panic` feature still links.

use core::hint;
use core::mem::MaybeUninit;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::raw_ptr::MemContents;

verus! {

/// `array.get_unchecked(index)`, with its safety condition `index < N` proved by Verus.
#[inline(always)]
pub(crate) fn get_unchecked<T, const N: usize>(array: &[T; N], index: usize) -> (element: &T)
    requires
        index < N,
    ensures
        *element == array@[index as int],
{
    if index >= N {
        // SAFETY: dead code; Verus proves `index < N` at every call site.
        unsafe { hint::unreachable_unchecked() };
    }
    &array[index]
}

/// `array.get_unchecked_mut(index).write(value)`, with its safety condition `index < N` proved
/// by Verus. (`MaybeUninit::write` is `*self = MaybeUninit::new(val)`, plus a returned reference
/// that the callers in itoa discard.)
#[inline(always)]
pub(crate) fn write_unchecked<const N: usize>(
    array: &mut [MaybeUninit<u8>; N],
    index: usize,
    value: u8,
)
    requires
        index < N,
    ensures
        final(array)@[index as int].mem_contents() == MemContents::Init(value),
        final(array)@ == old(array)@.update(index as int, final(array)@[index as int]),
{
    if index >= N {
        // SAFETY: dead code; Verus proves `index < N` at every call site.
        unsafe { hint::unreachable_unchecked() };
    }
    array[index] = MaybeUninit::new(value);
}

} // verus!
