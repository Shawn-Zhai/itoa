//! The developer-written specification (`verus_human_written_spec/itoa/src/lib.rs`), transcribed.
//!
//! Ghost code only: `verus!` erases all of it from normal builds. The spec functions below are
//! the developer's, unchanged, with one exception: `initialized_ascii_suffix` was `uninterp`, so
//! no caller could ever establish the precondition of `slice_buffer_to_str`. Here it has the
//! meaning that its comment and the `# Safety` section of `slice_buffer_to_str` give it.
//!
//! The developer's contracts are stated in `lib.rs` and `u128_ext.rs`, on the functions they
//! belong to, next to Claude's contracts; each such clause is marked `// Human spec`.
//! `spec_equiv.rs` relates these definitions to Claude's (`spec.rs`).

#![allow(unused_imports)]
use core::mem::MaybeUninit;
use vstd::prelude::*;

verus! {

// maps 0-9 to '0'-'9'
pub open spec fn decimal_digit(d: nat) -> char
    recommends
        d < 10,
{
    if d == 0 {
        '0'
    } else if d == 1 {
        '1'
    } else if d == 2 {
        '2'
    } else if d == 3 {
        '3'
    } else if d == 4 {
        '4'
    } else if d == 5 {
        '5'
    } else if d == 6 {
        '6'
    } else if d == 7 {
        '7'
    } else if d == 8 {
        '8'
    } else {
        '9'
    }
}

// converts a non-negative integer into a sequence of char
pub open spec fn decimal_unsigned(n: nat) -> Seq<char>
    decreases n,
{
    if n < 10 {
        Seq::empty().push(decimal_digit(n))
    } else {
        decimal_unsigned(n / 10).push(decimal_digit(n % 10))
    }
}

// converts a signed integer into a sequence of char
pub open spec fn decimal_signed(n: int) -> Seq<char> {
    if n < 0 {
        seq!['-'].add(decimal_unsigned((-n) as nat))
    } else {
        decimal_unsigned(n as nat)
    }
}

// buffer content starting from `offset` index must be initialized and ascii characters
//
// (The developer declared this `uninterp`. Defined here: each element from `offset` on holds an
// initialized byte below 128.)
pub open spec fn initialized_ascii_suffix(buf: &[MaybeUninit<u8>], offset: usize) -> bool {
    forall|i: int|
        offset <= i < buf@.len() ==> {
            &&& (#[trigger] buf@[i]).mem_contents().is_init()
            &&& buf@[i].mem_contents().value() < 128
        }
}

// checks whether a char sequence represents a valid signed or unsigned integer string
pub open spec fn is_decimal_text(s: Seq<char>) -> bool {
    if s.len() == 0 {
        false
    } else {
        (s[0] != '-' || s.len() > 1) && (forall|k: int|
            0 <= k < s.len() ==> (s[k] >= '0' && s[k] <= '9') || (k == 0 && s[k] == '-'))
    }
}

} // verus!
