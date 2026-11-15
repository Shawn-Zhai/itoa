//! Verified clients of `Buffer::format`. They show that its contract determines the output:
//! Verus proves the exact strings of upstream's doc examples, and the extreme values of a type.
//! Only compiled under Verus (`#[cfg(verus_keep_ghost)]` on the module).

use crate::human_spec::*;
use crate::Buffer;
use vstd::prelude::*;

verus! {

/// The crate-level doc example: `buffer.format(128u64) == "128"`.
fn example_doc_128() {
    let mut buffer = Buffer::new();
    let printed = buffer.format(128u64);
    reveal_with_fuel(decimal_unsigned, 3);
    assert(printed@ == seq!['1', '2', '8']);
}

/// The doc example of `Buffer`: `buffer.format(1234) == "1234"` (an `i32`).
fn example_doc_1234() {
    let mut buffer = Buffer::new();
    let printed = buffer.format(1234i32);
    reveal_with_fuel(decimal_unsigned, 4);
    assert(printed@ == seq!['1', '2', '3', '4']);
}

/// Negative numbers get a `'-'`; zero is `"0"`.
fn example_sign_and_zero() {
    let mut buffer = Buffer::new();
    let printed = buffer.format(-128i8);
    reveal_with_fuel(decimal_unsigned, 3);
    assert(printed@ == seq!['-', '1', '2', '8']);

    let printed = buffer.format(0u128);
    assert(printed@ == seq!['0']);
}

/// The longest output of each type has exactly `MAX_STR_LEN` chars.
fn example_max_len() {
    let mut buffer = Buffer::new();
    let printed = buffer.format(i8::MIN);
    reveal_with_fuel(decimal_unsigned, 3);
    assert(printed@.len() == <i8 as crate::Integer>::MAX_STR_LEN);

    let printed = buffer.format(u16::MAX);
    reveal_with_fuel(decimal_unsigned, 5);
    assert(printed@.len() == <u16 as crate::Integer>::MAX_STR_LEN);
}

} // verus!
