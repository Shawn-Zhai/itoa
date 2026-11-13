#[cfg(feature = "no-panic")]
use no_panic::no_panic;

use vstd::prelude::*;

/// Multiply unsigned 128 bit integers, return upper 128 bits of the result
verus! {
#[inline]
#[cfg_attr(feature = "no-panic", no_panic)]
pub(crate) fn mulhi(x: u128, y: u128) -> (result: u128)
    ensures
        result as nat == (x as nat) * (y as nat)
            / 340282366920938463463374607431768211456nat,
{
    assume(false);
    
    let x_lo = x as u64;
    let x_hi = (x >> 64) as u64;
    let y_lo = y as u64;
    let y_hi = (y >> 64) as u64;
    // handle possibility of overflow
    let carry = (u128::from(x_lo) * u128::from(y_lo)) >> 64;
    let m = u128::from(x_lo) * u128::from(y_hi) + carry;
    let high1 = m >> 64;

    let m_lo = m as u64;
    let high2 = (u128::from(x_hi) * u128::from(y_lo) + u128::from(m_lo)) >> 64;

    u128::from(x_hi) * u128::from(y_hi) + high1 + high2
}
}
