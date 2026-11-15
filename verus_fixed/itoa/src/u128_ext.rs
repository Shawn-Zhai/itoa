#[cfg(feature = "no-panic")]
use no_panic::no_panic;
use vstd::prelude::*;

verus! {

/// 2^64, as a mathematical integer.
#[verifier::inline]
pub(crate) open spec fn b64() -> int {
    0x1_0000_0000_0000_0000
}

/// 2^128, as a mathematical integer.
#[verifier::inline]
pub(crate) open spec fn b128() -> int {
    b64() * b64()
}

/// `v >> 64` is the high half of `v`.
proof fn lemma_shr_64(v: u128)
    ensures
        v >> 64u128 == v / 0x1_0000_0000_0000_0000u128,
{
    assert(v >> 64u128 == v / 0x1_0000_0000_0000_0000u128) by (bit_vector);
}

/// `v as u64` is the low half of `v`.
proof fn lemma_low_64(v: u128)
    ensures
        (v as u64) as u128 == v % 0x1_0000_0000_0000_0000u128,
{
    assert((v as u64) as u128 == v % 0x1_0000_0000_0000_0000u128) by (bit_vector);
}

/// The product of two 64-bit values fits in 128 bits, with room for one more 64-bit value.
proof fn lemma_mul_64_64(a: int, b: int)
    requires
        0 <= a < b64(),
        0 <= b < b64(),
    ensures
        0 <= a * b,
        a * b + (b64() - 1) < b128(),
{
    assert(0 <= a * b <= (b64() - 1) * (b64() - 1)) by (nonlinear_arith)
        requires
            0 <= a < b64(),
            0 <= b < b64(),
    ;
}

/// The schoolbook multiplication in `mulhi`: the high 128 bits of `x * y` are
/// `xh * yh + high1 + high2`, and they fit in 128 bits.
proof fn lemma_mulhi_algebra(
    x: int,
    y: int,
    xh: int,
    xl: int,
    yh: int,
    yl: int,
    carry: int,
    high1: int,
    m_lo: int,
    high2: int,
)
    requires
        0 <= xh < b64(),
        0 <= xl < b64(),
        0 <= yh < b64(),
        0 <= yl < b64(),
        x == xh * b64() + xl,
        y == yh * b64() + yl,
        carry == (xl * yl) / b64(),
        high1 == (xl * yh + carry) / b64(),
        m_lo == (xl * yh + carry) % b64(),
        high2 == (xh * yl + m_lo) / b64(),
    ensures
        xh * yh + high1 + high2 == (x * y) / b128(),
        (x * y) / b128() < b128(),
{
    // Name the four partial products; from here on the reasoning is linear in them.
    let (p_hh, p_hl, p_lh, p_ll) = (xh * yh, xh * yl, xl * yh, xl * yl);
    let lo0 = p_ll % b64();
    let lo1 = (p_hl + m_lo) % b64();
    assert(x * y == p_hh * b128() + (p_hl + p_lh) * b64() + p_ll) by (nonlinear_arith)
        requires
            x == xh * b64() + xl,
            y == yh * b64() + yl,
            p_hh == xh * yh,
            p_hl == xh * yl,
            p_lh == xl * yh,
            p_ll == xl * yl,
    ;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p_ll, b64());
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p_lh + carry, b64());
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p_hl + m_lo, b64());
    assert(0 <= lo0 < b64());
    assert(0 <= lo1 < b64());
    // x * y == (xh*yh + high1 + high2) * 2^128 + (lo1 * 2^64 + lo0)
    assert(x * y == (p_hh + high1 + high2) * b128() + (lo1 * b64() + lo0));
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        x * y,
        b128(),
        p_hh + high1 + high2,
        lo1 * b64() + lo0,
    );
    assert(x * y <= (b128() - 1) * (b128() - 1)) by (nonlinear_arith)
        requires
            0 <= x < b128(),
            0 <= y < b128(),
    ;
    vstd::arithmetic::div_mod::lemma_multiply_divide_lt(x * y, b128(), b128());
}

/// Multiply unsigned 128 bit integers, return upper 128 bits of the result
#[inline]
#[cfg_attr(feature = "no-panic", no_panic)]
pub(crate) fn mulhi(x: u128, y: u128) -> (hi: u128)
    ensures
        hi as int == (x as int * y as int) / b128(),
        // Human spec
        hi as nat == (x as nat) * (y as nat) / 340282366920938463463374607431768211456nat,
{
    let x_lo = x as u64;
    let x_hi = (x >> 64) as u64;
    let y_lo = y as u64;
    let y_hi = (y >> 64) as u64;
    let ghost (xl, xh, yl, yh) = (x_lo as int, x_hi as int, y_lo as int, y_hi as int);
    proof {
        lemma_low_64(x);
        lemma_low_64(y);
        lemma_shr_64(x);
        lemma_shr_64(y);
        assert(x as int == xh * b64() + xl);
        assert(y as int == yh * b64() + yl);
        lemma_mul_64_64(xl, yl);
        lemma_mul_64_64(xl, yh);
        lemma_mul_64_64(xh, yl);
        lemma_mul_64_64(xh, yh);
    }

    // handle possibility of overflow
    let carry = (u128::from(x_lo) * u128::from(y_lo)) >> 64;
    proof {
        lemma_shr_64((x_lo as u128 * y_lo as u128) as u128);
    }
    let m = u128::from(x_lo) * u128::from(y_hi) + carry;
    let high1 = m >> 64;

    let m_lo = m as u64;
    proof {
        lemma_shr_64(m);
        lemma_low_64(m);
    }
    let high2 = (u128::from(x_hi) * u128::from(y_lo) + u128::from(m_lo)) >> 64;
    proof {
        lemma_shr_64((x_hi as u128 * y_lo as u128 + m_lo as u128) as u128);
        lemma_mulhi_algebra(
            x as int,
            y as int,
            xh,
            xl,
            yh,
            yl,
            carry as int,
            high1 as int,
            m_lo as int,
            high2 as int,
        );
    }

    u128::from(x_hi) * u128::from(y_hi) + high1 + high2
}

} // verus!
