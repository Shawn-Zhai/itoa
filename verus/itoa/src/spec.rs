//! Specification of decimal formatting, and the arithmetic lemmas the proofs use.
//!
//! Ghost code only: `verus!` erases all of it from normal builds. Nothing in this file is
//! trusted; every lemma is proved.

#![allow(unused_imports)]
use core::mem::MaybeUninit;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{
    lemma_div_by_self, lemma_div_denominator, lemma_div_is_ordered, lemma_fundamental_div_mod,
    lemma_fundamental_div_mod_converse, lemma_mod_breakdown, lemma_mod_mod, lemma_mod_twice,
    lemma_multiply_divide_lt, lemma_small_div_converse, lemma_small_mod,
};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::mul::lemma_mul_inequality;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::raw_ptr::MemContents;

verus! {

// ===== Definitions =====

/// 10 to the power `n`.
pub open spec fn pow10(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        10 * pow10((n - 1) as nat)
    }
}

/// The ASCII code of the decimal digit `d`, that is `b'0' + d`.
pub open spec fn digit(d: nat) -> u8 {
    (48 + d) as u8
}

/// The `k` least-significant decimal digits of `n` in ASCII, zero-padded to `k` digits, most
/// significant first.
pub open spec fn dec_pad(n: nat, k: nat) -> Seq<u8>
    decreases k,
{
    if k == 0 {
        Seq::empty()
    } else {
        dec_pad(n / 10, (k - 1) as nat).push(digit(n % 10))
    }
}

/// The number of decimal digits of `n` (one for zero).
pub open spec fn num_digits(n: nat) -> nat
    decreases n,
{
    if n < 10 {
        1
    } else {
        1 + num_digits(n / 10)
    }
}

/// The decimal representation of `n` in ASCII, without leading zeros: `"0"` for zero.
pub open spec fn dec(n: nat) -> Seq<u8> {
    dec_pad(n, num_digits(n))
}

/// The decimal representation of `n` in ASCII, with a leading `'-'` (45) when `n` is negative.
pub open spec fn dec_int(n: int) -> Seq<u8> {
    if n < 0 {
        seq![45u8] + dec((-n) as nat)
    } else {
        dec(n as nat)
    }
}

/// `buf[start..start + bytes.len()]` holds the initialized bytes `bytes`.
/// (`holds` and `unchanged_outside` are opaque, to keep their quantifiers out of the `fmt` bodies.)
#[verifier::opaque]
pub open spec fn holds(buf: Seq<MaybeUninit<u8>>, start: int, bytes: Seq<u8>) -> bool {
    &&& 0 <= start
    &&& start + bytes.len() <= buf.len()
    &&& forall|j: int|
        start <= j < start + bytes.len() ==> #[trigger] buf[j].mem_contents() == MemContents::Init(
            bytes[j - start],
        )
}

/// `new` agrees with `old` outside the index range `lo..hi`.
#[verifier::opaque]
pub open spec fn unchanged_outside(
    new: Seq<MaybeUninit<u8>>,
    old: Seq<MaybeUninit<u8>>,
    lo: int,
    hi: int,
) -> bool {
    &&& new.len() == old.len()
    &&& forall|j: int| 0 <= j < old.len() && !(lo <= j < hi) ==> #[trigger] new[j] == old[j]
}

/// The value of a sequence of ASCII decimal digits, most significant first. Used only to show
/// that `dec` is the usual decimal notation (`lemma_dec_value`).
pub open spec fn digits_value(s: Seq<u8>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        10 * digits_value(s.drop_last()) + (s.last() - 48)
    }
}

/// Every byte of `s` is an ASCII decimal digit `b'0'..=b'9'`.
pub open spec fn is_digits(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> 48 <= #[trigger] s[i] <= 57
}

// ===== Powers of ten =====

proof fn lemma_div_by_one(x: int)
    ensures
        x / 1 == x,
{
}

pub broadcast proof fn lemma_pow10_pos(n: nat)
    ensures
        #[trigger] pow10(n) > 0,
    decreases n,
{
    if n > 0 {
        lemma_pow10_pos((n - 1) as nat);
    }
}

pub proof fn lemma_pow10_add(a: nat, b: nat)
    ensures
        pow10(a + b) == pow10(a) * pow10(b),
    decreases a,
{
    if a > 0 {
        let a1 = (a - 1) as nat;
        lemma_pow10_add(a1, b);
        assert(pow10(a + b) == 10 * pow10(a1 + b));
        assert(pow10(a) == 10 * pow10(a1));
        assert(pow10(a + b) == pow10(a) * pow10(b)) by (nonlinear_arith)
            requires
                pow10(a + b) == 10 * pow10(a1 + b),
                pow10(a1 + b) == pow10(a1) * pow10(b),
                pow10(a) == 10 * pow10(a1),
        ;
    } else {
        assert(pow10(a) == 1);
        assert(a + b == b);
    }
}

pub proof fn lemma_pow10_strictly_increases(a: nat, b: nat)
    requires
        a < b,
    ensures
        pow10(a) < pow10(b),
    decreases b,
{
    lemma_pow10_pos(a);
    if b > a + 1 {
        lemma_pow10_strictly_increases(a, (b - 1) as nat);
    }
}

pub proof fn lemma_pow10_le(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow10(a) <= pow10(b),
{
    if a < b {
        lemma_pow10_strictly_increases(a, b);
    }
}

/// `pow10` is injective on its order: `pow10(a) < pow10(b)` implies `a < b`.
pub proof fn lemma_pow10_lt_inv(a: nat, b: nat)
    requires
        pow10(a) < pow10(b),
    ensures
        a < b,
{
    if a >= b {
        lemma_pow10_le(b, a);
    }
}

/// `n / 10^(k + 1) == (n / 10^k) / 10`, and the analogous fact for steps of 100 and 10000.
pub proof fn lemma_div_pow10_step(n: nat, k: nat, j: nat)
    ensures
        n / pow10(k + j) == (n / pow10(k)) / pow10(j),
{
    lemma_pow10_add(k, j);
    lemma_pow10_pos(k);
    lemma_pow10_pos(j);
    lemma_div_denominator(n as int, pow10(k) as int, pow10(j) as int);
}

pub proof fn lemma_pow10_values()
    ensures
        pow10(0) == 1,
        pow10(1) == 10,
        pow10(2) == 100,
        pow10(3) == 1000,
        pow10(4) == 10000,
{
    reveal_with_fuel(pow10, 5);
}

// ===== Digit strings =====

pub broadcast proof fn lemma_dec_pad_len(n: nat, k: nat)
    ensures
        #[trigger] dec_pad(n, k).len() == k,
    decreases k,
{
    if k > 0 {
        lemma_dec_pad_len(n / 10, (k - 1) as nat);
    }
}

/// The digits of `n` split into the high `a` digits (of `n / 10^b`) and the low `b` digits.
pub proof fn lemma_dec_pad_split(n: nat, a: nat, b: nat)
    ensures
        dec_pad(n, a + b) == dec_pad(n / pow10(b), a) + dec_pad(n, b),
    decreases b,
{
    if b == 0 {
        assert(pow10(0) == 1);
        assert(n / pow10(b) == n) by {
            lemma_div_by_one(n as int);
        }
        assert(dec_pad(n, a + b) =~= dec_pad(n / pow10(b), a) + dec_pad(n, b));
    } else {
        let b1 = (b - 1) as nat;
        lemma_dec_pad_split(n / 10, a, b1);
        lemma_div_pow10_step(n, 1, b1);
        lemma_pow10_values();
        assert(1 + b1 == b);
        assert(a + b1 == (a + b - 1) as nat);
        let x = dec_pad(n / pow10(b), a);
        let y = dec_pad(n / 10, b1);
        let d = digit(n % 10);
        lemma_dec_pad_len(n / pow10(b), a);
        lemma_dec_pad_len(n / 10, b1);
        assert(dec_pad(n, a + b) == dec_pad(n / 10, a + b1).push(d));
        assert(dec_pad(n, b) == y.push(d));
        assert((x + y).push(d) =~= x + y.push(d));
    }
}

/// `dec_pad(n, k)` depends only on `n % 10^k`.
pub proof fn lemma_dec_pad_mod(n: nat, k: nat)
    ensures
        dec_pad(n, k) == dec_pad(n % pow10(k), k),
    decreases k,
{
    if k > 0 {
        let p = pow10((k - 1) as nat);
        lemma_pow10_pos((k - 1) as nat);
        let m = n % pow10(k);
        assert(pow10(k) == 10 * p);
        lemma_mod_mod(n as int, 10, p as int);
        lemma_mod_breakdown(n as int, 10, p as int);
        assert(m == 10 * ((n / 10) % p) + n % 10);
        assert(m / 10 == (n / 10) % p);
        assert(m % 10 == n % 10);
        lemma_dec_pad_mod(n / 10, (k - 1) as nat);
        lemma_dec_pad_mod(m / 10, (k - 1) as nat);
        lemma_mod_twice((n / 10) as int, p as int);
        assert((m / 10) % p == (n / 10) % p);
    }
}

pub proof fn lemma_dec_pad_1(d: nat)
    requires
        d < 10,
    ensures
        dec_pad(d, 1) == seq![digit(d)],
{
    reveal_with_fuel(dec_pad, 2);
    assert(dec_pad(d, 1) =~= seq![digit(d)]);
}

pub proof fn lemma_dec_pad_2(p: nat)
    requires
        p < 100,
    ensures
        dec_pad(p, 2) == seq![digit(p / 10), digit(p % 10)],
{
    reveal_with_fuel(dec_pad, 3);
    assert(dec_pad(p / 10, 1) == seq![digit((p / 10) % 10)]);
    assert((p / 10) % 10 == p / 10);
    assert(dec_pad(p, 2) =~= seq![digit(p / 10), digit(p % 10)]);
}

/// The four digits of `q` are the two digits of `q / 100` and the two digits of `q % 100`.
pub proof fn lemma_dec_pad_4(q: nat)
    requires
        q < 10000,
    ensures
        dec_pad(q, 4) == seq![
            digit((q / 100) / 10),
            digit((q / 100) % 10),
            digit((q % 100) / 10),
            digit((q % 100) % 10),
        ],
{
    lemma_pow10_values();
    lemma_dec_pad_split(q, 2, 2);
    lemma_dec_pad_mod(q, 2);
    lemma_dec_pad_2(q / 100);
    lemma_dec_pad_2(q % 100);
    assert(dec_pad(q, 4) =~= seq![
        digit((q / 100) / 10),
        digit((q / 100) % 10),
        digit((q % 100) / 10),
        digit((q % 100) % 10),
    ]);
}

/// `n` has exactly `k` digits when `10^(k-1) <= n < 10^k` (or `k == 1` and `n < 10`).
pub proof fn lemma_num_digits(n: nat, k: nat)
    requires
        1 <= k,
        n < pow10(k),
        k == 1 || pow10((k - 1) as nat) <= n,
    ensures
        num_digits(n) == k,
    decreases k,
{
    reveal_with_fuel(pow10, 2);
    if k > 1 {
        lemma_pow10_le(1, (k - 1) as nat);
        let p = pow10((k - 1) as nat);
        assert(n / 10 < p);
        if k > 2 {
            assert(pow10((k - 1) as nat) == 10 * pow10((k - 2) as nat));
            assert(pow10((k - 2) as nat) <= n / 10);
        }
        lemma_num_digits(n / 10, (k - 1) as nat);
    }
}

/// The converse of `lemma_num_digits`.
pub proof fn lemma_num_digits_bounds(n: nat)
    ensures
        1 <= num_digits(n),
        n < pow10(num_digits(n)),
        num_digits(n) == 1 || pow10((num_digits(n) - 1) as nat) <= n,
    decreases n,
{
    reveal_with_fuel(pow10, 2);
    if n >= 10 {
        lemma_num_digits_bounds(n / 10);
        let k = num_digits(n / 10);
        assert(pow10(k + 1) == 10 * pow10(k));
        if k > 1 {
            assert(pow10(k) == 10 * pow10((k - 1) as nat));
        }
    }
}

/// `n` has at most `k` digits exactly when `n < 10^k` (for `k >= 1`).
pub proof fn lemma_num_digits_le(n: nat, k: nat)
    requires
        1 <= k,
    ensures
        num_digits(n) <= k <==> n < pow10(k),
{
    lemma_num_digits_bounds(n);
    let d = num_digits(n);
    if d <= k {
        lemma_pow10_le(d, k);
    } else {
        lemma_pow10_le(k, (d - 1) as nat);
    }
}

pub proof fn lemma_dec_len(n: nat)
    ensures
        dec(n).len() == num_digits(n),
{
    lemma_dec_pad_len(n, num_digits(n));
}

// ===== Sanity: `dec` is the usual decimal notation =====

pub proof fn lemma_dec_pad_is_digits(n: nat, k: nat)
    ensures
        is_digits(dec_pad(n, k)),
    decreases k,
{
    if k > 0 {
        lemma_dec_pad_is_digits(n / 10, (k - 1) as nat);
        let s = dec_pad(n, k);
        assert forall|i: int| 0 <= i < s.len() implies 48 <= #[trigger] s[i] <= 57 by {
            lemma_dec_pad_len(n / 10, (k - 1) as nat);
            if i < k - 1 {
                assert(s[i] == dec_pad(n / 10, (k - 1) as nat)[i]);
            }
        }
    }
}

pub proof fn lemma_dec_pad_value(n: nat, k: nat)
    ensures
        digits_value(dec_pad(n, k)) == n % pow10(k),
    decreases k,
{
    if k > 0 {
        lemma_dec_pad_value(n / 10, (k - 1) as nat);
        let s = dec_pad(n, k);
        assert(s.drop_last() =~= dec_pad(n / 10, (k - 1) as nat));
        let p = pow10((k - 1) as nat);
        lemma_pow10_pos((k - 1) as nat);
        assert(pow10(k) == 10 * p);
        lemma_mod_breakdown(n as int, 10, p as int);
    } else {
        assert(n % 1 == 0);
    }
}

/// `dec(n)` consists of decimal digits, has no leading zero unless it is `"0"`, and its value is
/// `n`. These three facts determine it uniquely.
pub proof fn lemma_dec_value(n: nat)
    ensures
        is_digits(dec(n)),
        digits_value(dec(n)) == n,
        dec(n).len() >= 1,
        dec(n)[0] == 48 ==> n == 0 && dec(n) == seq![48u8],
{
    lemma_dec_pad_is_digits(n, num_digits(n));
    lemma_dec_pad_value(n, num_digits(n));
    lemma_num_digits_bounds(n);
    lemma_dec_len(n);
    let k = num_digits(n);
    lemma_pow10_pos(k);
    lemma_small_mod(n, pow10(k));
    assert(n % pow10(k) == n);
    // The leading digit is `n / 10^(k-1)`, which is nonzero when `k > 1`.
    lemma_dec_pad_split(n, 1, (k - 1) as nat);
    assert((1 + (k - 1)) as nat == k);
    let top = n / pow10((k - 1) as nat);
    lemma_pow10_pos((k - 1) as nat);
    assert(top < 10) by {
        assert(pow10(k) == 10 * pow10((k - 1) as nat)) by {
            reveal_with_fuel(pow10, 2);
        }
        lemma_multiply_divide_lt(n as int, pow10((k - 1) as nat) as int, 10);
    }
    lemma_dec_pad_1(top);
    assert(dec(n)[0] == digit(top));
    if k > 1 {
        assert(top >= 1) by {
            lemma_div_is_ordered(pow10((k - 1) as nat) as int, n as int, pow10((k - 1) as nat) as int);
            lemma_div_by_self(pow10((k - 1) as nat) as int);
        }
    } else {
        assert(pow10(0) == 1);
        if dec(n)[0] == 48 {
            assert(dec(n) =~= seq![48u8]);
        }
    }
}

// ===== Buffers and the digit loops =====

/// `holds` for an empty run.
pub proof fn lemma_holds_empty(buf: Seq<MaybeUninit<u8>>, start: int)
    requires
        0 <= start <= buf.len(),
    ensures
        holds(buf, start, Seq::empty()),
{
    reveal(holds);
    reveal(unchanged_outside);
}

/// After `w` is written at `start..start + w.len()`, the buffer holds it and is otherwise
/// unchanged. The preconditions are cheap to prove at a call site after a few writes, whereas
/// revealing `holds` and `unchanged_outside` there would slow down the whole function body.
pub proof fn lemma_wrote(
    old_buf: Seq<MaybeUninit<u8>>,
    new_buf: Seq<MaybeUninit<u8>>,
    start: int,
    w: Seq<u8>,
)
    requires
        0 <= start,
        start + w.len() <= old_buf.len(),
        new_buf.len() == old_buf.len(),
        forall|i: int|
            0 <= i < w.len() ==> #[trigger] new_buf[start + i].mem_contents() == MemContents::Init(
                w[i],
            ),
        forall|j: int|
            0 <= j < old_buf.len() && !(start <= j < start + w.len()) ==> #[trigger] new_buf[j]
                == old_buf[j],
    ensures
        holds(new_buf, start, w),
        unchanged_outside(new_buf, old_buf, start, start + w.len()),
{
    reveal(holds);
    reveal(unchanged_outside);
    assert forall|j: int| start <= j < start + w.len() implies #[trigger] new_buf[j].mem_contents()
        == MemContents::Init(w[j - start]) by {
        assert(new_buf[start + (j - start)] == new_buf[j]);
    }
}

/// `unchanged_outside` over an empty range: nothing changed.
pub proof fn lemma_unchanged_refl(buf: Seq<MaybeUninit<u8>>, at: int)
    ensures
        unchanged_outside(buf, buf, at, at),
{
    reveal(unchanged_outside);
}

/// Writing `chunk` just before a run `rest` that the buffer already holds extends the run.
pub proof fn lemma_holds_prepend(
    old_buf: Seq<MaybeUninit<u8>>,
    new_buf: Seq<MaybeUninit<u8>>,
    start: int,
    chunk: Seq<u8>,
    rest: Seq<u8>,
)
    requires
        holds(old_buf, start + chunk.len(), rest),
        holds(new_buf, start, chunk),
        unchanged_outside(new_buf, old_buf, start, start + chunk.len()),
    ensures
        holds(new_buf, start, chunk + rest),
{
    reveal(holds);
    reveal(unchanged_outside);
    assert forall|j: int| start <= j < start + (chunk + rest).len() implies #[trigger] new_buf[j].mem_contents()
        == MemContents::Init((chunk + rest)[j - start]) by {
        if j >= start + chunk.len() {
            assert(new_buf[j] == old_buf[j]);
            assert(old_buf[j].mem_contents() == MemContents::Init(rest[j - (start + chunk.len())]));
        }
    }
}

/// A run survives writes outside it.
pub proof fn lemma_holds_frame(
    old_buf: Seq<MaybeUninit<u8>>,
    new_buf: Seq<MaybeUninit<u8>>,
    start: int,
    bytes: Seq<u8>,
    lo: int,
    hi: int,
)
    requires
        holds(old_buf, start, bytes),
        unchanged_outside(new_buf, old_buf, lo, hi),
        hi <= start || start + bytes.len() <= lo,
    ensures
        holds(new_buf, start, bytes),
{
    reveal(holds);
    reveal(unchanged_outside);
    assert forall|j: int| start <= j < start + bytes.len() implies #[trigger] new_buf[j].mem_contents()
        == MemContents::Init(bytes[j - start]) by {
        assert(new_buf[j] == old_buf[j]);
    }
}

/// Writes to `lo..mid` after writes to `mid..hi` change only `lo..hi`.
pub proof fn lemma_unchanged_extend(
    b0: Seq<MaybeUninit<u8>>,
    b1: Seq<MaybeUninit<u8>>,
    b2: Seq<MaybeUninit<u8>>,
    lo: int,
    mid: int,
    hi: int,
)
    requires
        unchanged_outside(b1, b0, mid, hi),
        unchanged_outside(b2, b1, lo, mid),
        lo <= mid <= hi,
    ensures
        unchanged_outside(b2, b0, lo, hi),
{
    reveal(unchanged_outside);
}

/// Invariant of the digit loops of `Unsigned::fmt`: `buf[offset..n]` holds the `n - offset` low
/// digits of `v`, the most significant of which is a significant digit of `v`; `remain` is what is
/// left of `v` once those digits are removed; and `buf` is unchanged before `offset`.
/// (Opaque, to keep its quantifiers out of the `fmt` bodies; the lemmas below reveal it.)
#[verifier::opaque]
pub open spec fn digits_inv(
    v: nat,
    n: nat,
    offset: nat,
    remain: nat,
    buf: Seq<MaybeUninit<u8>>,
    old_buf: Seq<MaybeUninit<u8>>,
) -> bool {
    let k = (n - offset) as nat;
    &&& offset <= n
    &&& buf.len() == n
    &&& v < pow10(n)
    &&& remain == v / pow10(k)
    &&& (k == 0 || pow10((k - 1) as nat) <= v)
    &&& holds(buf, offset as int, dec_pad(v, k))
    &&& unchanged_outside(buf, old_buf, offset as int, n as int)
}

/// The invariant holds before any digit is written.
pub proof fn lemma_digits_start(v: nat, n: nat, buf: Seq<MaybeUninit<u8>>)
    requires
        dec(v).len() <= n,
        buf.len() == n,
    ensures
        1 <= n,
        v < pow10(n),
        digits_inv(v, n, n, v, buf, buf),
{
    reveal(holds);
    reveal(unchanged_outside);
    reveal(digits_inv);
    lemma_dec_len(v);
    lemma_num_digits_bounds(v);
    lemma_num_digits_le(v, n);
    assert(pow10(0) == 1);
    lemma_div_by_one(v as int);
    assert(dec_pad(v, 0) =~= Seq::<u8>::empty());
    lemma_holds_empty(buf, n as int);
}

/// `remain`, the part of `v` above the `k` digits written, is at least `10^(j-1)`, so `v` has at
/// least `k + j` digits.
proof fn lemma_digits_lower_bound(v: nat, k: nat, remain: nat, j: nat)
    requires
        remain == v / pow10(k),
        1 <= j,
        pow10((j - 1) as nat) <= remain,
    ensures
        pow10((k + j - 1) as nat) <= v,
{
    lemma_pow10_pos(k);
    lemma_fundamental_div_mod(v as int, pow10(k) as int);
    lemma_mul_inequality(pow10((j - 1) as nat) as int, remain as int, pow10(k) as int);
    lemma_pow10_add((j - 1) as nat, k);
    assert((j - 1) as nat + k == (k + j - 1) as nat);
    assert(pow10(k) * remain == remain * pow10(k)) by (nonlinear_arith);
}

/// There is room for `j` more digits when the rest `remain` has at least `j` digits.
pub proof fn lemma_digits_room(
    v: nat,
    n: nat,
    offset: nat,
    remain: nat,
    buf: Seq<MaybeUninit<u8>>,
    old_buf: Seq<MaybeUninit<u8>>,
    j: nat,
)
    requires
        digits_inv(v, n, offset, remain, buf, old_buf),
        1 <= j,
        pow10((j - 1) as nat) <= remain,
    ensures
        j <= offset <= n,
        0 < v,
{
    reveal(digits_inv);
    let k = (n - offset) as nat;
    lemma_digits_lower_bound(v, k, remain, j);
    lemma_pow10_lt_inv((k + j - 1) as nat, n);
    lemma_pow10_pos((k + j - 1) as nat);
}

/// Writing the `j` low digits of `remain` just before `offset` (when `remain` has at least `j`
/// digits) re-establishes the invariant with `j` more digits. (`d` is `10^j`, passed as a literal
/// so that callers see a division by a constant.)
pub proof fn lemma_digits_step(
    v: nat,
    n: nat,
    offset: nat,
    remain: nat,
    j: nat,
    d: nat,
    buf: Seq<MaybeUninit<u8>>,
    new_buf: Seq<MaybeUninit<u8>>,
    old_buf: Seq<MaybeUninit<u8>>,
)
    requires
        digits_inv(v, n, offset, remain, buf, old_buf),
        1 <= j <= offset,
        d == pow10(j),
        pow10((j - 1) as nat) <= remain,
        holds(new_buf, offset - j, dec_pad(remain, j)),
        unchanged_outside(new_buf, buf, offset - j, offset as int),
    ensures
        digits_inv(v, n, (offset - j) as nat, remain / d, new_buf, old_buf),
{
    reveal(holds);
    reveal(unchanged_outside);
    reveal(digits_inv);
    let k = (n - offset) as nat;
    let k2 = (n - (offset - j)) as nat;
    assert(k2 == j + k);
    lemma_dec_pad_split(v, j, k);
    lemma_dec_pad_len(remain, j);
    lemma_dec_pad_len(v, k);
    lemma_holds_prepend(buf, new_buf, offset - j, dec_pad(remain, j), dec_pad(v, k));
    lemma_div_pow10_step(v, k, j);
    assert(k + j == j + k);
    lemma_digits_lower_bound(v, k, remain, j);
    assert((k2 - 1) as nat == (k + j - 1) as nat);
}

/// Once `remain` is zero, the buffer holds exactly the decimal representation of `v > 0`.
pub proof fn lemma_digits_done(
    v: nat,
    n: nat,
    offset: nat,
    buf: Seq<MaybeUninit<u8>>,
    old_buf: Seq<MaybeUninit<u8>>,
)
    requires
        digits_inv(v, n, offset, 0, buf, old_buf),
        0 < v,
    ensures
        offset + dec(v).len() == n,
        holds(buf, offset as int, dec(v)),
        unchanged_outside(buf, old_buf, offset as int, n as int),
{
    reveal(holds);
    reveal(unchanged_outside);
    reveal(digits_inv);
    let k = (n - offset) as nat;
    lemma_pow10_pos(k);
    lemma_small_div_converse(v as int, pow10(k) as int);
    if k == 0 {
        assert(pow10(0) == 1);
    }
    lemma_num_digits(v, k);
    lemma_dec_len(v);
}

/// Zero has no significant digits, so no digit was written yet.
pub proof fn lemma_digits_zero(
    n: nat,
    offset: nat,
    buf: Seq<MaybeUninit<u8>>,
    old_buf: Seq<MaybeUninit<u8>>,
)
    requires
        digits_inv(0, n, offset, 0, buf, old_buf),
    ensures
        offset == n,
        buf == old_buf,
{
    reveal(holds);
    reveal(unchanged_outside);
    reveal(digits_inv);
    if offset < n {
        lemma_pow10_pos((n - offset - 1) as nat);
    }
    assert(buf =~= old_buf);
}

/// The decimal representation of zero is `"0"`.
pub proof fn lemma_dec_zero()
    ensures
        dec(0) == seq![48u8],
{
    lemma_dec_pad_1(0);
}

/// The 4-digit chunk the loops write for `r`: the table entries of `(r % 10000) / 100` and of
/// `(r % 10000) % 100`.
pub proof fn lemma_chunk_4(r: nat, p1: int, p2: int)
    requires
        p1 == (r % 10000) / 100,
        p2 == (r % 10000) % 100,
    ensures
        dec_pad(r, 4) == seq![
            decimal_pairs()[p1 * 2 + 0],
            decimal_pairs()[p1 * 2 + 1],
            decimal_pairs()[p2 * 2 + 0],
            decimal_pairs()[p2 * 2 + 1],
        ],
{
    lemma_pow10_values();
    lemma_dec_pad_mod(r, 4);
    lemma_dec_pad_4(r % 10000);
    lemma_decimal_pair(p1);
    lemma_decimal_pair(p2);
}

/// The 2-digit chunk the loops write for `r`: the table entries of `r % 100`.
pub proof fn lemma_chunk_2(r: nat, p: int)
    requires
        p == r % 100,
    ensures
        dec_pad(r, 2) == seq![decimal_pairs()[p * 2 + 0], decimal_pairs()[p * 2 + 1]],
{
    lemma_pow10_values();
    lemma_dec_pad_mod(r, 2);
    lemma_dec_pad_2(r % 100);
    lemma_decimal_pair(p);
}

/// The 1-digit chunk the loops write for `r < 10`: `b'0' + r`.
pub proof fn lemma_chunk_1(r: nat)
    requires
        r < 10,
    ensures
        dec_pad(r, 1) == seq![(48 + r) as u8],
{
    lemma_dec_pad_1(r);
}

/// The lookup table `DECIMAL_PAIRS`: the two digits of each of `00`, `01`, ..., `99` in turn, so
/// entry `2p` is the tens digit and entry `2p + 1` the units digit of `p`.
pub open spec fn decimal_pairs() -> Seq<u8> {
    Seq::new(
        200,
        |i: int|
            if i % 2 == 0 {
                digit(((i / 2) / 10) as nat)
            } else {
                digit(((i / 2) % 10) as nat)
            },
    )
}

pub proof fn lemma_decimal_pair(p: int)
    requires
        0 <= p < 100,
    ensures
        decimal_pairs()[p * 2 + 0] == digit((p / 10) as nat),
        decimal_pairs()[p * 2 + 1] == digit((p % 10) as nat),
{
    assert((p * 2 + 0) % 2 == 0 && (p * 2 + 0) / 2 == p);
    assert((p * 2 + 1) % 2 == 1 && (p * 2 + 1) / 2 == p);
}

} // verus!
