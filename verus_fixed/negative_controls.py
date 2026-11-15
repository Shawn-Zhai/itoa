#!/usr/bin/env python3
"""Negative controls: inject one bug at a time into a scratch copy of itoa/src and check that
Verus rejects it. Usage: python3 negative_controls.py (from verus_fixed/), with `verus` on PATH or
VERUS=/path/to/verus. Exits 1 if any mutant is accepted.

A mutant is rejected when verification fails, or when `--no-cheating` reports a trust marker
beyond the two expected ones (`buffer_of` and `slice_buffer_to_str` in trusted.rs).
M1-M20 are the mutants of Claude's first pass (M16/M17 re-anchored: `MAX_STR_LEN` moved out of
trusted.rs); M21-M28 exercise the contracts added in verus_fixed."""
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, 'itoa', 'src')
VERUS = os.environ.get('VERUS', shutil.which('verus') or 'verus')

# The macros' compile-time checks of the `MAX_STR_LEN` constants against upstream's formula.
# M16/M17 delete them, so that the mutant tests Verus rather than rustc's const evaluation.
ASSERT_UNSIGNED = ('            assert!(private::$unsigned_len == $Unsigned::MAX.ilog10() as usize + 1, '
                   '"wrong unsigned length");\n')
ASSERT_SIGNED = ('            assert!(private::$signed_len == $Signed::MAX.ilog10() as usize + 2, '
                 '"wrong signed length");\n')

UNSIGNED_WRITE_TAIL = '''                let offset = Unsigned::fmt(self, buf);
                proof {
                    lemma_holds_suffix(buf@, offset as int, dec(self as nat));
                }
                // SAFETY: Starting from `offset`, all elements of the slice have been set.
                unsafe { slice_buffer_to_str(buf, offset) }'''
SIGNED_WRITE_TAIL = '''                let offset = Signed::fmt(self, buf);
                proof {
                    lemma_holds_suffix(buf@, offset as int, dec_int(self as int));
                }
                // SAFETY: Starting from `offset`, all elements of the slice have been set.
                unsafe { slice_buffer_to_str(buf, offset) }'''

# (id, description, [(file, old text, new text), ...]). Each `old` must occur exactly once.
MUTANTS = [
    ('M1', 'divmod100: shift 18 instead of 19 (wrong reciprocal)', [('lib.rs',
     'const EXP: u32 = 19;', 'const EXP: u32 = 18;')]),
    ('M2', 'DECIMAL_PAIRS: entry "07" stored as "70"', [('lib.rs',
     '48, 54, 48, 55, 48, 56, 48, 57, // "00010203040506070809"',
     '48, 54, 55, 48, 48, 56, 48, 57, // "00010203040506070809"')]),
    ('M3', 'div_rem_1e16: M_HIGH one too small (floor instead of ceiling of 2^179 / 10^16)', [('lib.rs',
     'const M_HIGH: u128 = 76624777043294442917917351357515459181;',
     'const M_HIGH: u128 = 76624777043294442917917351357515459180;')]),
    ('M4', 'div_rem_1e16: post-shift 50 instead of 51', [('lib.rs',
     'const SH_POST: u8 = 51;', 'const SH_POST: u8 = 50;')]),
    ('M5', 'mulhi: drops the second carry `high2`', [('u128_ext.rs',
     'u128::from(x_hi) * u128::from(y_hi) + high1 + high2', 'u128::from(x_hi) * u128::from(y_hi) + high1')]),
    ('M6', 'mulhi: high half of `m` taken with `>> 63`', [('u128_ext.rs',
     'let high1 = m >> 64;', 'let high1 = m >> 63;')]),
    ('M7', 'u8..u64 fmt: the two pairs of a 4-digit group written in swapped order', [('lib.rs',
     'write_unchecked(buf, offset + 0, *get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 0));\n'
     '                    write_unchecked(buf, offset + 1, *get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 1));\n'
     '                    write_unchecked(buf, offset + 2, *get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 0));\n'
     '                    write_unchecked(buf, offset + 3, *get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 1));',
     'write_unchecked(buf, offset + 0, *get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 0));\n'
     '                    write_unchecked(buf, offset + 1, *get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 1));\n'
     '                    write_unchecked(buf, offset + 2, *get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 0));\n'
     '                    write_unchecked(buf, offset + 3, *get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 1));')]),
    ('M8', 'u8..u64 fmt: two-digit step only above 10 (10 would print as ":")', [('lib.rs',
     '                // Format per two digits from the lookup table.\n                if remain > 9 {\n'
     '                    let ghost (offset0, remain0, buf0) = (offset as nat, remain as nat, buf@);\n'
     '                    proof {\n                        lemma_pow10_values();\n'
     '                        lemma_digits_room(v, N as nat, offset0, remain0, buf0, old(buf)@, 2);',
     '                // Format per two digits from the lookup table.\n                if remain > 10 {\n'
     '                    let ghost (offset0, remain0, buf0) = (offset as nat, remain as nat, buf@);\n'
     '                    proof {\n                        lemma_pow10_values();\n'
     '                        lemma_digits_room(v, N as nat, offset0, remain0, buf0, old(buf)@, 2);')]),
    ('M9', 'u8..u64 fmt: no digit for zero (drops `|| self == 0`)', [('lib.rs',
     'if remain != 0 || self == 0 {', 'if remain != 0 {')]),
    ('M10', 'u8..u64 fmt: offset moves 3 for a 4-digit group (groups overlap)', [('lib.rs',
     '                    offset -= 4;\n\n                    // pull two pairs\n                    let scale: Self',
     '                    offset -= 3;\n\n                    // pull two pairs\n                    let scale: Self')]),
    ('M11', 'u128 fmt: second 16-digit block reported at N - 15', [('lib.rs',
     '(mod2, N - 16)', '(mod2, N - 15)')]),
    ('M12', 'u128 fmt: zero shortcut removed (zero prints the empty string)', [('lib.rs',
     '        if self == 0 {\n            let offset = buf.len() - 1;',
     '        if false {\n            let offset = buf.len() - 1;')]),
    ('M13', 'enc_16lsd: loop stops one 4-digit group early', [('lib.rs',
     'while quad_index > 1', 'while quad_index > 2')]),
    ('M14', 'Signed::fmt: unsigned_abs off by one for negative values', [('lib.rs',
     '(-(self + 1)) as $Unsigned + 1', '(-(self + 1)) as $Unsigned')]),
    ('M15', "Signed::fmt: '-' written over the first digit", [('lib.rs',
     '                    offset -= 1;\n                    write_unchecked(buf, offset, 45); // b\'-\'',
     '                    write_unchecked(buf, offset, 45); // b\'-\'')]),
    ('M16', 'u8 MAX_STR_LEN one too small (2), compile-time check removed', [
     ('lib.rs', 'pub const U8_MAX_STR_LEN: usize = 3;', 'pub const U8_MAX_STR_LEN: usize = 2;'),
     ('lib.rs', ASSERT_UNSIGNED, '')]),
    ('M17', 'i64 MAX_STR_LEN without room for the sign (19), compile-time check removed', [
     ('lib.rs', 'pub const I64_MAX_STR_LEN: usize = 20;', 'pub const I64_MAX_STR_LEN: usize = 19;'),
     ('lib.rs', ASSERT_SIGNED, '')]),
    ('M18', "spec: digits encoded from b'1' instead of b'0'", [('spec.rs',
     '    (48 + d) as u8\n', '    (49 + d) as u8\n')]),
    ('M19', 'cheating: `assume(false)` in divmod100 (a new trust marker for --no-cheating)', [('lib.rs',
     '        assert(1u32 << 19u32 == 524288) by (bit_vector);',
     '        assume(false);')]),
    ('M20', 'cheating: divmod100 made external_body (a new trust marker for --no-cheating)', [('lib.rs',
     '// Returns {value / 100, value % 100} correct for values of up to 4 digits.\nfn divmod100',
     '// Returns {value / 100, value % 100} correct for values of up to 4 digits.\n'
     '#[verifier::external_body]\nfn divmod100')]),
    # --- contracts added in verus_fixed ---
    ('M21', 'unsigned write: the string starts one byte late (drops the leading digit)', [('lib.rs',
     UNSIGNED_WRITE_TAIL, UNSIGNED_WRITE_TAIL.replace('slice_buffer_to_str(buf, offset)',
                                                      'slice_buffer_to_str(buf, offset + 1)'))]),
    ('M22', 'signed write: the string starts at 0 (reads the uninitialized prefix)', [('lib.rs',
     SIGNED_WRITE_TAIL, SIGNED_WRITE_TAIL.replace('slice_buffer_to_str(buf, offset)',
                                                  'slice_buffer_to_str(buf, 0)'))]),
    ('M23', 'format: the `unreachable_unchecked` length check uses `>=` (reachable at full length)', [('lib.rs',
     'if string.len() > I::MAX_STR_LEN {', 'if string.len() >= I::MAX_STR_LEN {')]),
    ('M24', 'usize MAX_STR_LEN taken from u32 (10) instead of u64 (20)', [('lib.rs',
     'impl_Integer_size!(usize as u64, U64_MAX_STR_LEN #[cfg(target_pointer_width = "64")]);',
     'impl_Integer_size!(usize as u64, U32_MAX_STR_LEN #[cfg(target_pointer_width = "64")]);')]),
    ('M25', 'trusted contract of slice_buffer_to_str shifted by one byte', [('trusted.rs',
     'result.spec_bytes() == suffix_bytes(buf@, offset as int),',
     'result.spec_bytes() == suffix_bytes(buf@, offset as int + 1),')]),
    ('M26', "developer's spec: decimal_digit(7) is '8'", [('human_spec.rs',
     "    } else if d == 7 {\n        '7'", "    } else if d == 7 {\n        '8'")]),
    ('M27', "developer's spec: initialized_ascii_suffix requires nothing", [('human_spec.rs',
     'pub open spec fn initialized_ascii_suffix(buf: &[MaybeUninit<u8>], offset: usize) -> bool {\n'
     '    forall|i: int|',
     'pub open spec fn initialized_ascii_suffix(buf: &[MaybeUninit<u8>], offset: usize) -> bool {\n'
     '    true || forall|i: int|')]),
    ('M28', 'usize MAX_STR_LEN taken from u128 (39) instead of u64 (20): too large', [('lib.rs',
     'impl_Integer_size!(usize as u64, U64_MAX_STR_LEN #[cfg(target_pointer_width = "64")]);',
     'impl_Integer_size!(usize as u64, U128_MAX_STR_LEN #[cfg(target_pointer_width = "64")]);')]),
]


def run(root, *flags):
    proc = subprocess.run([VERUS, '--crate-type=lib', *flags, 'src/lib.rs'], cwd=root,
                          capture_output=True, text=True)
    return proc.returncode, proc.stdout + proc.stderr


def check(root):
    """(verified, first error, trust markers): verification without --no-cheating, then the
    locations that --no-cheating reports."""
    code, out = run(root)
    m = re.search(r'verification results:: (\d+) verified, (\d+) errors', out)
    verified = code == 0 and m is not None and m.group(2) == '0'
    errors = [line.strip() for line in out.splitlines() if line.startswith('error')]
    _, out_nc = run(root, '--no-cheating')
    markers, lines = [], out_nc.splitlines()
    for i, line in enumerate(lines):
        if line.startswith('error') and 'not allowed with --no-cheating' in line:
            loc = re.search(r'--> (\S+):(\d+)', '\n'.join(lines[i + 1:i + 3]))
            markers.append((loc.group(1), ' '.join(lines[i + 3:i + 4]).strip()) if loc else ('?', line))
    return verified, (errors[0] if errors else '(no error line)'), markers


def copy_with(root, edits):
    if os.path.exists(root):
        shutil.rmtree(root)
    shutil.copytree(SRC, os.path.join(root, 'src'))
    for fname, old, new in edits:
        path = os.path.join(root, 'src', fname)
        text = open(path).read()
        count = text.count(old)
        if count != 1:
            raise SystemExit(f'mutation anchor found {count} times in {fname}: {old!r}')
        open(path, 'w').write(text.replace(old, new))


def main():
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        root = os.path.join(tmp, 'crate')
        copy_with(root, [])
        ok, err, base_markers = check(root)
        if not ok or len(base_markers) != 2:
            print(f'the unmodified crate does not verify, or has {len(base_markers)} trust markers: {err}')
            sys.exit(2)
        print('unmodified crate: verifies; --no-cheating reports the 2 trusted items')
        for mid, desc, edits in MUTANTS:
            copy_with(root, edits)
            ok, err, markers = check(root)
            extra = len(markers) - len(base_markers)
            accepted = ok and extra <= 0
            if accepted:
                failures += 1
            why = err if not ok else f'{extra} new trust marker(s) under --no-cheating'
            print(f'{mid:<4} {"ACCEPTED (BAD)" if accepted else "rejected":<15} {desc}\n     -> {why}')
    print(f'{len(MUTANTS)} mutants, {len(MUTANTS) - failures} rejected')
    sys.exit(1 if failures else 0)


if __name__ == '__main__':
    main()
