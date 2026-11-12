#!/usr/bin/env python3
"""Negative controls: inject one bug at a time into a scratch copy of itoa/src and check that
Verus rejects it. Usage: python3 negative_controls.py (from verus/), with `verus` on PATH or
VERUS=/path/to/verus. Exits 1 if any mutant verifies."""
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, 'itoa', 'src')
VERUS = os.environ.get('VERUS', shutil.which('verus') or 'verus')

# (id, description, file, old text, new text). `old` must occur exactly once in `file`.
MUTANTS = [
    ('M1', 'divmod100: shift 18 instead of 19 (wrong reciprocal)', 'lib.rs',
     'const EXP: u32 = 19;', 'const EXP: u32 = 18;'),
    ('M2', 'DECIMAL_PAIRS: entry "07" stored as "70"', 'lib.rs',
     '48, 54, 48, 55, 48, 56, 48, 57, // "00010203040506070809"',
     '48, 54, 55, 48, 48, 56, 48, 57, // "00010203040506070809"'),
    ('M3', 'div_rem_1e16: M_HIGH one too small (floor instead of ceiling of 2^179 / 10^16)', 'lib.rs',
     'const M_HIGH: u128 = 76624777043294442917917351357515459181;',
     'const M_HIGH: u128 = 76624777043294442917917351357515459180;'),
    ('M4', 'div_rem_1e16: post-shift 50 instead of 51', 'lib.rs',
     'const SH_POST: u8 = 51;', 'const SH_POST: u8 = 50;'),
    ('M5', 'mulhi: drops the second carry `high2`', 'u128_ext.rs',
     'u128::from(x_hi) * u128::from(y_hi) + high1 + high2', 'u128::from(x_hi) * u128::from(y_hi) + high1'),
    ('M6', 'mulhi: high half of `m` taken with `>> 63`', 'u128_ext.rs',
     'let high1 = m >> 64;', 'let high1 = m >> 63;'),
    ('M7', 'u8..u64 fmt: the two pairs of a 4-digit group written in swapped order', 'lib.rs',
     'write_unchecked(buf, offset + 0, *get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 0));\n'
     '                    write_unchecked(buf, offset + 1, *get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 1));\n'
     '                    write_unchecked(buf, offset + 2, *get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 0));\n'
     '                    write_unchecked(buf, offset + 3, *get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 1));',
     'write_unchecked(buf, offset + 0, *get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 0));\n'
     '                    write_unchecked(buf, offset + 1, *get_unchecked(&DECIMAL_PAIRS.0, pair2 as usize * 2 + 1));\n'
     '                    write_unchecked(buf, offset + 2, *get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 0));\n'
     '                    write_unchecked(buf, offset + 3, *get_unchecked(&DECIMAL_PAIRS.0, pair1 as usize * 2 + 1));'),
    ('M8', 'u8..u64 fmt: two-digit step only above 10 (10 would print as ":")', 'lib.rs',
     '                // Format per two digits from the lookup table.\n                if remain > 9 {\n'
     '                    let ghost (offset0, remain0, buf0) = (offset as nat, remain as nat, buf@);\n'
     '                    proof {\n                        lemma_pow10_values();\n'
     '                        lemma_digits_room(v, N as nat, offset0, remain0, buf0, old(buf)@, 2);',
     '                // Format per two digits from the lookup table.\n                if remain > 10 {\n'
     '                    let ghost (offset0, remain0, buf0) = (offset as nat, remain as nat, buf@);\n'
     '                    proof {\n                        lemma_pow10_values();\n'
     '                        lemma_digits_room(v, N as nat, offset0, remain0, buf0, old(buf)@, 2);'),
    ('M9', 'u8..u64 fmt: no digit for zero (drops `|| self == 0`)', 'lib.rs',
     'if remain != 0 || self == 0 {', 'if remain != 0 {'),
    ('M10', 'u8..u64 fmt: offset moves 3 for a 4-digit group (groups overlap)', 'lib.rs',
     '                    offset -= 4;\n\n                    // pull two pairs\n                    let scale: Self',
     '                    offset -= 3;\n\n                    // pull two pairs\n                    let scale: Self'),
    ('M11', 'u128 fmt: second 16-digit block reported at N - 15', 'lib.rs',
     '(mod2, N - 16)', '(mod2, N - 15)'),
    ('M12', 'u128 fmt: zero shortcut removed (zero prints the empty string)', 'lib.rs',
     '        if self == 0 {\n            let offset = buf.len() - 1;',
     '        if false {\n            let offset = buf.len() - 1;'),
    ('M13', 'enc_16lsd: loop stops one 4-digit group early', 'lib.rs',
     'while quad_index > 1', 'while quad_index > 2'),
    ('M14', 'Signed::fmt: unsigned_abs off by one for negative values', 'lib.rs',
     '(-(self + 1)) as $Unsigned + 1', '(-(self + 1)) as $Unsigned'),
    ('M15', "Signed::fmt: '-' written over the first digit", 'lib.rs',
     '                    offset -= 1;\n                    write_unchecked(buf, offset, 45); // b\'-\'',
     '                    write_unchecked(buf, offset, 45); // b\'-\''),
    ('M16', 'trusted: unsigned MAX_STR_LEN one too small (`ilog10() + 0`)', 'trusted.rs',
     'const MAX_STR_LEN: usize = $Unsigned::MAX.ilog10() as usize + 1;',
     'const MAX_STR_LEN: usize = $Unsigned::MAX.ilog10() as usize + 0;'),
    ('M17', 'trusted: signed MAX_STR_LEN without room for the sign (`ilog10() + 1`)', 'trusted.rs',
     'const MAX_STR_LEN: usize = $Signed::MAX.ilog10() as usize + 2;',
     'const MAX_STR_LEN: usize = $Signed::MAX.ilog10() as usize + 1;'),
    ('M18', 'spec: digits encoded from b\'1\' instead of b\'0\'', 'spec.rs',
     '    (48 + d) as u8\n', '    (49 + d) as u8\n'),
    ('M19', 'cheating: `assume(false)` in divmod100 (rejected by --no-cheating)', 'lib.rs',
     '        assert(1u32 << 19u32 == 524288) by (bit_vector);',
     '        assume(false);'),
    ('M20', 'cheating: divmod100 made external_body (rejected by --no-cheating)', 'lib.rs',
     '// Returns {value / 100, value % 100} correct for values of up to 4 digits.\nfn divmod100',
     '// Returns {value / 100, value % 100} correct for values of up to 4 digits.\n'
     '#[verifier::external_body]\nfn divmod100'),
]


def run_verus(root):
    proc = subprocess.run([VERUS, '--crate-type=lib', '--no-cheating', 'src/lib.rs'], cwd=root,
                          capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    m = re.search(r'verification results:: (\d+) verified, (\d+) errors', out)
    errors = [line.strip() for line in out.splitlines() if line.startswith('error')]
    ok = proc.returncode == 0 and m is not None and m.group(2) == '0'
    return ok, (errors[0] if errors else '(no error line)'), out


def main():
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        root = os.path.join(tmp, 'crate')
        ok, _, out = run_verus_copy(root, None)
        if not ok:
            print('the unmodified crate does not verify:\n' + out)
            sys.exit(2)
        print('unmodified crate: verifies')
        for mid, desc, fname, old, new in MUTANTS:
            ok, first_error, _ = run_verus_copy(root, (fname, old, new))
            status = 'VERIFIED (BAD)' if ok else 'rejected'
            if ok:
                failures += 1
            print(f'{mid:<4} {status:<15} {desc}\n     -> {first_error}')
    print(f'{len(MUTANTS)} mutants, {len(MUTANTS) - failures} rejected')
    sys.exit(1 if failures else 0)


def run_verus_copy(root, mutation):
    if os.path.exists(root):
        shutil.rmtree(root)
    shutil.copytree(SRC, os.path.join(root, 'src'))
    if mutation:
        fname, old, new = mutation
        path = os.path.join(root, 'src', fname)
        text = open(path).read()
        count = text.count(old)
        if count != 1:
            raise SystemExit(f'mutation anchor found {count} times in {fname}: {old!r}')
        open(path, 'w').write(text.replace(old, new))
    return run_verus(root)


if __name__ == '__main__':
    main()
