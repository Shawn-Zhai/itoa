#!/usr/bin/env python3
"""Check that itoa/src/trusted.rs is upstream code: each of its items must appear verbatim in
upstream ../src/lib.rs, except the `write` method for signed types inside `impl_Integer!`, the one
expected change (its formatting logic moved to the verified `Signed::fmt`). Prints the diff of
that change. Usage: python3 check_trusted.py (from verus/)."""
import difflib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
UPSTREAM = open(os.path.join(HERE, '..', 'src', 'lib.rs')).read()
TRUSTED = open(os.path.join(HERE, 'itoa', 'src', 'trusted.rs')).read()


def items(text):
    """Top-level items (with their doc comments and attributes) after the module header."""
    body = text[text.index('// ===== T1 =====') :]
    lines = [l for l in body.split('\n') if not l.startswith('// =====')]
    out, cur = [], []
    for line in lines:
        cur.append(line)
        # An item ends at a closing brace or semicolon in column 0.
        if line in ('}', '};') or (line.endswith(';') and not line.startswith(' ')):
            out.append('\n'.join(cur).strip('\n'))
            cur = []
    return [i for i in out if i.strip()]


def unindent_impl_method(item):
    """`impl Buffer { <method> }` in trusted.rs is one method of upstream's `impl Buffer`."""
    m = re.match(r'impl Buffer \{\n(.*)\n\}$', item, re.S)
    return m.group(1) if m else item


failures = 0
for item in items(TRUSTED):
    probe = unindent_impl_method(item)
    head = probe.strip().split('\n')[0]
    name = re.search(r'(fn \w+|macro_rules! \w+|impl_Integer\w*!\([^)]*\))', probe)
    label = name.group(1) if name else head
    if probe in UPSTREAM:
        print(f'verbatim            {label}')
    elif label == 'macro_rules! impl_Integer':
        up = re.search(r'macro_rules! impl_Integer \{.*?\n\}', UPSTREAM, re.S).group(0)
        diff = list(difflib.unified_diff(up.split('\n'), probe.split('\n'), 'upstream', 'trusted.rs',
                                         lineterm='', n=1))
        changed = [l for l in diff if l[:1] in '+-' and l[:3] not in ('+++', '---')]
        removed = [l[1:].strip() for l in changed if l.startswith('-') and l[1:].strip()]
        expected_removed = {
            'let mut offset = Self::MAX_STR_LEN - $Unsigned::MAX_STR_LEN;',
            'offset += Unsigned::fmt(', 'self.unsigned_abs(),',
            '(&mut buf[offset..]).try_into().unwrap(),', ');', 'if self < 0 {', 'offset -= 1;',
            "unsafe { buf.get_unchecked_mut(offset).write(b'-') };", '}',
        }
        if set(removed) <= expected_removed:
            print(f'changed (expected)  {label}: signed `write` calls the verified `Signed::fmt`')
            print('\n'.join('    ' + l for l in diff))
        else:
            failures += 1
            print(f'CHANGED             {label}')
            print('\n'.join('    ' + l for l in diff))
    else:
        failures += 1
        print(f'CHANGED             {label}')
print(f'{len(items(TRUSTED))} items, {failures} unexpected changes')
sys.exit(1 if failures else 0)
