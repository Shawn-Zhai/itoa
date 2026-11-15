#!/usr/bin/env python3
"""Check that the trusted code in itoa/src/trusted.rs is upstream's code (../src/lib.rs), and that
the shells around it, now verified, keep upstream's statements.

- T3 `slice_buffer_to_str`: the body is upstream's body, verbatim.
- T1 `buffer_of`: the body is upstream's cast from `Buffer::format`, with `self.bytes` passed in
  as `bytes`.
- `Buffer::format` (verified): upstream's body, with the cast replaced by a call to `buffer_of`.
- The `write` methods (verified): upstream's bodies, except the signed `write`, whose formatting
  moved into the verified `Signed::fmt` in Claude's first pass.

Ghost code (`proof { ... }` blocks) and comments are ignored. Usage: python3 check_trusted.py
(from verus_fixed/)."""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
UPSTREAM = open(os.path.join(HERE, '..', 'src', 'lib.rs')).read()
TRUSTED = open(os.path.join(HERE, 'itoa', 'src', 'trusted.rs')).read()
LIB = open(os.path.join(HERE, 'itoa', 'src', 'lib.rs')).read()


def body(text, signature, nth=0):
    """Statements of the body of the `nth` function whose header contains `signature`
    (declarations without a body, such as trait methods, are skipped)."""
    def has_body(s):
        depth = 0  # parentheses and brackets; a `;` inside them (array types) does not end the item
        for c in text[s:]:
            depth += {'(': 1, '[': 1, ')': -1, ']': -1}.get(c, 0)
            if depth == 0 and c in '{;':
                return c == '{'
    starts = [m.start() for m in re.finditer(re.escape(signature), text)]
    start = [s for s in starts if has_body(s)][nth]
    i = text.index('{', start)
    depth, j = 0, i
    while True:
        depth += {'{': 1, '}': -1}.get(text[j], 0)
        if depth == 0:
            break
        j += 1
    src = text[i + 1:j]
    src = re.sub(r'proof \{.*?\n\s*\}\n', '', src, flags=re.S)  # ghost blocks
    lines = [re.sub(r'\s*//.*$', '', l).strip() for l in src.split('\n')]
    return [l for l in lines if l]


failures = 0


def check(label, ok, got, want):
    global failures
    print(f'{"ok      " if ok else "CHANGED "} {label}')
    if not ok:
        failures += 1
        print('    got: ', got)
        print('    want:', want)


up_format = body(UPSTREAM, 'pub fn format<I: Integer>')
up_slice = body(UPSTREAM, 'unsafe fn slice_buffer_to_str')
up_write_unsigned = body(UPSTREAM, 'fn write(self, buf: &mut Self::Buffer) -> &str', 0)
up_write_size = body(UPSTREAM, 'fn write(self, buf: &mut Self::Buffer) -> &str', 2)

# T3: verbatim.
got = body(TRUSTED, 'unsafe fn slice_buffer_to_str')
check('T3 slice_buffer_to_str: upstream body, verbatim', got == up_slice, got, up_slice)

# T1: the cast of upstream's `format`.
got = body(TRUSTED, 'fn buffer_of<I: Integer>')
want = [up_format[0].replace('self.bytes', 'bytes'), 'unsafe { &mut *buf_ptr }']
ok = got == want and 'unsafe { &mut *buf_ptr }' in up_format[1]
check("T1 buffer_of: upstream's cast from Buffer::format", ok, got, want)

# Verified `format`: upstream's statements, with the cast replaced by `buffer_of`.
got = body(LIB, 'pub fn format<I: Integer>')
want = [up_format[1].replace('unsafe { &mut *buf_ptr }', 'buffer_of::<I>(&mut self.bytes)')] + up_format[2:]
check('Buffer::format (verified): upstream body, the cast moved to buffer_of', got == want, got, want)

# Verified `write` methods.
got = body(LIB, 'fn write(self, buf: &mut Self::Buffer) -> (result: &str)', 0)
check('unsigned write (verified): upstream body', got == up_write_unsigned, got, up_write_unsigned)
got = body(LIB, 'fn write(self, buf: &mut Self::Buffer) -> (result: &str)', 1)
want = ['let offset = Signed::fmt(self, buf);', up_write_unsigned[-1]]
check('signed write (verified): calls Signed::fmt (Claude, first pass), then upstream tail', got == want, got,
      want)
got = body(LIB, 'fn write(self, buf: &mut Self::Buffer) -> (result: &str)', 2)
check('usize/isize write (verified): upstream body', got == up_write_size, got, up_write_size)

print(f'{failures} unexpected changes')
sys.exit(1 if failures else 0)
