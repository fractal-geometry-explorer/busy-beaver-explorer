"""The b-map of 1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA, by direct simulation (C helper evrun2 of
../../1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/c, on the mirror image of the machine).

    X(a, b) = 0^inf (10)^a 1^b C> 0^inf        Y(a, b) = 0^inf (10)^a 1^b 0 C> 0^inf     (head at the right end)

For a large enough the next such event is X(a - d(b), f(b)) (b even) or Y(a - d(b), f(b)) (b odd), with f, d
independent of a; and from Y(a, b) the next event is Y(a - d(b) - 2, f(b) + 4) for b even, X(a - d(b), f(b) + 2) for
b odd.   python3 bmap.py B [A]  checks b < B (a = 4b + 100 and a = 4b + 100 + A) and prints the table."""
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
M = '1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA'
MIRROR = ''.join({'L': 'R', 'R': 'L'}.get(c, c) for c in M)
d = tempfile.mkdtemp()
exe = os.path.join(d, 'evrun2')
subprocess.check_call(['gcc', '-O2', '-o', exe, os.path.join(HERE, '..', '..', '1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---',
                                                              'c', 'evrun2.c')])
P = subprocess.Popen([exe, MIRROR, 'C', '0', '100000000000'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
                     bufsize=1)
RX = re.compile(r'(0|00)(1+)((01)*)$')


def nxt(kind, a, b):
    """Next event from X(a, b) or Y(a, b): (kind', a', b', steps) or None if it has another form."""
    P.stdin.write(('0' if kind == 'X' else '00') + '1' * b + '01' * a + '\n')
    r = P.stdout.readline().split()
    x = r[1] if len(r) > 1 else ''
    mm = RX.match(x)
    if not mm:
        return None
    return ('X' if mm.group(1) == '0' else 'Y', len(mm.group(3)) // 2, len(mm.group(2)), int(r[0]))


if __name__ == '__main__':
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    A = int(sys.argv[2]) if len(sys.argv) > 2 else 37
    bad = 0
    for b in range(B):
        a = 4 * b + 100
        x1, x2, y1 = nxt('X', a, b), nxt('X', a + A, b), nxt('Y', a, b)
        f, dd = x1[2], a - x1[1]
        ok = x1[0] == ('X' if b % 2 == 0 else 'Y') and x2[:3] == (x1[0], x1[1] + A, f)
        ok &= y1[:3] == (('Y', a - dd - 2, f + 4) if b % 2 == 0 else ('X', a - dd, f + 2))
        bad += not ok
        print(b, 'f', f, 'd', dd, '' if ok else 'DIFFERS %r %r %r' % (x1, x2, y1))
    print('b < %d: %d differ' % (B, bad))
    sys.exit(1 if bad else 0)
