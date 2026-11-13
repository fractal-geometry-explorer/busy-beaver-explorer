"""Rules of the block-list dynamics of 1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---, checked by direct simulation.
An event is the head in state A at the left end with the tape starting 001 (A> 00 1...).  Each rule maps an event to
the next one.   python3 listrules.py [N]   (N: largest parameter tried, default 40)"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
M = '1RB0LA_0RC1RD_0LD1RE_1LA0RF_0RD0LD_1RD---'


def w(*parts):
    """('10', 3) -> '101010'; strings as they are."""
    return ''.join(p if isinstance(p, str) else p[0] * p[1] for p in parts)


X = lambda n: w('00', ('10', n), '01')                                    # A> 00 (10)^n 01
Y = lambda a, b: w('00', ('10', 2), ('010', a), ('10', b), '01')           # A> 00 1010 (010)^a (10)^b 01
TAIL = w(('01', 2), '001')
Z = lambda a, b: w('00', ('10', 2), ('010', a), '00', ('10', b), TAIL)     # A> 00 1010 (010)^a 00 (10)^b (01)^2 00 1
RULES = [
    ('X(2k) -> Y(k-1, 3k)', lambda k: X(2 * k), lambda k: Y(k - 1, 3 * k), 2),
    ('Y(2i+1, b) -> X(b + 3i + 7)', lambda i, b: Y(2 * i + 1, b), lambda i, b: X(b + 3 * i + 7), (0, 1)),
    ('X(2k+1) -> Z(k, 3k-2)', lambda k: X(2 * k + 1), lambda k: Z(k, 3 * k - 2), 2),
    ('Z(2i+1, b) -> A> 00 (10)^(3i+5) 00 (10)^(b-1) (01)^5 00 1',
     lambda i, b: Z(2 * i + 1, b), lambda i, b: w('00', ('10', 3 * i + 5), '00', ('10', b - 1), ('01', 5), '001'), (0, 2)),
    ('Z(2i, 2j) -> A> 00 (10)^(3i+4) (010)^j 00 (10)^(3j+1) (01)^2 00 1',
     lambda i, j: Z(2 * i, 2 * j), lambda i, j: w('00', ('10', 3 * i + 4), ('010', j), '00', ('10', 3 * j + 1), TAIL), (1, 2)),
    ('Z(2i, 2j+1) -> A> 00 (10)^(3i+4) (010)^j (10)^(3j+6) 01',
     lambda i, j: Z(2 * i, 2 * j + 1), lambda i, j: w('00', ('10', 3 * i + 4), ('010', j), ('10', 3 * j + 6), '01'), (1, 2)),
]


def main(N):
    d = tempfile.mkdtemp()
    exe = os.path.join(d, 'evrun2')
    subprocess.check_call(['gcc', '-O2', '-o', exe, os.path.join(HERE, '..', '..', '1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---',
                                                                  'c', 'evrun2.c')])
    p = subprocess.Popen([exe, M, 'A', '001', '1000000000'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
                         bufsize=1)
    allok = True
    for name, start, end, lo in RULES:
        n = bad = 0
        args = [(k,) for k in range(lo, N)] if isinstance(lo, int) else \
            [(i, j) for i in range(lo[0], N // 2) for j in range(lo[1], N)]
        for a in args:
            p.stdin.write(start(*a) + '\n')
            f = p.stdout.readline().split()
            n += 1
            if len(f) < 2 or f[1] != end(*a).rstrip('0'):
                bad += 1
                if bad < 4:
                    print('   differs', a, f[:1])
        allok &= bad == 0
        print('%-70s %4d cases, %d differ' % (name, n, bad))
    return allok


if __name__ == '__main__':
    sys.exit(0 if main(int(sys.argv[1]) if len(sys.argv) > 1 else 40) else 1)
