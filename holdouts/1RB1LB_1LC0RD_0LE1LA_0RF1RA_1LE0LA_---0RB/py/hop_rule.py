"""The two deep sweeps at a `10` defect of 1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB, checked with the machine's table.

Words x = 111, y = 110, defect T = 10.  Started in B on the first cell, run until the head leaves the string on the left:

  shielded:  P x T G y 0        ->  x102(P, x)  T  x102(y G y, y)  1                       (lean/Hop.lean, `shielded`)
  jump:      P y T y^j x^(a+1) C y 0, C empty or starting with y
                                ->  x102(P y, x)  x^(j+a+1)  T  x102(C y, y)  1            (lean/Hop.lean, `jump`)
  danger:    P y T y^j 0        ->  halts                                                   (lean/Danger.lean)

x102(w, q): word i becomes w[i] xor w[i+1], with q after the end (rule 102).  The exit state is C or E as the first
word is y or x.  Every P of up to 5 words, G of up to 6, j and a up to 4, C of up to 5.  A few seconds.

usage: python3 hop_rule.py
"""
import itertools

TABLE = "1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB"
TR = {}
for i, g in enumerate(TABLE.split('_')):
    for r in range(2):
        c = g[3 * r:3 * r + 3]
        TR['ABCDEF'[i], r] = None if c[0] == '-' else (int(c[0]), 1 if c[1] == 'R' else -1, c[2])
CELLS = {'x': '111', 'y': '110', 'T': '10'}


def enc(ws):
    return ''.join(CELLS[w] for w in ws)


def x102(ws, q):
    v = [w == 'y' for w in ws] + [q == 'y']
    return ''.join('y' if v[i] != v[i + 1] else 'x' for i in range(len(ws)))


def run(cells):
    """B on the first cell; returns (state, cells) when the head leaves on the left, or ('HALT', None)."""
    tape, p, s = [int(c) for c in cells], 0, 'B'
    while 0 <= p < len(tape):
        a = TR[s, tape[p]]
        if a is None:
            return 'HALT', None
        tape[p], p, s = a[0], p + a[1], a[2]
    return s, ''.join(map(str, tape))


def words(n):
    for k in range(n + 1):
        for w in itertools.product('xy', repeat=k):
            yield ''.join(w)


def main():
    tail = enc('xxxx')       # cells after the wall: never read
    n = bad = 0
    for P in words(5):
        for G in words(6):
            st, out = run(enc(P + 'xT' + G + 'y') + '0' + tail)
            want = enc(x102(P, 'x') + 'T' + x102('y' + G + 'y', 'y')) + '1' + tail
            n += 1
            bad += (st, out) != ('C' if (P + 'x')[0] == 'y' else 'E', want)
    print(f"shielded: {n} cases, {bad} mismatches")
    n = bad = 0
    for P in words(5):
        for j in range(5):
            for a in range(4):
                for C in words(4):
                    C = 'y' + C if C else ''
                    for C2 in ([C] if C else ['', 'y']):
                        st, out = run(enc(P + 'yT' + 'y' * j + 'x' * (a + 1) + C2 + 'y') + '0' + tail)
                        want = enc(x102(P + 'y', 'x') + 'x' * (j + a + 1) + 'T' + x102(C2 + 'y', 'y')) + '1' + tail
                        n += 1
                        bad += (st, out) != ('C' if (P + 'y')[0] == 'y' else 'E', want)
    print(f"jump: {n} cases, {bad} mismatches")
    n = halts = 0
    for P in words(5):
        for j in range(8):
            n += 1
            halts += run(enc(P + 'yT' + 'y' * j) + '0' + tail)[0] == 'HALT'
    print(f"danger: {halts} of {n} halt")


if __name__ == '__main__':
    main()
