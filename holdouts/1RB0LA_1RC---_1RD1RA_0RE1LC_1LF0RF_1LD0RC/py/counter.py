"""The tape of 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC as a binary number N and a spacer number S.

At each sweep (first visit of the right end after a visit of the left end; `c/rounds.c`) the tape after the leading
`111` is a word over x = 0001 (spacer), y = 0001111 (digit 1), z = 0111111 (digit 0). Write it as
s_0 d_1 s_1 d_2 ... d_m s_m (s_i = number of x, d_i digits). Then

    N = sum d_i 2^(i-1),   S = sum s_i 2^i,

and one round (sweep right to left, then left to right) is, as long as no defect word appears,

    right to left:  each x adds 1 to the number formed by the digits to its right (LSB nearest), carries past the
                    last digit are lost:                        N' = (N + S) mod 2^m
    left to right:  spacer s_i moves by d_(i+1) - d_i (each block of 1-digits moves one spacer to the right),
                    and the right end appends x y x:             S' = S - N' + 3 * 2^m,  N' += 2^m,  m' = m + 1

so with a = 3N - 2*2^m, b = 3S - 8*2^m the round is exactly (a, b) -> (a + b, -a), a rotation of order 6.

When a block of 1-digits has no x to its right (Y right before Z in the left code), the machine writes a merged
word: (1,3)(1,9) = 0111 0111111111 stands for x y [-1] z and (3,7) = 0001111111 for y [-1] y, a spacer of -1.
With these values the rotation still holds. Rarer words and the rounds where a digit disappears (m drops by one)
break it; this script lists those rounds.

usage: python3 counter.py ROUNDS_FILE            (ROUNDS_FILE from c/rounds.c)
"""
import re
import sys

VAL = {'(1,3)': ['x'], '(1,9)': ['y', -1, 'z'], '(3,7)': ['y', -1, 'y']}


def parse(s):
    sp, dg = [0], []
    for t in re.findall(r'\(\d+,\d+\)|[xyz]', s):
        for c in VAL.get(t, [t]) if t.startswith('(') else [t]:
            if t.startswith('(') and t not in VAL:
                return None
            if c == 'x':
                sp[-1] += 1
            elif c in ('y', 'z'):
                dg.append(1 if c == 'y' else 0)
                sp.append(0)
            else:
                sp[-1] += c
    return sp, dg


def ab(sp, dg):
    m = len(dg)
    A = 1 << m
    N = sum(d << i for i, d in enumerate(dg))
    S = sum(x << i for i, x in enumerate(sp))
    return m, 3 * N - 2 * A, 3 * S - 8 * A


def main():
    rows = {}
    for line in open(sys.argv[1]):
        t = line.split()
        if len(t) == 3 and t[2].startswith('[3]'):
            rows[int(t[1])] = t[2][3:]
    prev = None
    ok = bad = unknown = 0
    for r in sorted(rows):
        if r < 4:
            continue
        P = parse(rows[r])
        if P is None:
            unknown += 1
            prev = None
            continue
        cur = ab(*P)
        if prev is not None:
            if (prev[0] + 1, prev[1] + prev[2], -prev[1]) == cur:
                ok += 1
            else:
                bad += 1
                print('round %d: (m, a, b) %s -> %s' % (r, prev, cur))
        prev = cur
    print('rotation holds %d times, breaks %d times; %d rounds with other defect words' % (ok, bad, unknown))


if __name__ == '__main__':
    main()
