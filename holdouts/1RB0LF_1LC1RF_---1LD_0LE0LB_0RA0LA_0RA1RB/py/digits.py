"""Reads `tmrun MACHINE STEPS at D L K` output (the tape each time D is at the left end) and prints the tape as a list
of digits: the tape right of the head is `0 1 1` followed by words `0 1 1` (x) and `0 0 1 1` (y); a digit is a y
followed by its run of x (the first digit is the leading `0 1 1`), and its value counts the y and the x's.
With `check`, also tests the simple-phase rule: the next list is [1, 2] + middle + [last - 1].

  /home/user/w/tmrun 1RB0LF_1LC1RF_---1LD_0LE0LB_0RA0LA_0RA1RB 10000000000 at D L 1000000 | python3 digits.py [check]
"""
import re, sys
from itertools import groupby


def expand(rle):
    out = []
    for t in rle.split():
        if '>' in t:
            t = t.split('>')[1]
        if '^' in t:
            s, n = t.split('^')
            out += [s] * int(n)
        else:
            out.append(t)
    return ''.join(out)


def digits(s):
    s = s.rstrip('0')
    d, c = [], 0
    for m in re.finditer(r'(0+)(1+)', s):
        z, o = len(m.group(1)), len(m.group(2))
        if o != 2 or z > 2:
            raise ValueError('not a digit tape')
        if z == 1:
            c += 1
        else:
            d.append(c)
            c = 1
    d.append(c)
    return d


seq = []
for line in sys.stdin:
    p = line.split(None, 3)
    if len(p) == 4 and p[0].isdigit():
        d = digits(expand(p[3]))
        seq.append((int(p[0]), d))
        print(p[0], len(d), ' '.join(f'{k}^{len(list(g))}' for k, g in groupby(d)))
if 'check' in sys.argv:
    simple = [b == [1, 2] + a[1:-1] + [a[-1] - 1] for (_, a), (_, b) in zip(seq, seq[1:])]
    print(f'{sum(simple)} simple steps, {len(simple) - sum(simple)} others:')
    for ((t0, a), (t1, b)), s in zip(zip(seq, seq[1:]), simple):
        if not s:
            print(f'  step {t0} -> {t1}: {a} -> {b}' if len(a) < 12 else f'  step {t0} -> {t1}: {len(a)} digits -> {len(b)}')
