"""The macro configuration of 1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF at the right end of the tape.

usage: tmrun M 1e11 records 100000 > rec.txt;  python3 digits.py rec.txt [K]

At each record (new cell) on the right in state E, tests whether the tape is  1^a 0 (1^(4m+1) 0)* 1^b E>0  (every
block of 1s between the first and the last has length 1 mod 4 and is followed by a single 0), counts the records
that are and are not, and prints the last K regular ones as: step, steps since the previous E record, the digits m
(one character each, [m] when m > 9), b.
"""
import re
import sys


def expand(t):
    cells = []
    for tok in t.split():
        if '>' in tok:
            tok = tok[2:]
        if '^' in tok:
            c, n = tok.split('^')
            cells += [int(c)] * int(n)
        else:
            cells.append(int(tok))
    return ''.join(map(str, cells))


def main(path, k):
    ok = bad = 0
    rows, prev = [], 0
    for line in open(path):
        p = line.split(' ', 3)
        if len(p) < 4 or p[1] != 'R' or ' E>' not in ' ' + p[3]:
            continue
        s, tape = int(p[0]), expand(p[3]).lstrip('0')
        bl = re.findall('(1+)(0*)', tape)
        if all(len(z) == 1 for _, z in bl) and all(len(o) % 4 == 1 for o, _ in bl[1:-1]):
            ok += 1
            d = ''.join(str(m) if m < 10 else f'[{m}]' for m in ((len(o) - 1) // 4 for o, _ in bl[1:-1]))
            rows.append((s, s - prev, d, len(bl[-1][0])))
        else:
            bad += 1
        prev = s
    print('regular', ok, 'irregular', bad)
    for s, dd, d, b in rows[-k:]:
        print(s, dd, d, b)


if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 10)
