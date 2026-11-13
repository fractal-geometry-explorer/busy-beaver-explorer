"""Is the tape a list of numbers written as blocks of 1s of one residue?  Shared by the G11 batch-4 folders.

usage: tmrun M 1e11 records 100000 > rec.txt
       python3 residue_blocks.py rec.txt SIDE STATE P R [K]

At each record (new cell) on SIDE (L or R) with the head in STATE, the tape (leading and trailing 0s dropped) is
cut into blocks of 1s each followed by its run of 0s.  The record is *regular* when every block except the first and
the last has length = R (mod P) and is followed by exactly one 0.  Prints the counts of regular and irregular records
and the last K regular ones: step, steps since the previous record of this kind, first block, the numbers
m = (length - R) / P of the inner blocks (one character each, [m] when m > 9), last block.
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


def scan(path, side, state, p, r):
    rows, bad, prev = [], 0, 0
    for line in open(path):
        q = line.split(' ', 3)
        if len(q) < 4 or q[1] != side or f'{state}>' not in q[3]:
            continue
        s, tape = int(q[0]), expand(q[3]).strip('0')
        bl = re.findall('(1+)(0*)', tape)
        inner = bl[1:-1]
        if bl and all(len(z) == 1 for _, z in inner) and all(len(o) % p == r for o, _ in inner) and len(bl[0][1]) == 1:
            ms = [(len(o) - r) // p for o, _ in inner]
            rows.append((s, s - prev, len(bl[0][0]), ms, len(bl[-1][0])))
        else:
            bad += 1
        prev = s
    return rows, bad


def digits(ms):
    return ''.join(str(m) if m < 10 else f'[{m}]' for m in ms)


if __name__ == '__main__':
    path, side, state, p, r = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
    k = int(sys.argv[6]) if len(sys.argv) > 6 else 10
    rows, bad = scan(path, side, state, p, r)
    print('regular', len(rows), 'irregular', bad)
    for s, d, a, ms, b in rows[-k:]:
        print(s, d, a, digits(ms), b)
