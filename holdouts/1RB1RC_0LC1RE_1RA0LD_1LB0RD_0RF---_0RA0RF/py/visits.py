"""Which visits of the right end are instances of the Lean theorems `dec_last` and `dec_general`.

Input: the output of `tmrun MACHINE STEPS at A R K` (the tape each time the head, in state A, is at the right end).
For each visit the sweep is followed block by block (lean/Rules.lean: `p_pass` crosses an odd block behind 00, the
sweep stops at an odd block behind 000 (`p_stop_odd`), at an even block (`p_stop_even`) or at the left end, and halts
at an odd block behind a single 0 (`p_halt`)).  A visit is an instance of `dec_general` when it stops at an odd block
1^(2a+1) behind 000 with a >= 1, every block it crosses before has length >= 7 and the last block has length >= 6;
of `dec_last` when the last block itself is the one behind 000.

usage: tmrun MACHINE 1000000000 at A R 100000000 > ar.txt && python3 visits.py ar.txt
"""
import sys
from collections import Counter


def parse(toks):
    blocks, gaps = [], []
    for t in toks:
        if '>' in t:
            break
        n = int(t[2:]) if '^' in t else 1
        (blocks if t.startswith('1') else gaps).append(n)
    if len(gaps) == len(blocks):
        blocks.append(0)
    return blocks, gaps


def classify(b, g):
    n = len(b) - 1
    e = list(b)
    e[-1] += 1                      # A writes one more 1 before the sweep starts
    i = n
    while e[i] % 2 == 1 and i > 0 and g[i - 1] == 2:
        i -= 1
    if e[i] % 2 == 0:
        return 'stop at an even block'
    if i == 0:
        return 'stop at the left end'
    if g[i - 1] == 1:
        return 'HALT'
    if i == n:
        return 'dec_last' if b[n] >= 2 else 'stop, last block short'
    if e[i] >= 3 and all(e[j] >= 7 for j in range(i + 1, n)) and b[n] >= 6:
        return 'dec_general'
    return 'stop at an odd block behind 000, short blocks'


def main():
    c = Counter()
    for line in open(sys.argv[1]):
        p = line.split()
        if p[0] in ('running', 'halted'):
            break
        c[classify(*parse(p[1:]))] += 1
    for k, v in c.most_common():
        print(f"{v:8d}  {k}")
    print(f"{sum(c.values()):8d}  visits")


if __name__ == '__main__':
    main()
