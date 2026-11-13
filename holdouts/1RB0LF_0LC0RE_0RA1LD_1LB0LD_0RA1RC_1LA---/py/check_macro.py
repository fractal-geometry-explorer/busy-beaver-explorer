"""Checks the block macro machine (blockmm.py) against direct simulation, record by record.

usage: gcc -O2 -o recp ../c/recp.c && ./recp 4000000 3e8 1 100000 > r3e8.txt && python3 check_macro.py r3e8.txt

Each line of recp is a left record: steps, record number, width, the cell under the head, and the tape right of
the head as P-blocks ((10)^D then a single cell i = 1 or o = 0).  The macro machine runs from record 1
(0^inf B> 0 1 1 0, step 4) on its own and must give, at every record, the same step count, head cell and blocks."""
import sys
from blockmm import macro_step


def parse(line):
    head, toks = line.split('|')
    h = head.split()
    bl, D = [], 0
    for t in toks.split():
        if t in 'io':
            bl.append((D, 1 if t == 'i' else 0)); D = 0
        else:
            D = int(t)
    if D:
        bl.append((D, 0))
    return int(h[0]), int(h[1]), int(h[3]), bl


lines = [l for l in open(sys.argv[1]) if '|' in l]
recs = [parse(l) for l in lines]
assert recs[0][1] == 1
cur = ((), recs[0][2], recs[0][3])
steps = recs[0][0]
for st, rn, c, bl in recs[1:]:
    cur, s, _ = macro_step(*cur)
    steps += s
    if (steps, cur[1], cur[2]) != (st, c, bl):
        print('MISMATCH at record', rn, steps, st)
        sys.exit(1)
print('records 1 ..', recs[-1][1], 'agree (steps, head cell, blocks); last step', steps)
