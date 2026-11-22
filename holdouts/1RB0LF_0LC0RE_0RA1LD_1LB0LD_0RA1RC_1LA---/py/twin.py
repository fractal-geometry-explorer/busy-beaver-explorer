"""Checks the block macro machine (blockmm.py) on the twin 1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---, which is this
table mirrored and started in state D (lean/Twin29537.lean), against a direct simulation, record by record.

usage: gcc -O2 -o recp ../c/recp.c && ./recp 4000000 3e8 1 100000 D > twin3e8.txt && python3 twin.py twin3e8.txt

The macro machine starts at the twin's record 6 (step 157, `twin_reach157` in Lean:
0^inf B> 0 (10)^3 0 0 (10) 1 (10) 1 (10) 1 (10)) and must give the same step count, head cell and blocks at every
later record of the file."""
import sys
from blockmm import macro_step
from check_macro import parse

recs = [parse(l) for l in open(sys.argv[1]) if '|' in l]
st0, rn, c, bl = recs[5]
assert (st0, rn, c, bl) == (157, 6, 0, [(3, 0), (0, 0), (1, 1), (1, 1), (1, 1), (1, 0)]), recs[5]
cur, steps = ((), c, bl), st0
for st, rn, c, bl in recs[6:]:
    cur, s, _ = macro_step(*cur)
    steps += s
    if (steps, cur[1], cur[2]) != (st, c, bl):
        print('MISMATCH at record', rn, steps, st)
        sys.exit(1)
print('twin records 6 ..', recs[-1][1], 'agree (steps, head cell, blocks); last step', steps)
