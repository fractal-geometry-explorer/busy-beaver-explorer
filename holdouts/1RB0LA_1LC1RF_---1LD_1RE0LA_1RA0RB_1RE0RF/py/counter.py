"""The counter of 1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF.

usage (from the repo root):
  gcc -O2 -o /tmp/tmrun tools/c/tmrun.c
  /tmp/tmrun 1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF 1000000000 at A L 100000 > /tmp/al.txt
  python3 holdouts/1RB0LA_1LC1RF_---1LD_1RE0LA_1RA0RB_1RE0RF/py/counter.py /tmp/al.txt

At each time the head is at the left end in state A on `A>0 0`, the tape starts with (110)^p.  Prints how p changes
from one such time to the next, the steps per round / p^2, and what follows the block for each p mod 3.
"""
import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tokl import cells_of, tokenize  # noqa: E402

rows = []
for line in open(sys.argv[1]):
    t = line.split(None, 1)
    if len(t) < 2 or not t[0].isdigit() or not t[1].startswith("A>0 0"):
        continue
    c, _ = cells_of(t[1])
    tk = tokenize(c, {"c": "110", "a": "10"}).split()
    m = re.match(r"c\^(\d+)$", tk[1]) if len(tk) > 1 and tk[0] == "0^2" else None
    if m:
        nxt = tk[2] if len(tk) > 2 else ""
        if nxt == "0" and len(tk) > 3:
            nxt = "0 " + tk[3]
        rows.append((int(t[0]), int(m.group(1)), nxt))
inc = collections.Counter(b[1] - a[1] for a, b in zip(rows, rows[1:]))
print(f"visits: {len(rows)}; first (step, p): {rows[0][:2]}; last: {rows[-1][:2]}; increments of p: {dict(inc)}")
print("steps per round / p^2, last 5:", [round((b[0] - a[0]) / a[1] ** 2, 2) for a, b in zip(rows[-6:], rows[-5:])])
print("what follows (110)^p, by p mod 3, after step 10^6:", dict(collections.Counter((r[1] % 3, r[2]) for r in rows if r[0] > 10 ** 6)))
