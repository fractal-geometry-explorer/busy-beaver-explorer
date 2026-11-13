"""Splitting steps of 1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA.

usage (from the repo root):
  gcc -O2 -o /tmp/tmrun tools/c/tmrun.c
  /tmp/tmrun 1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA 1000000000 at E L 1000000 > /tmp/el.txt
  python3 holdouts/1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA/py/splits.py /tmp/el.txt

At each left-end visit in state E the tape is `E>0 1^x 0 0 1^y ...`.  Counts the consecutive visits that are a
splitting step (x' = ceil(2x/3), y' = y + x - x' + 1, the rest unchanged; the new second block may be written
`1 0 1^(y'-2)`) and prints the cost of the last ones.
"""
import re
import sys


def blocks(s):
    out, cur = [], 0
    for k in s.split():
        if k.startswith("1"):
            cur += int(k[2:]) if "^" in k else 1
        elif k == "0":
            out.append(cur)
            cur = 0
        else:
            return None
    out.append(cur)
    return out


rows = []
for line in open(sys.argv[1]):
    t = line.split()
    if len(t) < 2 or not t[0].isdigit():
        continue
    m = re.match(r"E>0 1\^(\d+) 0\^2 (.*)", " ".join(t[1:]))
    if m:
        rows.append((int(t[0]), int(m.group(1)), blocks(m.group(2))))
ok, other, cost = 0, 0, []
for (s, x, r), (s2, x2, r2) in zip(rows, rows[1:]):
    y2 = r[0] + x - x2 + 1 if r else None
    if r and r2 and x2 == -(-2 * x // 3) and (r2 == [y2] + r[1:] or r2 == [1, y2 - 2] + r[1:]):
        ok += 1
        cost.append((x, s2 - s))
    else:
        other += 1
print(f"left-end visits: {len(rows)}; splitting steps: {ok}; other: {other}")
print("last splits (x, steps, steps/x^2):", [(x, c, round(c / x ** 2, 3)) for x, c in cost[-6:]])
