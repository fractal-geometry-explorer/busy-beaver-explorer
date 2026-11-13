"""Read a log of `tmrun 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB T at E L 400` and print, for each event (E at the
left end on blank), the step, the left block N, and the block M after the `1^3`; then the phases where M is constant.

usage: python3 phases.py LOG
"""
import sys


def cells(s):
    out = []
    for tok in s.split():
        if ">" in tok:
            tok = tok.split(">")[1]
        if "^" in tok:
            c, n = tok.split("^")
            out += [c] * int(n)
        else:
            out.append(tok)
    return "".join(out).strip("0")


rows = []
seen = set()
for line in open(sys.argv[1]):
    p = line.split(None, 1)
    if len(p) != 2 or not p[0].isdigit():
        continue
    c = cells(p[1])
    if c in seen:
        continue
    seen.add(c)
    b = [len(x) for x in c.split("0") if x]
    if len(b) >= 3 and b[1] == 3:
        rows.append((int(p[0]), b[0], b[2], len(c)))
for t, N, M, w in rows:
    print(t, "N", N, "M", M, "width", w)
print()
cur = None
for t, N, M, w in rows:
    if M != cur:
        print(f"from step {t}: M = {M}, N = {N}")
        cur = M
