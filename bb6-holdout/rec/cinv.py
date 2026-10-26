import json, sys
from fractions import Fraction as F
from collections import defaultdict
K = int(sys.argv[1])
rows = [list(map(int, l.split()))[:2] for l in open("../jmin_all22.txt")]
src = open("nrefine.py").read()
src = src.replace("        while gap is not None:\n            g = gap[1]; m = first_right(g)",
                  "        while gap is not None:\n            PROBE(marks, gap, w)\n            g = gap[1]; m = first_right(g)")
ns = {}; exec(compile(src, "nr", "exec"), ns)
stats = defaultdict(lambda: -10**9)
def make_probe(k, rho):
    L = 2 ** (k + 1)
    def off(p): return F(p[1]) - F(p[0]) * (2 * rho + 6) / L
    def PROBE(marks, gap, w):
        cg = off(gap[1]); ag = gap[1][0]
        others = [m for m in marks if m is not gap]
        left = [off(m[1]) - cg for m in others if m[1] < gap[1]]
        right = [off(m[1]) - cg for m in others if m[1] > gap[1]]
        if left: stats["max over passed marks of (c - c_gap)"] = max(stats["max over passed marks of (c - c_gap)"], max(left))
        if right: stats["max over marks ahead of (c_gap - c)"] = max(stats["max over marks ahead of (c_gap - c)"], -min(right))
        ms = sorted(others, key=lambda m: m[1])
        inv = max([off(a[1]) - off(b[1]) for i, a in enumerate(ms) for b in ms[i + 1:] if a[1][0] < b[1][0]], default=-10**9)
        stats["max inversion among marks other than the gap"] = max(stats["max inversion among marks other than the gap"], inv)
        stats["max over marks of (c - c_width)"] = max(stats["max over marks of (c - c_width)"], max(off(m[1]) - off(w) for m in marks))
        stats["min offset of any mark"] = max(stats["min offset of any mark"], -min(off(m[1]) for m in marks))
    return PROBE
for k, rho in rows:
    if k > K: continue
    ns["PROBE"] = make_probe(k, rho)
    ns["cycle"](k, rho)
for key, v in stats.items():
    print(f"{key}: {float(v) if 'min offset' not in key else -float(v):.3f}")
