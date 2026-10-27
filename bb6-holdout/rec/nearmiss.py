"""Closest approaches between neighbouring marks over whole cycles (mark model), at every moment a rule is chosen.
Separation s = single stripe cells between two neighbouring marks (0 = touching). Pairs are recorded with the phase
(gap, shift or packet) and whether the pair lies left or right of the head position."""
import sys, json
import tracecycle as T
LEN = {"G": 3, "M": 2, "W": 2, "B": 3}
best = {}
CUR = [0]
def hook(marks, label, x):
    ms = sorted(marks, key=lambda m: m[1])
    for a, b in zip(ms, ms[1:]):
        s = b[1] - (a[1] + LEN[a[0]])
        side = "L" if b[1] <= x else ("R" if a[1] >= x else "X")
        key = f"{label}:{a[0]}{b[0]}:{side}"
        if key not in best or s < best[key][0]:
            best[key] = (s, CUR[0])
T.HOOK = hook
lo, hi = int(sys.argv[1]), int(sys.argv[2])
for n in range(lo, hi):
    CUR[0] = n; T.cycle(n)
json.dump(best, open(sys.argv[3], "w"))
for k, v in sorted(best.items(), key=lambda kv: kv[1][0]): print(f"{k:16s} min {v[0]:6d}  (n = {v[1]})")
