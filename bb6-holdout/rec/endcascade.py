"""For each n: the d-values of every meeting between a gap and the end marker in the cycle (mark model).
Reports the smallest d per n (after the first round) and the chain of end-marker meetings for the closest cases."""
import sys, json
import tracecycle as T
cur = []
def hook(marks, label, x):
    if label != "gap": return
    ms = sorted(marks, key=lambda m: m[1])
    r = [m for m in ms if m[1] > x]
    if r and r[0][0] == "M" and r[0] is ms[-1]:
        cur.append(r[0][1] - x - 3)
T.HOOK = hook
lo, hi = int(sys.argv[1]), int(sys.argv[2])
close = []
for n in range(lo, hi):
    cur.clear(); T.cycle(n)
    ds = cur[1:] if cur else []
    if ds and min(ds) < 400 and n > 100:
        close.append((min(ds), n, ds))
close.sort()
for d, n, ds in close[:12]:
    print(f"n = {n:7d}  closest d = {d:4d}   end-marker meetings: {ds}")
print(len(close), "cycles with a gap within 400 cells of the end marker (n > 100)")
