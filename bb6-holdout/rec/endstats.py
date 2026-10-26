"""Right-end and nesting statistics per dyadic range of n (mark model)."""
import sys, collections
import tracecycle as T
LEN = {"G": 3, "M": 2, "W": 2, "B": 3}
cur = {}
W = [0]
def upd(k, v, mode=min):
    cur[k] = v if k not in cur else mode(cur[k], v)
orig = T.round_events
def round_events(w, marks):
    W[0] = w
    return orig(w, marks)
T.round_events = round_events
def hook(marks, label, x):
    ms = sorted(marks, key=lambda m: m[1])
    gaps = sum(1 for m in ms if m[0] == "G")
    upd("gaps at once", gaps, max)
    upd("walls at once", sum(1 for m in ms if m[0] == "W"), max)
    if label == "gap":
        r = [m for m in ms if m[1] > x]
        if r and r[0][0] == "M" and r[0] is ms[-1]:
            upd("d when a gap faces the end marker", r[0][1] - x - 3)
T.HOOK = hook
lo, hi = int(sys.argv[1]), int(sys.argv[2])
bands = []; b = 1
while b < hi: bands.append((b, 2 * b)); b *= 2
res = {}
for n in range(max(lo, 1), hi):
    cur.clear(); T.cycle(n)
    bb = next(x for x in bands if x[0] <= n < x[1])
    for k, v in cur.items():
        mode = max if "at once" in k else min
        key = (bb, k)
        if key not in res: res[key] = (v, n)
        elif (mode is min and v < res[key][0]) or (mode is max and v > res[key][0]): res[key] = (v, n)
keys = ["d when a gap faces the end marker", "gaps at once", "walls at once"]
print("range".ljust(16) + "".join(k.rjust(36) for k in keys))
for bb in bands:
    print(f"{bb[0]}–{bb[1]-1}".ljust(16) + "".join((f"{res[(bb,k)][0]} (n={res[(bb,k)][1]})" if (bb, k) in res else "-").rjust(36) for k in keys))
