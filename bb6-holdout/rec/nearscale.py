"""Per dyadic range of n: the closest approach in the two halting arrangements, plus the other contacts that would
leave the rules. Measured at the moment the relevant rule is chosen (mark model)."""
import sys, json
import tracecycle as T
LEN = {"G": 3, "M": 2, "W": 2, "B": 3}
KEYS = {
  "A: wall reached by a packet, marker after it": None,   # s between the wall and the next marker (danger at 2)
  "B: wall reached by a packet, marker before it": None,  # danger at 0
  "C: marker reached by a packet, wall before it": None,  # danger at 0 (no rule)
  "D: wall reached by a shift, marker after it": None,    # danger at 0
  "E: block reached by a shift, wall after it": None,     # danger at 0
  "F: block reached by the gap, gap before it": None,     # danger at 0
}
cur = {}
def upd(k, s):
    if k not in cur or s < cur[k]: cur[k] = s
def nb(ms, i, step):
    j = i + step
    return ms[j] if 0 <= j < len(ms) else None
def sep(a, b): return b[1] - (a[1] + LEN[a[0]])
def hook(marks, label, x):
    ms = sorted(marks, key=lambda m: m[1])
    if label == "packet":
        left = [i for i, m in enumerate(ms) if m[1] < x and m[0] != "M"]
        if left:
            i = left[-1]; m = ms[i]
            if m[0] == "W":
                r = nb(ms, i, 1); l = nb(ms, i, -1)
                if r and r[0] == "M": upd("A: wall reached by a packet, marker after it", sep(m, r))
                if l and l[0] == "M": upd("B: wall reached by a packet, marker before it", sep(l, m))
        # markers crossed by the packet: each with a wall right before it
        for i, m in enumerate(ms):
            if m[0] == "M" and m[1] < x:
                l = nb(ms, i, -1)
                if l and l[0] == "W" and all(mm[0] == "M" for mm in ms if l[1] < mm[1] < x):
                    upd("C: marker reached by a packet, wall before it", sep(l, m))
    if label == "shift":
        r = [m for m in ms if m[1] > x]
        if r:
            k = r[0]; i = ms.index(k); nxt = nb(ms, i, 1)
            if k[0] == "W" and nxt and nxt[0] == "M": upd("D: wall reached by a shift, marker after it", sep(k, nxt))
            if k[0] == "B" and nxt and nxt[0] == "W": upd("E: block reached by a shift, wall after it", sep(k, nxt))
    if label == "gap":
        r = [m for m in ms if m[1] > x]
        if r and r[0][0] == "B": upd("F: block reached by the gap, gap before it", r[0][1] - (x + 3))
T.HOOK = hook
lo, hi = int(sys.argv[1]), int(sys.argv[2])
rng = {}
N = max(lo, 1)
bands = []
b = 1
while b < hi: bands.append((b, 2 * b)); b *= 2
res = {}
for n in range(lo, hi):
    cur.clear(); T.cycle(n)
    band = next(bb for bb in bands if bb[0] <= max(n, 1) < bb[1])
    for k, v in cur.items():
        key = (band, k)
        if key not in res or v < res[key][0]: res[key] = (v, n)
names = list(KEYS)
print("n range".ljust(16) + "".join(k[:1].center(12) for k in names))
for band in bands:
    row = f"{band[0]}–{band[1]-1}".ljust(16)
    for k in names:
        v = res.get((band, k)); row += (f"{v[0]}" if v else "-").center(12)
    print(row)
print("\n".join(names))
