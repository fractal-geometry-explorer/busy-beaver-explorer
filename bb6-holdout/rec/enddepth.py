import sys, math
import tracecycle as T
cur = []
def hook(marks, label, x):
    if label != "gap": return
    ms = sorted(marks, key=lambda m: m[1]); r = [m for m in ms if m[1] > x]
    if r and r[0][0] == "M" and r[0] is ms[-1]: cur.append(r[0][1] - x - 3)
T.HOOK = hook
rows = []
for n in range(int(sys.argv[1]), int(sys.argv[2])):
    cur.clear(); T.cycle(n)
    ds = cur[1:]
    if ds:
        d = min(ds); w = 2 * n + 6
        rows.append((math.log2(w / max(d, 1)), n, d, len(ds)))
rows.sort(reverse=True)
print("deepest right-end halving (halvings = log2(tape length / closest d)):")
for h, n, d, k in rows[:12]:
    print(f"  n = {n:7d} ({bin(n)[2:]:>19s})  closest d = {d:5d}  halvings {h:5.1f}  end-marker meetings {k}")
# record depth by dyadic band
bands = {}
for h, n, d, k in rows:
    b = 1 << (n.bit_length() - 1)
    if b not in bands or h > bands[b][0]: bands[b] = (h, n, d)
print("\nrecord per range:", ", ".join(f"{b}+: {v[0]:.1f} (n={v[1]}, d={v[2]})" for b, v in sorted(bands.items()) if b >= 256))
