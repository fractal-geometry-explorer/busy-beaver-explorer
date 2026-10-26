"""How cycles change with n (mark model): rounds per cycle, marks at once, blocks at once, and how often each kind
of event happens, per dyadic range of n."""
import sys, re, collections
import tracecycle as T
state = {}
def hook(marks, label, x):
    nm = len(marks); nb = sum(1 for m in marks if m[0] == "B")
    state["marks"] = max(state.get("marks", 0), nm); state["blocks"] = max(state.get("blocks", 0), nb)
T.HOOK = hook
def kinds(ev):
    out = []
    for i, e in enumerate(ev):
        k = re.sub(r"[0-9]+", "", e.split(" d=")[0]).replace("G/M", "").strip()
        k = {"swap": "swap", "merge": "merge"}.get(k.split()[0], k)
        if e.startswith("shift→") and i > 0:
            prev = ev[i - 1]
            src = "wall" if " meets W" in prev else ("block" if " passes B" in prev else "?")
            k = f"shift from {src} → " + {"M": "marker", "W": "wall", "B": "block", "e": "end"}[e[6]]
        out.append(k)
    return out
lo, hi = int(sys.argv[1]), int(sys.argv[2])
bands = []; b = 1
while b < hi: bands.append((b, 2 * b)); b *= 2
stats = {bb: collections.Counter() for bb in bands}; mx = {bb: collections.Counter() for bb in bands}
first = {}
for n in range(max(lo, 1), hi):
    state.clear(); m, out = T.cycle(n)
    bb = next(x for x in bands if x[0] <= n < x[1])
    mx[bb]["rounds"] = max(mx[bb]["rounds"], len(out)); mx[bb]["marks"] = max(mx[bb]["marks"], state["marks"])
    mx[bb]["blocks"] = max(mx[bb]["blocks"], state["blocks"]); stats[bb]["cycles"] += 1; stats[bb]["rounds"] += len(out)
    for (w, mk), ev in out:
        for k in kinds(ev):
            stats[bb][k] += 1; first.setdefault(k, n)
print("range".ljust(14), "mean rounds".rjust(11), "max rounds".rjust(10), "max marks".rjust(9), "max blocks".rjust(10))
for bb in bands:
    s = stats[bb]
    if not s["cycles"]: continue
    print(f"{bb[0]}–{bb[1]-1}".ljust(14), f"{s['rounds']/s['cycles']:.1f}".rjust(11), str(mx[bb]['rounds']).rjust(10), str(mx[bb]['marks']).rjust(9), str(mx[bb]['blocks']).rjust(10))
tot = collections.Counter()
for bb in bands: tot.update(stats[bb])
print()
for k, v in sorted(tot.items(), key=lambda kv: -kv[1]):
    if k in ("cycles", "rounds"): continue
    print(f"{k:32s} {v:10d}   first at n = {first[k]}")
