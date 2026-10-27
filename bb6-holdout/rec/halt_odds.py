"""Heuristic odds of a halt beyond 2^45, calibrated on the exhaustive data.
Only top-running integers (class still open one digit below the top) can halt. For each bit length b the run lists
how many there are and how many halvings of the right-end distance each reaches; a halt needs about log2(n) of them."""
import re, sys, math
L = open(sys.argv[1]).read()
hists = [dict((int(a), int(b)) for a, b in re.findall(r"(\d+):(\d+)", line)) for line in re.findall(r"halvings reached by the direct runs \(floor\):(.*)", L)]
opens = [int(x) for x in re.findall(r"direct runs of the (\d+) open-class members", L)]
print(" digits  candidates  share >=6   ratio per halving (from 6 up)")
rows = []
for i, h in enumerate(hists):
    b = i + 2                                    # the depth-k line covers integers with k+1 digits; depth starts at 1
    tot = sum(h.values())
    if tot < 20000: continue
    ge = {x: sum(c for y, c in h.items() if y >= x) for x in range(0, 64)}
    xs = [x for x in range(6, 64) if ge[x] >= 5]
    # least-squares slope of log(ge[x]) for x >= 6
    if len(xs) >= 3:
        mx = sum(xs) / len(xs); my = sum(math.log(ge[x]) for x in xs) / len(xs)
        sl = sum((x - mx) * (math.log(ge[x]) - my) for x in xs) / sum((x - mx) ** 2 for x in xs)
        r = math.exp(-sl); rows.append((b, tot, ge[6] / tot, r))
        print(f"  {b:2d}     {tot:9d}    {ge[6] / tot:.2e}      {r:.2f}   (tail to {max(xs)} halvings)")
b0, tot0, p6, r = rows[-1]
rmin = min(x[3] for x in rows[-5:])
growth = (rows[-1][1] / rows[-6][1]) ** (1 / 5)
print(f"candidates grow {growth:.3f}x per digit; tail ratio r = {r:.2f} (smallest of the last five fits: {rmin:.2f})")
for rr in (r, rmin):
    total = 0.0
    for b in range(46, 400):
        cand = tot0 * growth ** (b - b0)          # top-running integers with b digits
        need = b - 1                               # halvings to bring the distance from about 2n down to 2
        total += cand * p6 * rr ** (-(need - 6))
    print(f"  with r = {rr:.2f}: expected number of halting integers above 2^45 (all n) ~ {total:.1e}; "
          f"along the trajectory (it visits ~0.24 of them) ~ {0.24 * total:.1e}")
