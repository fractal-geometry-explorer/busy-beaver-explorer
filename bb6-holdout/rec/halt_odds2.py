"""Joint fit  log N(b, x) = a + b*log G - x*log r  over bit lengths b and halvings x >= 6, where N(b, x) is the number of
top-running integers with b digits whose right-end distance gets at least x halvings closer to the end.
A halt at b digits needs x ~ b - 1, so the expected number of halting integers there is exp(a) * G^b * r^-(b-1)."""
import re, sys, math
L = open(sys.argv[1]).read()
hists = [dict((int(a), int(b)) for a, b in re.findall(r"(\d+):(\d+)", line)) for line in re.findall(r"halvings reached by the direct runs \(floor\):(.*)", L)]
pts = []
for i, h in enumerate(hists):
    b = i + 2
    ge = {x: sum(c for y, c in h.items() if y >= x) for x in range(64)}
    for x in range(6, 64):
        if ge[x] >= 5 and b >= 22: pts.append((b, x, math.log(ge[x])))
n = len(pts)
# least squares for y = a + c1*b + c2*x
Sb = sum(p[0] for p in pts); Sx = sum(p[1] for p in pts); Sy = sum(p[2] for p in pts)
Sbb = sum(p[0]**2 for p in pts); Sxx = sum(p[1]**2 for p in pts); Sbx = sum(p[0]*p[1] for p in pts)
Sby = sum(p[0]*p[2] for p in pts); Sxy = sum(p[1]*p[2] for p in pts)
import itertools
M = [[n, Sb, Sx], [Sb, Sbb, Sbx], [Sx, Sbx, Sxx]]; v = [Sy, Sby, Sxy]
def solve(M, v):
    M = [row[:] + [vv] for row, vv in zip(M, v)]
    for c in range(3):
        p = max(range(c, 3), key=lambda r: abs(M[r][c])); M[c], M[p] = M[p], M[c]
        for r in range(3):
            if r != c:
                f = M[r][c] / M[c][c]; M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    return [M[i][3] / M[i][i] for i in range(3)]
a, c1, c2 = solve(M, v)
G, r = math.exp(c1), math.exp(-c2)
res = [p[2] - (a + c1 * p[0] + c2 * p[1]) for p in pts]
print(f"{n} points (b = 22..{max(p[0] for p in pts)}, x up to {max(p[1] for p in pts)}): G = {G:.3f} per digit, r = {r:.2f} per halving, "
      f"rms residual {math.sqrt(sum(e*e for e in res)/n):.2f} (natural log)")
print(f"per-digit factor for a halt, G/r = {G / r:.3f}")
tot = sum(math.exp(a + c1 * b + c2 * (b - 1)) for b in range(46, 2000))
print(f"expected number of halting integers above 2^45 (all n): {tot:.1e};  along the trajectory (~0.24 of them): {0.24 * tot:.1e}")
for dr in (0.5, 1.0):
    rr = r - dr; tot2 = sum(math.exp(a + c1 * b - math.log(rr) * (b - 1)) for b in range(46, 2000))
    print(f"   if the tail ratio were {rr:.2f} instead: {tot2:.1e}")
