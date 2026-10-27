"""Classify route entries by why no coset point can halt through them (October 23).
For each entry: R1 takes the values R0 + g Z on the coset (g = gcd of the y-coefficients).  (a) if no 16^p r (p >= 0,
r in the closing set) is congruent to R0 mod g, nothing can close: 'R-congruence'.  Otherwise, for each consistent
(p, r), the L1 congruence on the R1 = 16^p r line: if inconsistent for every (p, r): 'L-congruence'.  Otherwise the
exact enumeration over widths decides: 'enumeration'.  usage: pinclass.py kmin < S-lines"""
import sys, re, math
sys.path.insert(0, '../rt3'); import pinforms as P
kmin = int(sys.argv[1])
cnt = {'R-congruence': 0, 'L-congruence': 0, 'enumeration (0 found)': 0, 'candidates': 0}
gs = {}
for line in sys.stdin:
    m = re.match(r'S ([0-9.]+) t=[0-9.]+ bits (\d+) coset (-?\d+) (-?\d+) (-?\d+) (-?\d+) (-?\d+) forms B (-?\d+) (-?\d+) (-?\d+) (\d+) C (-?\d+) (-?\d+) (-?\d+) (\d+) W (-?\d+) (-?\d+) (-?\d+) (\d+) \| (.*)', line)
    if not m: continue
    ceil = float(m.group(1)); v = list(map(int, m.groups()[1:19])); bits, x0m, x0E, B00, B10, B11 = v[:6]; Bf, Cf, Wf = tuple(v[6:10]), tuple(v[10:14]), tuple(v[14:18])
    kh = int(math.floor(ceil + 6.38)) + 1
    if kh <= kmin: continue
    b = P.yforms(x0m, x0E, B00, B10, B11, Bf); c = P.yforms(x0m, x0E, B00, B10, B11, Cf); w = P.yforms(x0m, x0E, B00, B10, B11, Wf)
    R = [w[i] - c[i] - (1 if i == 0 else 0) for i in range(3)]; L = [147 * b[i] + 280 * w[i] - 392 * c[i] - (578 if i == 0 else 0) for i in range(3)]
    g = math.gcd(R[1], R[2]); r0 = R[0] % g if g else R[0]
    v2 = (g & -g).bit_length() - 1 if g else 99
    gs[v2] = gs.get(v2, 0) + 1
    rcons = [(p, r, cls, M) for p in range(0, 40) for r, cls, M in P.CLOSE if 16 ** p * r < (1 << kh) and (g == 0 or (16 ** p * r - R[0]) % g == 0)]
    if not rcons: cnt['R-congruence'] += 1; continue
    lcons = False
    for p, r, cls, M in rcons:
        gg, s, t = P.egcd(R[1], R[2]); rhs = 16 ** p * r - R[0]
        Y0, Y1 = s * (rhs // gg), t * (rhs // gg); d0, d1 = R[2] // gg, -R[1] // gg
        Lc = L[0] + L[1] * Y0 + L[2] * Y1; Ld = L[1] * d0 + L[2] * d1
        Mod = 64 ** p * M; want = (64 ** p * cls - Lc) % Mod
        h = math.gcd(Ld % Mod, Mod)
        if want % h == 0: lcons = True; break
    if not lcons: cnt['L-congruence'] += 1; continue
    out, _ = P.candidates(x0m, x0E, B00, B10, B11, Bf, Cf, Wf, kmin, kh)
    if out: cnt['candidates'] += 1
    else: cnt['enumeration (0 found)'] += 1
print('entries by what excludes them:', cnt)
print('2-adic valuation of the step g of R1 on the coset (count of entries):', dict(sorted(gs.items())))
