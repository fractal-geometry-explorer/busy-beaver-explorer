"""Exact halting candidates for GMM states on a line alpha*m - beta*E = gamma (the machine's first segment is
2m - E = -7), for every entry in S-lines: each (p, r) pins one point of the line; keep those in the coset with L1 in class.
usage: pinline.py alpha beta gamma kmin < S-lines"""
import sys, re, math
sys.path.insert(0, '../rt3'); import pinforms as P
al, be, ga, kmin = map(int, sys.argv[1:5])
nent = 0; npts = 0; cands = []; nline = 0
for line in sys.stdin:
    m = re.match(r'S ([0-9.]+) t=[0-9.]+ bits (\d+) coset (-?\d+) (-?\d+) (-?\d+) (-?\d+) (-?\d+) forms B (-?\d+) (-?\d+) (-?\d+) (\d+) C (-?\d+) (-?\d+) (-?\d+) (\d+) W (-?\d+) (-?\d+) (-?\d+) (\d+) \| (.*)', line)
    if not m: continue
    ceil = float(m.group(1)); v = list(map(int, m.groups()[1:19])); bits, x0m, x0E, B00, B10, B11 = v[:6]; Bf, Cf, Wf = tuple(v[6:10]), tuple(v[10:14]), tuple(v[14:18])
    kh = int(math.floor(ceil + 6.38)) + 1
    if kh <= kmin: continue
    nent += 1
    b = P.yforms(x0m, x0E, B00, B10, B11, Bf); c = P.yforms(x0m, x0E, B00, B10, B11, Cf); w = P.yforms(x0m, x0E, B00, B10, B11, Wf)
    R = [w[i] - c[i] - (1 if i == 0 else 0) for i in range(3)]; L = [147 * b[i] + 280 * w[i] - 392 * c[i] - (578 if i == 0 else 0) for i in range(3)]
    # line: al*(x0m + B00 y0) - be*(x0E + B10 y0 + B11 y1) = ga  ->  (al*B00 - be*B10) y0 - be*B11 y1 = ga - al*x0m + be*x0E
    A0, A1 = al * B00 - be * B10, -be * B11; rhs = ga - al * x0m + be * x0E
    g, s, t = P.egcd(A0, A1)
    if g == 0 or rhs % g: continue          # the line misses the coset
    nline += 1
    Y0, Y1 = s * (rhs // g), t * (rhs // g); d0, d1 = A1 // g, -A0 // g
    Rc = R[0] + R[1] * Y0 + R[2] * Y1; Rd = R[1] * d0 + R[2] * d1
    Lc = L[0] + L[1] * Y0 + L[2] * Y1; Ld = L[1] * d0 + L[2] * d1
    for p in range(0, 40):
        for r, cls, M in P.CLOSE:
            target = 16 ** p * r
            if target >= 1 << kh: continue
            if Rd == 0:
                if Rc != target: continue
                continue   # R1 constant on the line: ignore (would need the whole line)
            if (target - Rc) % Rd: continue
            u = (target - Rc) // Rd; y0, y1 = Y0 + u * d0, Y1 + u * d1
            mm, E = x0m + B00 * y0, x0E + B10 * y0 + B11 * y1
            if not (0 < mm < E - 2) or E < (1 << kmin): continue
            npts += 1
            L1 = Lc + Ld * u
            if (L1 - 64 ** p * cls) % (64 ** p * M) == 0: cands.append((ceil, mm, E, p, r, m.group(20)))
print(f'entries {nent}, entries whose coset meets the line {nline}, pinned points on the line {npts}, full candidates {len(cands)}')
for cnd in cands: print('CANDIDATE', cnd)
