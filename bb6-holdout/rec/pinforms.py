"""Exact halting candidates for plain entries listed by the route tree (rtree3c S lines).

An S line gives the entry's coset in (m, E), m = x0m + B00 y0, E = x0E + B10 y0 + B11 y1, and the forms of the second
wall b, third wall c and width W at the phase-0 pass start, each (a m + b E + c) / 2^e.  There R1 = W - c - 1 and
L1 = 147 b + 280 W - 392 c - 578.  A halt through this stretch needs R1 = 16^p r and L1 = 64^p cls_r (mod 64^p M_r)
for one of the nine closing values r (endsym.py), and this lists every coset point with width in [2^kmin, 2^kmax)
that satisfies both.  usage: pinforms.py kmin kmax [min_ceiling] < S-lines
"""
import sys, re, math, os
COUNTRP = os.environ.get('NORP') is None
from math import gcd
CLOSE = [(2, 10, 14), (4, 10, 14), (8, 24, 56), (16, 192, 224), (24, 416, 448), (32, 192, 448), (48, 640, 896), (64, 640, 896), (176, 640, 896)]

def egcd(x, y):
    r0, r1, s0, s1, t0, t1 = x, y, 1, 0, 0, 1
    while r1:
        q = r0 // r1; r0, r1 = r1, r0 - q * r1; s0, s1 = s1, s0 - q * s1; t0, t1 = t1, t0 - q * t1
    if r0 < 0: r0, s0, t0 = -r0, -s0, -t0
    return r0, s0, t0

def yforms(x0m, x0E, B00, B10, B11, F):
    """form (a, b, c, e) in (m, E) -> integer affine function [c0, c1, c2] of (y0, y1); checks integrality on the coset"""
    a, b, c, e = F; d = 1 << e
    c0 = a * x0m + b * x0E + c; c1 = a * B00 + b * B10; c2 = b * B11
    assert c0 % d == 0 and c1 % d == 0 and c2 % d == 0, 'form not integral on the coset'
    return [c0 // d, c1 // d, c2 // d]

def candidates(x0m, x0E, B00, B10, B11, Bf, Cf, Wf, kmin, kmax):
    b = yforms(x0m, x0E, B00, B10, B11, Bf); c = yforms(x0m, x0E, B00, B10, B11, Cf); w = yforms(x0m, x0E, B00, B10, B11, Wf)
    R = [w[i] - c[i] - (1 if i == 0 else 0) for i in range(3)]
    L = [147 * b[i] + 280 * w[i] - 392 * c[i] - (578 if i == 0 else 0) for i in range(3)]
    pt = lambda y0, y1: (x0m + B00 * y0, x0E + B10 * y0 + B11 * y1)
    Elo, Ehi = 1 << kmin, 1 << kmax
    out = []; rpinned = 0
    for p in range(0, 80):
        if 16 ** p * 2 > Ehi: break
        for r, cls, M in CLOSE:
            target = 16 ** p * r
            g, s, t = egcd(R[1], R[2]); rhs = target - R[0]
            if g == 0 or rhs % g: continue
            Y0, Y1 = s * (rhs // g), t * (rhs // g); d0, d1 = R[2] // g, -R[1] // g
            Ec = x0E + B10 * Y0 + B11 * Y1; Ed = B10 * d0 + B11 * d1
            if Ed != 0:
                ulo, uhi = (Elo - Ec) // Ed, (Ehi - Ec) // Ed
            else:
                if Ec < Elo or Ec >= Ehi: continue
                Mc = x0m + B00 * Y0; Md = B00 * d0
                if Md == 0: continue
                ulo, uhi = (0 - Mc) // Md, (Ec - Mc) // Md
            if ulo > uhi: ulo, uhi = uhi, ulo
            ulo -= 2; uhi += 2
            # intersect with 0 < m(u) < E(u) - 2, both linear in u
            Mc = x0m + B00 * Y0; Md = B00 * d0
            for A, Bc in ((Mc, Md), (Ec - 2 - Mc, Ed - Md)):      # need A + Bc u > 0
                if Bc > 0: ulo = max(ulo, (-A) // Bc + 1)
                elif Bc < 0: uhi = min(uhi, (A - 1) // (-Bc))
                elif A <= 0: ulo, uhi = 1, 0
            if ulo > uhi: continue
            if COUNTRP and uhi - ulo < 10 ** 7:
                for u in range(ulo, uhi + 1):
                    m, E = pt(Y0 + u * d0, Y1 + u * d1)
                    if Elo <= E < Ehi and 0 < m < E - 2: rpinned += 1
            Lc = L[0] + L[1] * Y0 + L[2] * Y1; Ld = L[1] * d0 + L[2] * d1
            Mod = 64 ** p * M; want = (64 ** p * cls - Lc) % Mod
            h, sh, _ = egcd(Ld % Mod, Mod)
            if want % h: continue
            step = Mod // h; u0 = ((want // h) * sh) % step
            u = ulo + (u0 - ulo) % step
            while u <= uhi:
                y0, y1 = Y0 + u * d0, Y1 + u * d1; m, E = pt(y0, y1)
                if Elo <= E < Ehi and 0 < m < E - 2:
                    R1 = R[0] + R[1] * y0 + R[2] * y1; L1 = L[0] + L[1] * y0 + L[2] * y1
                    assert R1 == target and (L1 - 64 ** p * cls) % Mod == 0
                    out.append((m, E, p, r))
                u += step
    return out, rpinned

if __name__ == '__main__':
    kmin, kmax = int(sys.argv[1]), int(sys.argv[2]); minc = float(sys.argv[3]) if len(sys.argv) > 3 else 0
    tot = 0; nent = 0; allc = []
    for line in sys.stdin:
        m = re.match(r'S ([0-9.]+) t=[0-9.]+ bits (\d+) coset (-?\d+) (-?\d+) (-?\d+) (-?\d+) (-?\d+) forms B (-?\d+) (-?\d+) (-?\d+) (\d+) C (-?\d+) (-?\d+) (-?\d+) (\d+) W (-?\d+) (-?\d+) (-?\d+) (\d+) \| (.*)', line)
        if not m: continue
        ceil = float(m.group(1))
        if ceil < minc: continue
        v = list(map(int, m.groups()[1:19]))
        bits, x0m, x0E, B00, B10, B11 = v[:6]; Bf, Cf, Wf = tuple(v[6:10]), tuple(v[10:14]), tuple(v[14:18])
        kh = min(kmax, int(math.floor(ceil + 6.38)) + 1)   # by the lock nothing above 2^(ceiling + 6.38)
        if kh <= kmin: continue
        out, rp = candidates(x0m, x0E, B00, B10, B11, Bf, Cf, Wf, kmin, kh)
        nent += 1; tot += len(out); allc += [(ceil, m.group(20), o) for o in out]
        if COUNTRP or out: print(f'ceiling {ceil} bits {bits}: widths 2^{kmin}..2^{kh}: {rp} points with R1 pinned, {len(out)} full candidates; {m.group(20)[:80]}')
    print(f'entries {nent}, candidates {tot}')
    for ceil, route, (mm, E, p, r) in allc: print('CANDIDATE', ceil, mm, E, p, r, route)
