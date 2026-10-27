import sys, collections
from k1lineup import *
def solve1d_idx(cong, alpha, beta):
    J0, Jm = 0, 1
    for idx, (pform, res, mod) in enumerate(cong):
        f = pform.f; den = 1
        for a in f: den = max(den, a.denominator)
        nv = len(f) - 1
        M = [int(a * den) for a in f[:nv]]; c = int(f[nv] * den); md = den * mod; r = den * res - c
        A = sum(a * b for a, b in zip(M, alpha)); Bv = sum(a * b for a, b in zip(M, beta))
        a1 = (A * Jm) % md; b1 = (r - Bv - A * J0) % md
        g = gcd(a1, md)
        if b1 % g: return idx, Jm.bit_length() - 1
        a2, b2, m2 = a1 // g, b1 // g, md // g
        t0 = (b2 * pow(a2, -1, m2)) % m2 if m2 > 1 else 0
        J0 = J0 + Jm * t0; Jm = Jm * m2; J0 %= Jm
    return None, Jm.bit_length() - 1
cnt = collections.Counter()
for l in open(sys.argv[1]):
    n0, kset = map(int, l.split()[:2])
    sts, hist = k1states(n0, kset)
    r, forms, vals = sts[0]
    k, fm, vv = entry_line(n0, r)
    cg = forced_cong('P', vv)
    idx, bits = solve1d_idx(cg, [a for a, b in fm], [b for a, b in fm])
    # which round of the pass does test idx belong to, and how far did the class actually follow P
    actual = hist[r: r + 8]; follow = 0
    for want, got in zip(P_sh, actual):
        if want != got: break
        follow += 1
    cnt[(idx, follow)] += 1
    print(n0, "entry depth", k, "first failing test", idx, "of", len(cg), "| j fixed to", bits, "bits before | class follows P for", follow, "rounds:", ' '.join(actual))
print(cnt)
