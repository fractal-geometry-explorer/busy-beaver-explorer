"""For clean-tape classes whose cycle reaches the extra-wall loop: at each G W W W W state, take the class's line
x(j) = alpha*j + beta (n = rho + 2^k j) and find the largest m such that some member follows P^m (and the best words
mixing in one detour), using the forced congruences of each word."""
import sys
from fractions import Fraction as F
from math import gcd
from conc import Model, Pos
import mixsolve
from mixsolve import P_out, Q_out, P_sh, Q_sh
def forced_cong(word, geo_vals):
    big = [F(v) * 2 ** (4 * len(word) + 120) for v in geo_vals]
    m = Model(5)
    for i in range(4): m.add('W', Pos([F(int(i == j)) for j in range(5)] + [F(0)], big[i]))
    m.W = Pos([F(int(j == 4)) for j in range(5)] + [F(0)], big[4]); m.add('G', m.const(1)); m.force = []
    for x in word: m.force += (P_out if x == 'P' else Q_out)
    for x in word:
        for want in (P_sh if x == 'P' else Q_sh):
            m.do_round()
            if m.bad or m.shape() != want: return None
    return m.cong
def solve1d(cong, alpha, beta):
    """Is there an integer j with M.(alpha j + beta) = r (mod m) for all congruences?  Returns modulus of the j-class or None."""
    J0, Jm = 0, 1        # j = J0 (mod Jm)
    for pform, res, mod in cong:
        f = pform.f; den = 1
        for a in f: den = max(den, a.denominator)
        nv = len(f) - 1
        M = [int(a * den) for a in f[:nv]]; c = int(f[nv] * den); md = den * mod; r = den * res - c
        A = sum(a * b for a, b in zip(M, alpha)); Bv = sum(a * b for a, b in zip(M, beta))
        # A*(J0 + Jm t) + Bv = r (mod md)  ->  (A Jm) t = r - Bv - A J0 (mod md)
        a1 = (A * Jm) % md; b1 = (r - Bv - A * J0) % md
        g = gcd(a1, md)
        if b1 % g: return None
        a2, b2, m2 = a1 // g, b1 // g, md // g
        t0 = (b2 * pow(a2, -1, m2)) % m2 if m2 > 1 else 0
        J0 = J0 + Jm * t0; Jm = Jm * m2; J0 %= Jm
    return Jm
def k1states(n0, k):
    """G W W W W states of the cycle of n0 with positions as alpha*j + beta for n = n0 mod 2^k + 2^k j."""
    rho = n0 % (1 << k); w0 = 2 * n0 + 6
    m = Model(1); m.W = Pos([F(2 ** (k + 1)), F(2 * rho + 6)], w0); m.add('G', m.const(1)); m.add('M', m.W - 2)
    out = []; hist = []
    for r in range(1, 4000):
        m.do_round(); sh = m.shape(); hist.append(sh)
        if sh == 'GWWWW':
            mk = m.marks(); pos = [p for t, p in mk[1:]] + [m.W]
            out.append((r, [(p.f[0], p.f[1]) for p in pos], [p.v for p in pos]))
        mk = m.marks()
        if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2: break
    return out, hist
if __name__ == '__main__':
    words = ['P' * m for m in range(1, 7)] + ['Q', 'PQ', 'QP', 'PPQ', 'PQP', 'QPP']
    for l in open(sys.argv[1]):
        if not l.strip(): continue
        n0, k = map(int, l.split()[:2])
        sts, hist = k1states(n0, k)
        for (r, forms, vals) in sts:
            j0 = (n0 >> k)
            alpha = [int(a) for a, b in forms]; beta = [int(b) for a, b in forms]
            if any(F(a).denominator != 1 or F(b).denominator != 1 for a, b in forms): print("non-integer forms"); continue
            res = {}
            for w in words:
                cg = forced_cong(w, vals)
                if cg is None: res[w] = 'geo'; continue
                Jm = solve1d(cg, alpha, beta)
                res[w] = 'no' if Jm is None else f"2^{Jm.bit_length() - 1}"
            nxt = ' '.join(hist[r: r + 9])
            print(n0, k, "round", r, "| next:", nxt, "|", ' '.join(f"{w}:{v}" for w, v in res.items()))

def entry_line(n0, target_round):
    """Smallest depth k at which every test before the given round is decided for all n = n0 mod 2^k; returns
    (k, forms at that round) with forms alpha*j + beta (integers)."""
    for k in range(8, 60):
        rho = n0 % (1 << k)
        m = Model(1); m.W = Pos([F(2 ** (k + 1)), F(2 * rho + 6)], 2 * n0 + 6); m.add('G', m.const(1)); m.add('M', m.W - 2)
        ok = True
        for r in range(1, target_round + 1):
            nc = len(m.cong); m.do_round()
            for (d, res, mod) in m.cong[nc:]:
                if d.f[0].denominator != 1 or int(d.f[0]) % 4: ok = False
            if not ok: break
        if ok:
            mk = m.marks(); pos = [p for t, p in mk[1:]] + [m.W]
            return k, [(int(p.f[0]), int(p.f[1])) for p in pos], [p.v for p in pos]
    return None
