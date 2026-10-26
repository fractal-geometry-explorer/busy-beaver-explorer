"""Hand-built states for words that mix the one-extra-wall loop (P, Q) with a drop into the plain loop (D) and plain
passes (L).  Same lattice method as mixsolve.py.  Optional: one extra linear relation among the unknowns, to test a
family with one free number fewer.
usage: mixdrop.py WORD K [relation]   relation like '11c-5E' (pinned to its value at the target geometry)"""
import sys, math, re, os
from fractions import Fraction as F
from conc import Model, Pos
from lattice import Coset, babai, lll, lg
sys.path.insert(0, '../rec')
geo = [21395686159, 412072778788, 1527835310093, 2817122580142, 3359928725359]
P_out = [2,2,2,2, 2,2,2,0, 0,2,2,2, 0, 0,2,2,2, 2]
Q_out = [2,2,0,0,0,2,2, 0,2, 0, 0,2,2,2, 0, 0,2,2,2, 2]
D_out = {'D': [0,2,0,2,0,2,2], 'd': [0,0,0,2,2,0,2,2]}
L_out = [2,2,0,0,2,2,0,0,2,2,2,2,2,2]
P_sh = ['GBWW', 'GWWWW', 'GBWW', 'GMBW', 'GMWWW', 'GMBW', 'GMWWW', 'GWWWW']
Q_sh = ['GBWW', 'GMMWW', 'GMWWW', 'GMBW', 'GMWWW', 'GMBW', 'GMWWW', 'GWWWW']
D_sh = ['GBWW', 'GMWW', 'GWWW']
L_sh = ['GBW', 'GMB', 'GMWW', 'GMB', 'GMWW', 'GWWW', 'GBW', 'GWWW']
X_sh = ['GBWW', 'GMMM', 'GMMW', 'GMWW', 'GWWW']; X_out = [int(c) for c in '20200002022']
Y_sh = ['GBWW', 'GMWWMW', 'GWWWMW', 'GBWMW', 'GWWW']; Y_out = [int(c) for c in '000202022222']
Z_sh = ['GBWW', 'GMBMM', 'GMMW', 'GMWW', 'GWWW']; Z_out = [int(c) for c in '02200202022']
V_sh = ['GBWW', 'GMWMWW', 'GWWMWW', 'GBMWW', 'GWWW']; V_out = [int(c) for c in '0002002022222']
U_sh = ['GBWW', 'GMMWMM', 'GMMW', 'GMWW', 'GWWW']; U_out = [int(c) for c in '2200002002022']
T_sh = ['GBWW', 'GMMWWW', 'GWMWWW', 'GBW', 'GWWW']; T_out = [int(c) for c in '00020020022222']
OUT = {'V': V_out, 'U': U_out, 'T': T_out, 'P': P_out, 'Q': Q_out, 'D': D_out['D'], 'd': D_out['d'], 'L': L_out, 'X': X_out, 'Y': Y_out, 'Z': Z_out}
SH = {'V': V_sh, 'U': U_sh, 'T': T_sh, 'P': P_sh, 'Q': Q_sh, 'D': D_sh, 'd': D_sh, 'L': L_sh, 'X': X_sh, 'Y': Y_sh, 'Z': Z_sh}
def expand(word):
    return ''.join(ch * int(n or 1) for ch, n in re.findall(r'([PQDdLXYZVUT])(\d*)', word))
def forced(word, scale):
    big = [F(v) * scale for v in geo]
    m = Model(5)
    for i in range(4): m.add('W', Pos([F(int(i == j)) for j in range(5)] + [F(0)], big[i]))
    m.W = Pos([F(int(j == 4)) for j in range(5)] + [F(0)], big[4]); m.add('G', m.const(1)); m.force = []
    for x in word: m.force += OUT[x]
    for k, x in enumerate(word):
        for want in SH[x]:
            m.do_round()
            if m.bad or m.shape() != want: return None, f"letter {k} ({x}): got {m.shape()} want {want}"
    return m, None
def coset(word, scale, rel=None, K=None, mod3=True):
    m, err = forced(word, scale)
    if m is None: return None, err, None
    C = Coset(5)
    for ci, (pform, res, mod) in enumerate(m.cong):
        f = pform.f; den = 1
        for a in f: den = max(den, a.denominator)
        M = [int(a * den) for a in f[:5]]; c = int(f[5] * den)
        if not C.impose(M, den * res - c, den * mod, reduce=(ci % 16 == 15)): return None, "inconsistent", m
    for i, par in enumerate((1, 0, 1, 0, 1)):
        if not C.impose([int(i == j) for j in range(5)], par, 2): return None, "parity", m
    if mod3 and not C.impose([0, 0, 0, 0, 1], 0, 3): return None, "mod 3", m
    C.B = lll(C.B)
    return C, None, m
def parse_rel(s):
    co = [0] * 5
    for sign, num, var in re.findall(r'([+-]?)(\d*)([abcdE])', s):
        co['abcdE'.index(var)] += (-1 if sign == '-' else 1) * int(num or 1)
    return co
def build(word, K, rel=None, Rexp=None, verbose=True, Rend=None):
    import hybsim
    w = expand(word)
    scale = F(2) ** max(200, 4 * len(w) + 80)
    C, err, m = coset(w, scale)
    if C is None: return f"{err}"
    E = 2 ** K; t = [F(g * E, geo[4]) for g in geo]
    if Rexp is not None:
        R = 2 ** Rexp
        if not C.impose([0, 0, 0, -1, 1], R + 1, 2 ** (K + 8)): return "R pin inconsistent"
        t[3] = F(E - 1 - R)
    if Rend is not None:
        mk = m.marks(); Rf = m.W - mk[-1][1]; D = 1
        for q in Rf.f: D = D * q.denominator // math.gcd(D, q.denominator)
        co = [int(q * D) for q in Rf.f[:5]]; c5 = int(Rf.f[5] * D)
        if not C.impose(co, Rend * D - c5, D * 2 ** (K + 8)): return "final distance pin inconsistent"
        Rt = Rf.f[5] + sum(a * b for a, b in zip(Rf.f[:5], t))
        t[3] += (Rend - Rt) / Rf.f[3]
    if rel is not None:
        co = parse_rel(rel); val = round(sum(a * b for a, b in zip(co, t)))
        g = 0
        for row in C.B: g = math.gcd(g, sum(a * b for a, b in zip(co, row)))
        r0 = sum(a * b for a, b in zip(co, C.x0))
        g = math.gcd(g, 2 ** (K + 8)) if g else 2 ** (K + 8)
        val = val + ((r0 - val) % g)
        relinfo = f"relation fixed mod 2^{g.bit_length() - 1} by the word; "
        if not C.impose(co, val, 2 ** (K + 8)): return "relation inconsistent"
    C.B = lll(C.B)
    bl = [lg(sum(a * a for a in v)) / 2 for v in C.B]
    x = [p + q for p, q in zip(C.x0, babai(C.B, [u - v for u, v in zip(t, C.x0)]))]
    dev = max(abs(float((a - b) / t[-1])) for a, b in zip(x, t))
    info = (relinfo if rel is not None else '') + f"index 2^{C.index_bits():.0f}, longest basis vector 2^{max(bl):.1f}, deviation {dev:.2g}"
    if not (0 < x[0] < x[1] < x[2] < x[3] < x[4]): return info + "; point out of order " + str([round(float(v / x[4]), 4) for v in x]) + " target " + str([round(float(v / t[4]), 4) for v in t])
    try:
        res = hybsim.run(hybsim.config_from([('G', 1)] + [('W', p) for p in x[:-1]], x[-1]), max_rounds=20 * K + 400, log=lambda *a: None)
    except AssertionError as e:
        return info + f"; invalid tape {e}"
    return info + f"; {res['result']} {res.get('rule', '')} after {res['rounds']} rounds"
if __name__ == '__main__':
    word = sys.argv[1]; K = int(sys.argv[2]); rel = sys.argv[3] if len(sys.argv) > 3 and sys.argv[3] != '-' else None
    rr = [int(v) for v in sys.argv[4].split(':')] if len(sys.argv) > 4 else None
    if len(sys.argv) > 5 and sys.argv[5] == 'auto':
        w = expand(word); m, err = forced(w, F(2) ** max(200, 4 * len(w) + 80))
        mk = m.marks(); Rf = m.W - mk[-1][1]; E = 2 ** K; t = [F(g * E, geo[4]) for g in geo]
        Rt = float(Rf.f[5] + sum(a * b for a, b in zip(Rf.f[:5], t))); print("end distance at the target geometry", Rt)
        for T in range(rr[0], rr[1] + 1, 2): print(word, K, rel, 'Rend=%d' % T, build(word, K, rel, None, Rend=T), flush=True)
    elif len(sys.argv) > 5 and sys.argv[5] == 'end':
        for T in range(rr[0], rr[1] + 1, 2 if rr[0] % 2 == 0 else 1): print(word, K, rel, 'Rend=%d' % T, build(word, K, rel, None, Rend=T), flush=True)
    elif rr:
        for e in range(rr[0], rr[1] + 1): print(word, K, rel, 'R=2^%d' % e, build(word, K, rel, e), flush=True)
    else:
        print(word, K, rel, build(word, K, rel), flush=True)
