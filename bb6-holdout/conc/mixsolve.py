"""Hand-built states for mixed P/Q words of the one-extra-wall loop at a large scale: solve the forced congruences as
a lattice coset, pick the coset point nearest the scaled geometry (LLL + Babai), and run the integer mark model."""
import sys, math
from fractions import Fraction as F
from conc import Model, Pos
from lattice import Coset, babai, lg
geo = [21395686159, 412072778788, 1527835310093, 2817122580142, 3359928725359]
SC = 2 ** 200; big = [F(v) * SC for v in geo]
import os
MOD3 = bool(os.environ.get('MOD3'))
def set_scale(nw):
    global big
    big = [F(v) * 2 ** max(200, 4 * nw + 80) for v in geo]
P_out = [2,2,2,2, 2,2,2,0, 0,2,2,2, 0, 0,2,2,2, 2]
Q_out = [2,2,0,0,0,2,2, 0,2, 0, 0,2,2,2, 0, 0,2,2,2, 2]
P_sh = ['GBWW', 'GWWWW', 'GBWW', 'GMBW', 'GMWWW', 'GMBW', 'GMWWW', 'GWWWW']
Q_sh = ['GBWW', 'GMMWW', 'GMWWW', 'GMBW', 'GMWWW', 'GMBW', 'GMWWW', 'GWWWW']
def forced(word):
    m = Model(5)
    for i in range(4): m.add('W', Pos([F(int(i == j)) for j in range(5)] + [F(0)], big[i]))
    m.W = Pos([F(int(j == 4)) for j in range(5)] + [F(0)], big[4]); m.add('G', m.const(1)); m.force = []
    for x in word: m.force += (P_out if x == 'P' else Q_out)
    for x in word:
        for want in (P_sh if x == 'P' else Q_sh):
            m.do_round()
            if m.bad or m.shape() != want: return None
    return m
def coset(word):
    m = forced(word)
    if m is None: return None
    C = Coset(5)
    for ci, (pform, res, mod) in enumerate(m.cong):
        f = pform.f; den = 1
        for a in f: den = max(den, a.denominator)
        M = [int(a * den) for a in f[:5]]; c = int(f[5] * den)
        if not C.impose(M, den * res - c, den * mod, reduce=(ci % 16 == 15)): return None
    # tape parities: walls alternate odd, even, odd, even after the gap; the last 1 is at E - 1
    for i, par in enumerate((1, 0, 1, 0, 1)):
        if not C.impose([int(i == j) for j in range(5)], par, 2): return None
    # the machine's conserved quantity: (#1s + state weight) = 0 mod 3 on every tape reached from blank; at this
    # round start #1s = (E - 5)/2 and state E weighs 1, so E = 0 (mod 3)
    if MOD3 and not C.impose([0, 0, 0, 0, 1], 0, 3): return None
    from lattice import lll
    C.B = lll(C.B)
    return C
def run_int(x, maxrounds=100000):
    mm = Model(1); mm.W = mm.const(x[4]); mm.add('G', mm.const(1))
    for v in x[:4]: mm.add('W', mm.const(v))
    shapes = []
    for rd in range(maxrounds):
        mm.do_round(); shapes.append(mm.shape())
        if mm.halted or mm.bad: break
        mk = mm.marks()
        if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == mm.W.v - 2: break
    return mm, shapes
if __name__ == '__main__':
    word = sys.argv[1]; K = int(sys.argv[2]); set_scale(len(word))
    C = coset(word)
    if C is None: print("word inconsistent"); sys.exit()
    print(f"word {word}: coset index 2^{C.index_bits():.1f}; reduced basis lengths (log2):",
          [round(lg(sum(a*a for a in v)) / 2, 1) for v in C.B])
    t = [F(g * 2 ** K, geo[4]) for g in geo]
    tt = [a - b for a, b in zip(t, C.x0)]
    x = [a + b for a, b in zip(C.x0, babai(C.B, tt))]
    print("point:", x, " rel. deviation:", [float((a - b) / t[4]) for a, b in zip(x, t)])
    if len(sys.argv) > 3: open(sys.argv[3], 'w').write(' '.join(map(str, x)) + '\n')
    mm, shapes = run_int(x)
    ds = [int(d.v) for r, d in mm.endd]
    print("end meetings:", len(ds), "halted" if mm.halted else "", "bad" if mm.bad else "")
    print("  halvings log2(E/d):", [round(lg(x[4]) - lg(max(d, 1)), 1) for d in ds])
    print("  last meetings:", ds[-8:], "final shapes:", shapes[-6:])
