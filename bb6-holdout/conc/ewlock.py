"""Is P^n (and other words) 2-adically consistent on a 2-parameter family of extra-wall states, using only the
family's map (no route congruences)?  Test GMM-born families and random affine 2-D families; compare with 3-D."""
import sys, json, random
from fractions import Fraction as F
import ewforms as EF, mixsolve as MS
from lattice import Coset as LCoset
P5cache = {}
def conds(word):
    if word not in P5cache: P5cache[word] = MS.forced(word).cong
    return P5cache[word]
def max_word(wpos, nvar, letters='P', nmax=10, base=None):
    """largest n such that letters*n is consistent on the family wpos (forms over nvar vars + const)."""
    best = 0
    for n in range(1, nmax + 1):
        word = letters * n
        C = LCoset(nvar) if base is None else base()
        ok = True
        for form5, res, mod in conds(word):
            f = [F(0)] * (nvar + 1)
            for i in range(5):
                for j in range(nvar + 1): f[j] += form5.f[i] * wpos[i][j]
            f[nvar] += form5.f[5]
            den = 1
            for q in f: den = max(den, q.denominator)
            M = [int(q * den) for q in f[:nvar]]; c = int(f[nvar] * den)
            if not C.impose(M, den * res - c, den * mod, reduce=False): ok = False; break
        if not ok: break
        best = n
    return best
routes = json.load(open('../ewroutes_30.json'))
print("GMM-born families (route map only, parity of m, E imposed):")
for idx in [0, 1, 13, 15, 20, 55, 91]:
    h, o, p = routes[idx]
    md = EF.route_model(h, o); mk = md.marks()
    wpos = [list(q.f) for t, q in mk[1:]] + [list(md.W.f)]
    def base():
        C = LCoset(2); C.impose([1, 0], 0, 2, reduce=False); C.impose([0, 1], 1, 2, reduce=False); return C
    print(f"  route #{idx}: P^n consistent up to n = {max_word(wpos, 2, 'P', 8, base)}, Q^n up to {max_word(wpos, 2, 'Q', 8, base)}")
random.seed(5)
def rnd_family(nvar):
    # walls w1 < w2 < w3 < w4 < E as random affine forms (odd/even parities handled by generic coefficients)
    fam = []
    for i in range(4): fam.append([F(random.randrange(-2**12, 2**12), 2 ** random.randrange(0, 12)) for _ in range(nvar)] + [F(random.randrange(0, 2**10))])
    fam.append([F(int(j == nvar - 1)) for j in range(nvar)] + [F(0)])
    return fam
for nvar in (1, 2, 3, 4):
    res = [max_word(rnd_family(nvar), nvar, 'P', 8) for _ in range(12)]
    print(f"random {nvar}-parameter families: largest consistent P^n: {res}")
