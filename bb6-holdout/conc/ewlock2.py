import random, collections
from fractions import Fraction as F
from lattice import Coset as LCoset
import mixsolve as MS
P5cache = {}
def conds(word):
    if word not in P5cache: P5cache[word] = MS.forced(word).cong
    return P5cache[word]
def consistent(wpos, nvar, word):
    C = LCoset(nvar)
    for form5, res, mod in conds(word):
        f = [F(0)] * (nvar + 1)
        for i in range(5):
            for j in range(nvar + 1): f[j] += form5.f[i] * wpos[i][j]
        f[nvar] += form5.f[5]
        den = 1
        for q in f: den = max(den, q.denominator)
        if not C.impose([int(q * den) for q in f[:nvar]], den * (res) - int(f[nvar] * den), den * mod, reduce=False): return False
    return True
def family(nvar):
    # integer variables; w_i = 2*(integer affine form) + parity; E = 2*x_last + 1 + const
    fam = []
    for i, par in enumerate((1, 0, 1, 0)):
        fam.append([F(2 * random.randrange(-999, 1000)) for _ in range(nvar)] + [F(2 * random.randrange(0, 999) + par)])
    fam.append([F(2 * random.randrange(1, 999)) for _ in range(nvar)] + [F(2 * random.randrange(0, 999) + 1)])
    return fam
if __name__ == "__main__":
  random.seed(11)
  for nvar in (1, 2, 3, 4):
      hist = collections.Counter()
      for trial in range(60):
          fam = family(nvar); n = 0
          while n < 8 and consistent(fam, nvar, 'P' * (n + 1)): n += 1
          hist[n] += 1
      print(f"{nvar}-parameter families (60 random): largest consistent P^n -> counts {dict(sorted(hist.items()))}", flush=True)
