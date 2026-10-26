"""Turn a large-gap pass start into a long cascade: take the line of the class at the depth where its pass start is
determined, choose higher digits of n so that the left countdown has the trailing zeros the gap allows, and run."""
import sys
from fractions import Fraction as F
from conc import Model, Pos
from depthslack import v2f
from plainlineup import entry_line
def chain_info(n0):
    m = Model(1); m.W = m.const(2 * n0 + 6); m.add('G', m.const(1)); m.add('M', m.W - 2); hist = []
    for r in range(5000):
        hist.append(m.shape()); m.do_round()
        mk = m.marks()
        if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2: break
    ds = [int(d.v) for rr, d in m.endd]
    def pred(d): return (d - 2) // 2 if d % 4 == 2 else d // 2 + 4
    best = cur = 1
    for i in range(1, len(ds)):
        cur = cur + 1 if ds[i] == pred(ds[i - 1]) else 1; best = max(best, cur)
    md = min(ds[1:]) if len(ds) > 1 else None
    import math
    return best, (math.log2((2 * n0 + 6) / md) if md else 0), hist
def pass_starts(hist):
    return [i for i in range(len(hist) - 2) if hist[i] == 'GWWW' and hist[i + 1] == 'GBW' and hist[i + 2] == 'GMB']
def build(n0, which=0, extra_bits=0):
    L0, h0, hist = chain_info(n0)
    ps = pass_starts(hist)
    if not ps: return None
    r = ps[which]
    k, fm, vv = entry_line(n0, r, 4)
    # positions at the pass start as alpha*j + beta, n = rho + 2^k j
    (aa, ab), (ba, bb), (ca, cb), (Ea, Eb) = fm
    Ra, Rb = Ea - ca, Eb - cb - 1
    La, Lb = 1029 * ba + 1960 * Ea - 2744 * ca, 1029 * bb + 1960 * Eb - 2744 * cb - 4046
    D = F(Ra) * Lb - F(La) * Rb
    GR = v2f(D) - v2f(F(La)); GL = v2f(D) - v2f(F(Ra))
    m = max(0, (GR - 1) // 4)
    # choose j with v2(L(j)) >= 6m + 1 + extra and v2(R(j)) >= 4m + 1: solve La*j + Lb = 0 mod 2^e
    rho = n0 % (1 << k)
    best = None
    for mm in range(m, -1, -1):
        e = 6 * mm + 1 + extra_bits
        g = 1 << v2f(F(La)) if La else 1
        # La j + Lb = 0 mod 2^e  -> divide by 2^v2(La)
        vL = v2f(F(La))
        if Lb % (1 << min(vL, e)): continue
        if e <= vL: j = 1
        else:
            Mod = 1 << (e - vL); j = ((-Lb >> vL) * pow(La >> vL, -1, Mod)) % Mod
            if j == 0: j = Mod
        n = rho + (j << k)
        Lv = La * j + Lb; Rv = Ra * j + Rb
        best = (mm, n, v2f(F(Lv)), v2f(F(Rv))); break
    mm, n, vl, vr = best
    L1, h1, hist1 = chain_info(n)
    return dict(class_n=n0, pass_round=r, entry_depth=k, gaps=(GL, GR), passes_allowed=mm, n=n, bits=n.bit_length(),
                fuels=(vl, vr), chain=L1, halvings=round(h1, 1), orig_chain=L0)
if __name__ == '__main__':
    for a in sys.argv[1:]:
        print(build(int(a)))
