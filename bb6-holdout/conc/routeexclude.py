"""Route-by-route exclusion of single-stretch halts from GMM states (gap at 1, marker m, end marker at E - 2).
For a route r (the shapes and outcomes from the GMM state to the first G W W W), a halt at width E in [2^k, 2^(k+1))
needs p plain passes with H_r + 4p + 8 >= k - 1 (H_r = most halvings the route itself can make, 8 = proved bound on the
exit).  The forced congruences of route + p passes form a 2-D coset in (m, E); every state that halts this way lies in
it.  Enumerate its points in the box and write them out for simulation.
usage: routeexclude.py m_ex E_ex kmin kmax outfile"""
import sys, math, io, contextlib
from fractions import Fraction as F
from conc import Model, Pos
from lattice import Coset, lll
with contextlib.redirect_stdout(io.StringIO()):
    from cyccost import CYC, outs as L_out

def concrete_route(m_ex, E_ex):
    md = Model(1); md.W = md.const(E_ex); md.add('G', md.const(1)); md.add('M', md.const(m_ex)); md.add('M', md.W - 2)
    shapes = []; marks_at = []
    for r in range(400):
        md.do_round()
        if md.bad or md.halted: break
        shapes.append(md.shape()); marks_at.append(len(md.outcomes))
        mk = md.marks()
        if md.shape() in ('GM', 'GMM') and mk[-1][0] == 'M' and mk[-1][1].v == md.W.v - 2: break   # segment ends
    outs = list(md.outcomes)
    # (a) a G W W W from which a plain pass starts (followed by G B W, G M B)
    for i, sh in enumerate(shapes):
        if sh == 'GWWW' and shapes[i + 1:i + 3] == CYC[:2]:
            return shapes[:i + 1], outs[:marks_at[i]]
    # (b) a G W W W in the middle of a pass (after G M B, G M W W): finish the pass's last two rounds
    for i, sh in enumerate(shapes):
        if sh == 'GWWW' and i >= 2 and shapes[i - 2:i] == ['GMB', 'GMWW']:
            return shapes[:i + 1] + ['GBW', 'GWWW'], outs[:marks_at[i]] + [2, 2, 2]
    return None

def forced(m_ex, E_ex, shapes, outs, p, sc):
    md = Model(2)
    md.W = Pos([F(0), F(1), F(0)], F(E_ex) * sc)
    md.add('G', md.const(1)); md.add('M', Pos([F(1), F(0), F(0)], F(m_ex) * sc)); md.add('M', md.W - 2)
    md.force = list(outs) + list(L_out) * p
    for want in shapes + CYC * p:
        md.do_round()
        if md.bad or md.shape() != want: return None, f"shape {md.shape()} want {want}"
    return md, None

def coset_of(md):
    C = Coset(2)
    for pform, res, mod in md.cong:
        f = pform.f; den = 1
        for q in f: den = den * q.denominator // math.gcd(den, q.denominator)
        if not C.impose([int(q * den) for q in f[:2]], den * res - int(f[2] * den), den * mod, reduce=False): return None
    if not C.impose([1, 0], 0, 2, reduce=False) or not C.impose([0, 1], 1, 2, reduce=False): return None
    return C

def route_halvings(m_ex, E_ex, shapes, outs):
    """Largest halvings the end distance at the first G W W W can have, over 0 < m/E < 1, from its affine form."""
    md, err = forced(m_ex, E_ex, shapes, outs, 0, F(2) ** 80)
    mk = md.marks(); d = md.W - mk[-1][1]
    a, b = d.f[0], d.f[1]          # d = a m + b E + c
    lo = min(b, a + b)             # d/E at m/E = 0 and 1, for large E
    if lo <= 0: return None
    return math.log2(1 / float(lo))

def points(C, k):
    """All coset points with 2^k <= E < 2^(k+1), 4 <= m <= E - 7."""
    (u1, e1), (u2, e2) = C.B
    # unimodular reduction on the E components: make the second vector have E-component 0
    while e2 != 0:
        q = e1 // e2; u1, e1, u2, e2 = u2, e2, u1 - q * u2, e1 - q * e2
    gE, uE, dm = e1, u1, abs(u2)
    if gE < 0: gE, uE = -gE, -uE
    x0m, x0E = C.x0
    t0 = -(-(2 ** k - x0E) // gE)
    E = x0E + t0 * gE; t = t0
    while E < 2 ** (k + 1):
        mbase = x0m + t * uE
        m = 4 + ((mbase - 4) % dm)
        while m <= E - 7:
            yield m, E
            m += dm
        t += 1; E += gE

if __name__ == '__main__':
    m_ex, E_ex, kmin, kmax, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    cr = concrete_route(m_ex, E_ex)
    if cr is None: print("no loop entry found in the example's segment"); sys.exit()
    shapes, outs = cr
    H = route_halvings(m_ex, E_ex, shapes, outs)
    print("route:", ' '.join(shapes), "| outcomes", len(outs), "| most route halvings", None if H is None else round(H, 2))
    if H is None: print("route can bring the end arbitrarily close by itself; not handled"); sys.exit()
    f = open(out, 'w'); total = 0; cache = {}
    for k in range(kmin, kmax + 1):
        p = max(1, math.ceil((k - 1 - 8 - H) / 4))
        if p not in cache:
            md, err = forced(m_ex, E_ex, shapes, outs, p, F(2) ** (4 * p + 100))
            if md is None: cache[p] = ('geometry', err)
            else:
                C = coset_of(md)
                cache[p] = ('ok', C) if C is not None else ('inconsistent', None)
        st, C = cache[p]
        if st != 'ok': print(f"k = {k}: p = {p}: {st} {C if st == 'geometry' else ''}"); continue
        cnt = 0
        for m, E in points(C, k):
            f.write(f"{m} {E}\n"); cnt += 1
            if cnt > 5_000_000: break
        total += cnt
        print(f"k = {k}: passes needed {p}, coset index 2^{C.index_bits():.1f}, candidates {cnt}", flush=True)
    print("total candidates", total)
