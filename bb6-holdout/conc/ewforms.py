"""Why GMM-born entries into G W W W W cannot run the extra-wall loop: for each route found by ewroutes.explore,
print the G W W W W positions as affine forms in the GMM state's (m, E), and find the first congruence of a P or Q
pass (written in the 5-variable wall coordinates w1..w4, E of mixsolve) that the route's own 2-adic coset violates.
usage: ewforms.py cut_bits [routes.json]"""
import sys, json, math, os
from fractions import Fraction as F
from conc import Model, Pos
from lattice import Coset as LCoset
import mixsolve as MS

def frac_row(f, n):
    den = 1
    for q in f: den = den * q.denominator // math.gcd(den, q.denominator)
    return [int(q * den) for q in f[:n]], int(f[n] * den), den

def route_model(shapes, outs, extra_out=(), ratio=0.5, E_ex=2 ** 40 + 1):
    m_ex = int(E_ex * ratio) // 2 * 2; sc = F(2) ** 140
    md = Model(2)
    md.W = Pos([F(0), F(1), F(0)], F(E_ex) * sc)
    md.add('G', md.const(1)); md.add('M', Pos([F(1), F(0), F(0)], F(m_ex) * sc)); md.add('M', md.W - 2)
    md.force = list(outs) + list(extra_out)
    for want in shapes:
        md.do_round()
        if md.bad or md.shape() != want: return None
    return md

def coset_from(congs, start=None):
    C = LCoset(2) if start is None else start
    for pform, res, mod in congs:
        M, c, den = frac_row(pform.f, 2)
        if not C.impose(M, den * res - c, den * mod, reduce=False): return None
    return C

def pass5(letter):
    """The pass's congruences in the 5 wall coordinates (w1, w2, w3, w4, E)."""
    m = MS.forced(letter)
    return m.cong

def subst(form5, wpos):
    """form5: Pos over 5 vars + const; wpos: list of 5 Pos over (m, E). Returns the form over (m, E) + const."""
    f = [F(0), F(0), F(0)]
    for i in range(5):
        for j in range(3): f[j] += form5.f[i] * wpos[i].f[j]
    f[2] += form5.f[5]
    return f

def show(f, names=('m', 'E')):
    s = []
    for q, nm in zip(f[:2], names):
        if q: s.append(f"{q}{nm}")
    s.append(str(f[2]))
    return ' + '.join(s)

def show5(f):
    nm = ['w1', 'w2', 'w3', 'w4', 'E']
    s = [f"{q}{n}" for q, n in zip(f[:5], nm) if q]
    if f[5]: s.append(str(f[5]))
    return ' + '.join(s)

if __name__ == '__main__':
    cut = int(sys.argv[1])
    cache = sys.argv[2] if len(sys.argv) > 2 else f'../ewroutes_{cut}.json'
    if os.path.exists(cache):
        routes = [tuple(x) for x in json.load(open(cache))]
    else:
        import ewroutes as EW
        r, lost = EW.explore(0.5, cut)
        routes = [(list(h), list(o), float(p)) for (h, o), p in sorted(r.items(), key=lambda x: -x[1])]
        json.dump(routes, open(cache, 'w'))
        print(f"{len(routes)} routes into G W W W W within {cut} bits, lost {float(lost):.2e}")
    P5 = {x: pass5(x) for x in 'PQ'}
    for idx, (shapes, outs, meas) in enumerate(routes):
        md = route_model(shapes, outs)
        if md is None: print(idx, 'geometry fails'); continue
        C = coset_from(md.cong)
        mk = md.marks()
        assert md.shape() == 'GWWWW', md.shape()
        wpos = [p for t, p in mk[1:]] + [md.W]
        print(f"\n#{idx} measure {meas:.2e}, coset index 2^{C.index_bits():.0f}; route {' '.join(shapes)}")
        print("   G W W W W at  " + ' | '.join(show(p.f) for p in wpos))
        # residues of each wall coordinate that the route fixes: largest 2^j with w determined mod 2^j on the coset
        for letter in 'PQ':
            C2 = coset_from(md.cong)
            for k, (form5, res, mod) in enumerate(P5[letter]):
                f = subst(form5, wpos)
                M, c, den = frac_row(f, 2)
                if not C2.impose(M, den * res - c, den * mod, reduce=False):
                    print(f"   {letter}: condition {k + 1} of {len(P5[letter])} fails: {show5(form5.f)} = {res} mod {mod}"
                          f"   i.e. {show(f)} = {res} mod {mod}")
                    break
            else:
                print(f"   {letter}: all {len(P5[letter])} conditions consistent")
