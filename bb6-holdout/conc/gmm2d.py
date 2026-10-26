"""Can a GMM round start (gap at 1, one marker m, end marker at E - 2; m and E free) halt the machine at a large scale?
Take a route that real clean cycles use from a GMM state into the extra-wall loop, append a pass word, solve the
congruences as a 2-D lattice coset in (m, E), and test the nearest point at width 2^K in the integer model."""
import sys, math
from fractions import Fraction as F
from conc import Model, Pos
from lattice import Coset, babai, lll, lg
from mixsolve import P_out, Q_out, P_sh, Q_sh
def route_from_gmm(n0):
    m = Model(1); m.W = m.const(2 * n0 + 6); m.add('G', m.const(1)); m.add('M', m.W - 2)
    snaps = []
    for r in range(4000):
        mk = m.marks(); snaps.append((m.shape(), [p.v for t, p in mk[1:]], m.W.v, len(m.outcomes)))
        if m.shape() == 'GWWWW': break
        m.do_round()
    # last GMM (marker + end marker) before the GWWWW state
    for i in range(len(snaps) - 1, -1, -1):
        sh, pos, W, o = snaps[i]
        if sh == 'GMM' and pos[1] == W - 2: break
    else: return None
    shapes = [s[0] for s in snaps[i + 1:]]
    return snaps[i], m.outcomes[snaps[i][3]: snaps[-1][3]], shapes
def symbolic(gmm, outs, shapes, word, scale_exp):
    sh, pos, W, _ = gmm
    md = Model(2)
    md.W = Pos([F(0), F(1), F(0)], F(W) * 2 ** scale_exp)
    md.add('G', md.const(1)); md.add('M', Pos([F(1), F(0), F(0)], F(pos[0]) * 2 ** scale_exp)); md.add('M', md.W - 2)
    md.force = list(outs)
    for x in word: md.force += (P_out if x == 'P' else Q_out)
    for want in shapes:
        md.do_round()
        if md.bad or md.shape() != want: return None, f"route: got {md.shape()} want {want}"
    for x in word:
        for want in (P_sh if x == 'P' else Q_sh):
            md.do_round()
            if md.bad or md.shape() != want: return None, f"{x}: got {md.shape()} want {want}"
    C = Coset(2)
    for pform, res, mod in md.cong:
        f = pform.f; den = max(q.denominator for q in f)
        if not C.impose([int(q * den) for q in f[:2]], den * res - int(f[2] * den), den * mod, reduce=False): return None, "inconsistent"
    if not C.impose([1, 0], 0, 2) or not C.impose([0, 1], 1, 2): return None, "parity"
    C.B = lll(C.B)
    return C, None
if __name__ == '__main__':
    n0 = int(sys.argv[1]); words = sys.argv[2:]
    r = route_from_gmm(n0)
    gmm, outs, shapes = r
    print("route from GMM:", ' '.join(shapes), "| GMM m/E =", round(gmm[1][0] / gmm[2], 4))
    for word in words:
        C, err = symbolic(gmm, outs, shapes, word, 4 * len(word) + 120)
        if C is None: print(word, err); continue
        bl = [round(lg(sum(a * a for a in v)) / 2, 1) for v in C.B]
        print(f"word {word or '-'}: 2-D coset index 2^{C.index_bits():.1f}, reduced basis lengths 2^{bl}")
