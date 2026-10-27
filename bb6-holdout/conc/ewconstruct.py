"""Construct explicit GMM states (m, E) that follow a GMM-born route into G W W W W and then a given word of
extra-wall passes: the 2-D coset of route + word, its lattice points by width, each run concretely.
usage: ewconstruct.py routes.json route_index word kmin kmax [max_found]"""
import sys, json, math
from fractions import Fraction as F
from conc import Model, Pos
from lattice import Coset as LCoset
import mixsolve as MS
import routeexclude as RX

def word_model(shapes, outs, word, ratio=0.5, E_ex=2 ** 40 + 1):
    m_ex = int(E_ex * ratio) // 2 * 2; sc = F(2) ** (4 * len(word) + 140)
    md = Model(2)
    md.W = Pos([F(0), F(1), F(0)], F(E_ex) * sc)
    md.add('G', md.const(1)); md.add('M', Pos([F(1), F(0), F(0)], F(m_ex) * sc)); md.add('M', md.W - 2)
    md.force = list(outs)
    for x in word: md.force += (MS.P_out if x == 'P' else MS.Q_out)
    want_all = list(shapes) + sum(((MS.P_sh if x == 'P' else MS.Q_sh) for x in word), [])
    for want in want_all:
        md.do_round()
        if md.bad or md.shape() != want: return None, want_all
    return md, want_all

def concrete_shapes(m, E, nr):
    md = Model(0); md.W = md.const(E); md.add('G', md.const(1)); md.add('M', md.const(m)); md.add('M', md.W - 2)
    sh = []
    for r in range(nr):
        md.do_round()
        if md.halted or md.bad: break
        sh.append(md.shape())
    return sh, md

if __name__ == '__main__':
    routes = json.load(open(sys.argv[1])); idx = int(sys.argv[2]); word = sys.argv[3]
    kmin, kmax = int(sys.argv[4]), int(sys.argv[5]); maxf = int(sys.argv[6]) if len(sys.argv) > 6 else 5
    shapes, outs, meas = routes[idx]
    md, want = word_model(shapes, outs, word)
    if md is None: print("geometry fails at ratio 1/2"); sys.exit()
    C = RX.coset_of(md)
    if C is None: print("coset inconsistent"); sys.exit()
    print(f"route #{idx} + {word}: coset index 2^{C.index_bits():.1f}")
    found = 0; tried = 0
    for k in range(kmin, kmax + 1):
        for m, E in RX.points(C, k):
            tried += 1
            sh, mm = concrete_shapes(m, E, len(want) + 12)
            if sh[:len(want)] == want:
                found += 1
                print(f"  k={k}: m = {m}, E = {E} (m/E = {m / E:.4f}) follows the route and {word}; next shapes {' '.join(sh[len(want):len(want) + 12])}")
                if found >= maxf: break
        if found >= maxf: break
    print(f"tried {tried} lattice points, found {found}")
