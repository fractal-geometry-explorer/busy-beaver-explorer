import json, copy, math, sys
from fractions import Fraction as F
from conc import Model, Pos
from ewlock2 import consistent
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from cyccost import CYC, outs as L_out
routes = [json.loads(l) for l in open('../routetree_routes30.txt')]
sfx = [(a, b) for a, b, w in json.load(open('../entry_suffixes.json')) if a.count('GWWWW') == 1 and a[-1] == 'GWWWW']
def fam_of(ri, p, si):
    r = routes[ri]; E_ex = 2 ** 40 + 1; m_ex = int(E_ex * r['ratio']) // 2 * 2; sc = F(2) ** 200
    md = Model(2); md.W = Pos([F(0), F(1), F(0)], F(E_ex) * sc)
    md.add('G', md.const(1)); md.add('M', Pos([F(1), F(0), F(0)], F(m_ex) * sc)); md.add('M', md.W - 2)
    md.force = list(r['outs']) + L_out * p + list(sfx[si][1])
    for want in r['shapes'] + CYC * p + sfx[si][0]:
        md.do_round(); assert md.shape() == want
    mk = md.marks(); fam = [list(q.f) for t, q in mk[1:]] + [list(md.W.f)]
    return [[f[0] * 2, f[1] * 2, f[2] + f[1]] for f in fam]
if __name__ == '__main__':
    for ri, p, si in [(208, 0, 11), (293, 0, 11), (5, 2, 2)]:
        fam = fam_of(ri, p, si); frontier = ['']; L = 0
        while frontier and L < 8:
            nxt = [w + x for w in frontier for x in 'PQ' if consistent(fam, 2, w + x)]
            if not nxt: break
            frontier = nxt; L += 1
        print(ri, p, si, 'longest word', L, frontier[:6])
    def run_h(m, E):
        md = Model(0); md.W = md.const(E); md.add('G', md.const(1)); md.add('M', md.const(m)); md.add('M', md.W - 2)
        ends = []
        for r in range(400):
            ne = len(md.endd); md.do_round()
            if md.halted or md.bad: break
            ends += [d.v for rr, d in md.endd[ne:]]
            mk = md.marks()
            if r > 2 and len(mk) <= 3 and mk[-1][0] == 'M' and mk[-1][1].v == md.W.v - 2: break
        return math.log2(E / min(ends))
    for m, E in [(793076764, 41575487909), (17972945948, 50165422501), (54480167964, 180088183205), (1738202608, 19137579705), (664460784, 12963564217), (18846612876, 89471941005)]:
        print(m, E, f"width 2^{math.log2(E):.1f}: closest approach {run_h(m, E):.2f} halvings")

