"""Routes from a free GMM state (m, E) into the one-extra-wall loop state G W W W W, enumerated exactly to a bit cut;
for each, test which forced words of the extra-wall loop (P, Q and all two-letter words) the 2-D coset allows.
usage: ewroutes.py cut_bits"""
import sys, copy, collections, math
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch
from gmmreturn import start
from conc import Model, Pos
from lattice import Coset as LCoset
from mixsolve import P_out, Q_out, P_sh, Q_sh

def explore(ratio, cut_bits, max_rounds=200):
    m0 = start(ratio); c0 = Coset([0, 1], [[2, 0], [0, 2]])
    stack = [(m0, c0, [], 0, ())]
    routes = collections.defaultdict(F); lost = F(0)
    while stack:
        ms, cs, forced, rd, hist = stack.pop()
        m = copy.deepcopy(ms); c = cs.copy(); m.setup_tree(c); m.forced = forced
        try:
            m.do_round()
        except Branch:
            if cs.bits + len(forced) + 1 > cut_bits: lost += F(1, 2 ** (cs.bits + len(forced))); continue
            stack.append((ms, cs, forced + [0], rd, hist)); stack.append((ms, cs, forced + [2], rd, hist)); continue
        except AssertionError:
            continue
        if m.halted or m.bad: continue
        sh = m.shape(); mk = m.marks(); h2 = hist + (sh,)
        if sh == 'GM' and mk[1][1].v == m.W.v - 2: continue
        if sh == 'GMM' and mk[2][1].v == m.W.v - 2: continue
        if sh == 'GWWWW': routes[(h2, tuple(m.outcomes))] += F(1, 2 ** c.bits)
        if rd + 1 >= max_rounds: lost += F(1, 2 ** c.bits); continue
        stack.append((m, c, [], rd + 1, h2))
    return routes, lost

def consistent(shapes, outs, word, ratio=0.5, E_ex=2 ** 40 + 1):
    m_ex = int(E_ex * ratio) // 2 * 2; sc = F(2) ** (4 * len(word) + 100)
    md = Model(2)
    md.W = Pos([F(0), F(1), F(0)], F(E_ex) * sc)
    md.add('G', md.const(1)); md.add('M', Pos([F(1), F(0), F(0)], F(m_ex) * sc)); md.add('M', md.W - 2)
    md.force = list(outs)
    for x in word: md.force += (P_out if x == 'P' else Q_out)
    for want in list(shapes):
        md.do_round()
        if md.bad or md.shape() != want: return 'geometry'
    for x in word:
        for want in (P_sh if x == 'P' else Q_sh):
            md.do_round()
            if md.bad or md.shape() != want: return 'geometry'
    C = LCoset(2)
    for pform, res, mod in md.cong:
        f = pform.f; den = 1
        for q in f: den = den * q.denominator // math.gcd(den, q.denominator)
        if not C.impose([int(q * den) for q in f[:2]], den * res - int(f[2] * den), den * mod, reduce=False): return 'inconsistent'
    if not C.impose([1, 0], 0, 2, reduce=False) or not C.impose([0, 1], 1, 2, reduce=False): return 'inconsistent'
    return 'ok'

if __name__ == '__main__':
    cut = int(sys.argv[1])
    routes, lost = explore(0.5, cut)
    tot = sum(routes.values())
    print(f"routes into G W W W W within {cut} bits: {len(routes)}, measure {float(tot):.3e}, lost {float(lost):.3e}")
    words = ['P', 'Q', 'PP', 'PQ', 'QP', 'QQ']
    summary = collections.Counter()
    for (h, o), p in sorted(routes.items(), key=lambda x: -x[1]):
        res = {w: consistent(h, o, w) for w in words}
        ok = [w for w in words if res[w] == 'ok']
        summary[tuple(ok)] += 1
        if ok: print(f"  measure {float(p):.2e}: allows {ok}; route {' '.join(h)}")
    print("routes by the set of words their coset allows:", dict(summary))
