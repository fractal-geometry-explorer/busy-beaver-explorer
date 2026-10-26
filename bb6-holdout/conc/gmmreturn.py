"""Return map of the 'GMM' state (gap at 1, marker m, end marker at E - 2): from free (m, E), follow every branch of
the rules until the next GMM state, the clean tape, or a cap.  Records the affine map (m, E) -> (m', E') on each
branch, its probability (2^-bits) and the rounds taken."""
import sys, copy, collections
from fractions import Fraction as F
from conc import Pos, fmt
from tree4 import TModel, Coset, Branch
def start(ratio, scale=2 ** 120):
    E = scale; mv = int(E * ratio) // 2 * 2
    m = TModel(2)
    m.W = Pos([F(0), F(1), F(0)], F(E + 1))
    m.add('G', m.const(1)); m.add('M', Pos([F(1), F(0), F(0)], F(mv))); m.add('M', m.W - 2)
    return m
def explore(ratio, cut_bits, max_rounds):
    m0 = start(ratio)
    c0 = Coset([0, 1], [[2, 0], [0, 2]])          # m even, E odd
    stack = [(m0, c0, [], 0)]
    out = collections.Counter(); prob = collections.defaultdict(F); lost = F(0); maps = {}
    while stack:
        ms, cs, forced, rd = stack.pop()
        m = copy.deepcopy(ms); c = cs.copy(); m.setup_tree(c); m.forced = forced
        try:
            m.do_round()
        except Branch:
            if cs.bits + len(forced) + 1 > cut_bits: lost += F(1, 2 ** (cs.bits + len(forced))); continue
            stack.append((ms, cs, forced + [0], rd)); stack.append((ms, cs, forced + [2], rd)); continue
        except AssertionError as e:
            out['assert'] += 1; continue
        if m.halted or m.bad: out['halt/bad'] += 1; continue
        sh = m.shape(); mk = m.marks()
        if sh == 'GM' and mk[1][1].v == m.W.v - 2:
            out[('clean', rd + 1)] += 1; prob['clean'] += F(1, 2 ** c.bits); continue
        if sh == 'GMM' and mk[2][1].v == m.W.v - 2:
            mm, W = mk[1][1], m.W
            key = (fmt(mm, ['m', 'E']), fmt(W, ['m', 'E']), rd + 1)
            out[('GMM', rd + 1)] += 1; prob['GMM'] += F(1, 2 ** c.bits); maps[key] = maps.get(key, F(0)) + F(1, 2 ** c.bits); continue
        if rd + 1 >= max_rounds: lost += F(1, 2 ** c.bits); out['round cap'] += 1; continue
        stack.append((m, c, [], rd + 1))
    return out, prob, lost, maps
if __name__ == '__main__':
    ratio = float(sys.argv[1]); cut = int(sys.argv[2]); mr = int(sys.argv[3])
    out, prob, lost, maps = explore(ratio, cut, mr)
    print(f"m/E = {ratio}: P(next GMM) = {float(prob['GMM']):.6f}, P(clean) = {float(prob['clean']):.6f}, lost {float(lost):.2e}")
    for (fm, fw, rd), p in sorted(maps.items(), key=lambda x: -x[1])[:25]:
        print(f"   {float(p):.5f}  after {rd:2d} rounds: m' = {fm},  E' = {fw}")

def summary(ratio=0.3, cut=30, mr=120):
    out, prob, lost, maps = explore(ratio, cut, mr)
    nb = len(maps)
    byrounds = collections.Counter()
    for (fm, fw, rd), p in maps.items(): byrounds[fw] += p
    return prob, lost, nb, byrounds
