"""The cycle as a walk on GMM states: from a GMM state (free m, E), each branch ends at the next GMM state (growth
6t in E) or at the clean tape (record E growth). From the branch list: P(clean), mean growth per return, and the
exact mean jump of the clean-tape map implied by the walk."""
import sys, copy, collections
from fractions import Fraction as F
from conc import Pos, fmt
from tree4 import TModel, Coset, Branch
from gmmreturn import start
def explore(ratio, cut_bits, max_rounds):
    m0 = start(ratio); c0 = Coset([0, 1], [[2, 0], [0, 2]])
    stack = [(m0, c0, [], 0)]
    gmm = collections.defaultdict(F); clean = collections.defaultdict(F); lost = F(0)
    while stack:
        ms, cs, forced, rd = stack.pop()
        m = copy.deepcopy(ms); c = cs.copy(); m.setup_tree(c); m.forced = forced
        try:
            m.do_round()
        except Branch:
            if cs.bits + len(forced) + 1 > cut_bits: lost += F(1, 2 ** (cs.bits + len(forced))); continue
            stack.append((ms, cs, forced + [0], rd)); stack.append((ms, cs, forced + [2], rd)); continue
        except AssertionError:
            lost += F(1, 2 ** c.bits); continue
        if m.halted or m.bad: lost += F(1, 2 ** c.bits); continue
        sh = m.shape(); mk = m.marks(); W = m.W
        if sh == 'GM' and mk[1][1].v == W.v - 2:
            assert W.f[0] == 0 and W.f[1] == 1
            clean[(int(W.f[2]), rd + 1)] += F(1, 2 ** c.bits); continue
        if sh == 'GMM' and mk[2][1].v == W.v - 2:
            gmm[(int(W.f[2]), rd + 1)] += F(1, 2 ** c.bits); continue
        if rd + 1 >= max_rounds: lost += F(1, 2 ** c.bits); continue
        stack.append((m, c, [], rd + 1))
    return gmm, clean, lost
if __name__ == '__main__':
    gmm, clean, lost = explore(float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
    pg = sum(gmm.values()); pc = sum(clean.values())
    eg = sum(p * g for (g, r), p in gmm.items()); ec = sum(p * g for (g, r), p in clean.items())
    rg = sum(p * r for (g, r), p in gmm.items()); rc = sum(p * r for (g, r), p in clean.items())
    print(f"P(GMM) {float(pg):.6f}  P(clean) {float(pc):.6f}  lost {float(lost):.2e}")
    print(f"mean E growth on a GMM step {float(eg / pg):.4f}, on the final step {float(ec / pc):.4f}; mean rounds {float(rg / pg):.3f} / {float(rc / pc):.3f}")
    # cycle from clean tape n (even): round 1 gives GMM with E = 2n + 11; walk: K GMM steps then a clean step
    # expected total growth = 5 (first round) + (pg/pc) * mean GMM growth + mean clean growth; jump = growth / 2
    tot = 5 + (pg / pc) * (eg / pg) + ec / pc
    print(f"implied mean jump for even n: {float(tot / 2):.4f}")
    print("clean-step growths:", sorted(((g, float(p)) for (g, r), p in clean.items()), key=lambda x: -x[1])[:10])
