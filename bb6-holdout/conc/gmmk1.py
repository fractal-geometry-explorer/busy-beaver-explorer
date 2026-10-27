"""From a GMM state with free (m, E), follow every branch (2-adic cosets in the two unknowns) and, whenever a branch
reaches the extra-wall state G W W W W, test how many forced passes of P (and P then Q) the 2-D family can still
complete.  Also records plain-loop entries (G W W W followed by the loop) for comparison."""
import sys, copy, collections
from fractions import Fraction as F
from conc import Pos, fmt
from tree4 import TModel, Coset, Branch
from gmmreturn import start
from mixsolve import P_out, Q_out, P_sh, Q_sh
class Forced(TModel):
    def test_outcome(self, d):
        want = self.req.pop(0) if self.req else None
        dec = self.coset.decided(d.f)
        if want is None: raise Branch()
        if dec is not None:
            if dec != want: raise ValueError("inconsistent")
            return dec
        if not self.coset.impose(d.f, want): raise ValueError("inconsistent")
        return want
def passes_possible(model, coset, word_max=4):
    """Max number of consecutive P passes (forced) that the coset allows, and whether P..PQ works."""
    best = 0
    for mpass in range(1, word_max + 1):
        m = copy.deepcopy(model); m.__class__ = Forced; c = coset.copy(); m.coset = c
        m.req = list(P_out) * mpass
        ok = True
        try:
            for p in range(mpass):
                for want in P_sh:
                    m.do_round()
                    if m.bad or m.shape() != want: ok = False; break
                if not ok: break
        except (ValueError, AssertionError):
            ok = False
        except Branch:
            ok = False
        if not ok: break
        best = mpass
    return best
def explore(ratio, cut_bits, max_rounds):
    m0 = start(ratio); c0 = Coset([0, 1], [[2, 0], [0, 2]])
    stack = [(m0, c0, [], 0, ())]
    k1 = collections.Counter(); lost = F(0); seen_routes = {}
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
        if sh == 'GWWWW':
            pp = passes_possible(m, c)
            key = ' '.join(h2[-8:])
            k1[(pp, key)] += F(1, 2 ** c.bits)
            seen_routes.setdefault((pp, key), c.bits)
        if rd + 1 >= max_rounds: lost += F(1, 2 ** c.bits); continue
        stack.append((m, c, [], rd + 1, h2))
    return k1, lost, seen_routes
if __name__ == '__main__':
    k1, lost, sr = explore(float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
    print("lost", float(lost))
    agg = collections.Counter()
    for (pp, key), p in k1.items(): agg[pp] += p
    print("extra-wall entries from GMM by the number of forced P passes the 2-D family can still complete:",
          {k: float(v) for k, v in sorted(agg.items())})
    for (pp, key), p in sorted(k1.items(), key=lambda x: (-x[0][0], -x[1]))[:15]:
        print(f"  passes {pp}  prob {float(p):.3e}  bits {sr[(pp, key)]}  route ...{key}")
