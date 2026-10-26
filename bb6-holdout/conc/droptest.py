"""From the one-extra-wall loop state (G 1, W a, W b, W c, W d, end E, all free), force one P pass, then follow every
branch exactly and record the routes by which the run leaves: back to G W W W W (loop resumes) or down to G W W W
(the plain loop).  For routes into G W W W, test how many forced plain passes the coset still allows."""
import sys, copy, collections, io, contextlib
from fractions import Fraction as F
from conc import Pos, fmt
from tree4 import TModel, Coset, Branch
from mixsolve import P_out, P_sh, Q_out, Q_sh, geo
with contextlib.redirect_stdout(io.StringIO()):
    from cyccost import CYC, outs as L_out
SC = 2 ** 200
big = [F(v) * SC for v in geo]
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
def start():
    m = TModel(5)
    for i in range(4): m.add('W', Pos([F(int(i == j)) for j in range(5)] + [F(0)], big[i]))
    m.W = Pos([F(int(j == 4)) for j in range(5)] + [F(0)], big[4]); m.add('G', m.const(1))
    c = Coset([1, 0, 1, 0, 1], [[2 * int(i == j) for j in range(5)] for i in range(5)])
    return m, c
def force_word(m, c, outs, shapes):
    m = copy.deepcopy(m); c = c.copy(); m.__class__ = Forced; m.coset = c; m.req = list(outs)
    try:
        for want in shapes:
            m.do_round()
            if m.bad or m.halted or m.shape() != want: return None, None
    except (ValueError, AssertionError, Branch):
        return None, None
    m.__class__ = TModel
    return m, c
def plain_passes(m, c, kmax=4):
    best = 0
    for k in range(1, kmax + 1):
        mm, cc = force_word(m, c, L_out * k, CYC * k)
        if mm is None: break
        best = k
    return best
def explore(m0, c0, cut_bits, max_rounds):
    b0 = c0.bits
    stack = [(m0, c0, [], 0, ())]
    routes = collections.defaultdict(F); lost = F(0)
    while stack:
        ms, cs, forced, rd, hist = stack.pop()
        m = copy.deepcopy(ms); c = cs.copy(); m.setup_tree(c); m.forced = forced
        try:
            m.do_round()
        except Branch:
            if cs.bits - b0 + len(forced) + 1 > cut_bits: lost += F(1, 2 ** (cs.bits - b0 + len(forced))); continue
            stack.append((ms, cs, forced + [0], rd, hist)); stack.append((ms, cs, forced + [2], rd, hist)); continue
        except AssertionError:
            continue
        p = F(1, 2 ** (c.bits - b0))
        if m.halted: routes[('HALT', hist)] += p; continue
        if m.bad: continue
        sh = m.shape(); h2 = hist + (sh,)
        if sh == 'GWWWW':
            routes[('resume', h2)] += p; continue
        if sh == 'GWWW':
            k = plain_passes(m, c)
            routes[(f'plain x{k}', h2)] += p; continue
        if rd + 1 >= max_rounds: routes[('other', ())] += p; continue
        stack.append((m, c, [], rd + 1, h2))
    return routes, lost
if __name__ == '__main__':
    cut = int(sys.argv[1]); maxr = int(sys.argv[2])
    m, c = start()
    m, c = force_word(m, c, P_out, P_sh)
    print("after one forced P pass: coset bits", c.bits)
    routes, lost = explore(m, c, cut, maxr)
    print("lost (cut)", float(lost))
    agg = collections.defaultdict(F)
    for (kind, h), p in routes.items(): agg[kind] += p
    print({k: f'{float(v):.3e}' for k, v in sorted(agg.items())})
    for (kind, h), p in sorted(routes.items(), key=lambda x: -x[1])[:40]:
        print(f"  {kind:9s} p={float(p):.3e} (2^{F(p).denominator.bit_length() - 1})  {' '.join(h)}")
