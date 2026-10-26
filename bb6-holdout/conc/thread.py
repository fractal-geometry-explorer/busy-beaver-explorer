"""Follow one n along its cycle with the class n = n0 (mod 2^s0) as a coset: each test is fresh (reads a new digit;
n's own digit is taken) or implied (fixed by digits already read).  Prints per round the fresh and implied tests."""
import sys
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form
from conc import fmt
n0 = int(sys.argv[1]); s0 = int(sys.argv[2]); R0 = int(sys.argv[3])
w0 = 2 * n0 + 6
class FollowModel(TModel):
    def test_outcome(self, d):
        dec = self.coset.decided(d.f)
        val = int(sum(a * b for a, b in zip(d.f, [F(w0), F(1)])))   # concrete value for this n
        if dec is not None:
            self.log.append(('I', dec, d)); assert dec == val % 4; return dec
        self.coset.impose(d.f, val % 4); self.log.append(('F', val % 4, d)); return val % 4
m = FollowModel(1); m.W = Pos([F(1), F(0)], F(w0)); m.add('G', m.const(1)); m.add('M', Pos([F(1), F(-2)], F(w0 - 2)))
c = Coset([w0], [[2 ** (s0 + 1)]]); m.setup_tree(c); m.log = []
rd = 0; run = []
while True:
    ne0 = len(m.endd); nl0 = len(m.log); m.do_round(); rd += 1
    ev = []
    for (rr, d) in m.endd[ne0:]:
        cont = bool(run) and pred_form(*run[-1]).f == d.f
        if not cont: run = []
        run.append((d, c.decided(d.f))); ev.append(f"END#{len(run)}")
    lg = m.log[nl0:]
    if rd >= R0:
        s = ' '.join(f"{t}{o}" for t, o, d in lg)
        print(f"rd {rd:3d} {m.shape():8s} bits {c.bits:3d}  {' '.join(ev):14s} tests: {s}")
    mk = m.marks()
    if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2: break
print("final bits", c.bits)
