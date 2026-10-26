"""1-D exact branching from a clean tape class n = n0 (mod 2^s0): follow the cycle; runs that break before round R0
are reset, the first run alive at round R0 is followed until it breaks.  Reports P(that run reaches L meetings)."""
import sys, copy
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form
n0 = int(sys.argv[1]); s0 = int(sys.argv[2]); R0 = int(sys.argv[3]); Lmax = int(sys.argv[4]); cut = int(sys.argv[5])
SC = 2 ** 300
m = TModel(1)
# variable x = w = 2n + 6 ; virtual geometry at a scaled-up point keeping n0's residue irrelevant
w0 = 2 * n0 + 6
m.W = Pos([F(1), F(0)], F(SC))
m.add('G', m.const(1)); m.add('M', Pos([F(1), F(-2)], F(SC - 2)))
m.run = []; m.rd_done = 0
c = Coset([w0], [[2 ** (s0 + 1)]])
reach = [F(0)] * (Lmax + 2); lost = F(0); npaths = 0
stack = [(m, c, [])]
while stack:
    m0, c0, forced = stack.pop()
    mm = copy.deepcopy(m0); cc = c0.copy(); mm.setup_tree(cc); mm.forced = forced; ne0 = len(mm.endd)
    try: mm.do_round()
    except Branch:
        if cc.bits >= cut or c0.bits + len(forced) + 1 > cut: lost += F(1, 2 ** (c0.bits + len(forced))); continue
        stack.append((m0, c0, forced + [0])); stack.append((m0, c0, forced + [2])); continue
    mm.rd_done += 1
    broken = False
    for (rr, d) in mm.endd[ne0:]:
        if mm.run and pred_form(*mm.run[-1]).f != d.f:
            if mm.rd_done <= R0: mm.run = []
            else: broken = True; break
        mm.run.append((d, cc.decided(d.f)))
    mk = mm.marks(); done = len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == mm.W.v - 2
    if broken or done:
        L = len(mm.run) if mm.rd_done > R0 else 0
        for l in range(1, min(L, Lmax) + 1): reach[l] += F(1, 2 ** cc.bits)
        npaths += 1; print('END', mm.rd_done, mm.shape(), cc.bits, broken, L); continue
    stack.append((mm, cc, []))
print(f"class n = {n0} mod 2^{s0}: paths {npaths}, lost {float(lost):.2e}")
for l in range(1, Lmax + 1):
    if reach[l]: print(f"  P(run alive at round {R0} reaches {l:2d}) = {float(reach[l]):.4e}" + (f"  ratio {float(reach[l-1]/reach[l]):.2f}" if l > 1 else ""))
