import copy
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form
from conc import fmt
SC = 2 ** 300
for forced in ([0], [0, 0], [0, 2], [0, 0, 0], [0, 0, 2]):
    m = TModel(1); m.W = Pos([F(1), F(0)], F(SC)); m.add('G', m.const(1)); m.add('M', Pos([F(1), F(-2)], F(SC - 2)))
    c = Coset([6], [[2]]); m.setup_tree(c); m.forced = forced[:]
    out = []
    for i in range(6):
        try: m.do_round()
        except Branch: out.append("BRANCH"); break
        out.append(m.shape())
        if m.bad or m.halted: out.append(f"bad{m.bad}"); break
    print(forced, out, c.x0, c.B)
