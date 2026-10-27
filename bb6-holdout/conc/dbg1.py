import copy
from fractions import Fraction as F
from tree4 import TModel, Coset, Branch, Pos, pred_form
from conc import fmt
SC = 2 ** 300
m = TModel(1); m.W = Pos([F(1), F(0)], F(SC)); m.add('G', m.const(1)); m.add('M', Pos([F(1), F(-2)], F(SC - 2)))
c = Coset([6], [[2]]); m.setup_tree(c); m.forced = [2, 0, 0, 0, 0, 0, 0]
for i in range(3):
    try: m.do_round()
    except Branch: print("branch at round", i + 1); break
    print(m.shape(), [fmt(p, ['w']) for t, p in m.marks()], 'end', fmt(m.W, ['w']), m.endd, m.path)
