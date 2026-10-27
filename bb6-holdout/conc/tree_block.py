import sys
from fractions import Fraction as F
from tree4 import *
Lmax = int(sys.argv[1]); cut = int(sys.argv[2])
SC = 2 ** 200
E = SC; r = (SC * 3 // 10) & ~1; D = (SC // 200) | 1; R = E - D
m = TModel(3)
m.W = Pos([F(0), F(0), F(1), F(0)], F(E))
m.add('G', m.const(1)); m.add('B', Pos([F(1), F(0), F(0), F(0)], F(r))); m.add('W', Pos([F(0), F(1), F(0), F(0)], F(R)))
m.run = []
# coset: r even, R odd, E even  (x0 = parities, B = 2I)
c = Coset([0, 1, 0], [[2, 0, 0], [0, 2, 0], [0, 0, 2]])
reach, npaths, lost = run_tree(m, c, Lmax, cut)
print(f"paths {npaths}, mass lost to the cut {float(lost):.3e}")
for l in range(1, Lmax + 1): print(f"  P(run >= {l:2d}) = {float(reach[l]):.4e}" + (f"   ratio {float(reach[l-1]/reach[l]):.2f}" if l > 1 and reach[l] else ""))
