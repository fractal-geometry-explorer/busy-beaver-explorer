import sys, math
import mixdrop
from fractions import Fraction as F
from lattice import lll, lg
K = int(sys.argv[1])
for word in sys.argv[2:]:
    w = mixdrop.expand(word); scale = F(2) ** max(220, 4 * len(w) + 80)
    C, err, m = mixdrop.coset(w, scale)
    if C is None: print(word, err); continue
    bl = sorted(round(lg(sum(a * a for a in v)) / 2, 1) for v in C.B)
    mk = m.marks(); Rf = m.W - mk[-1][1]
    halv = -math.log2(abs(Rf.f[4]))
    print(f"{word}: index 2^{C.index_bits():.0f}, basis 2^{bl}, halvings of E {halv:.1f}", flush=True)
