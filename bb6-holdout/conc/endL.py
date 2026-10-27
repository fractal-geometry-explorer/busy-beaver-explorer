"""For every closing path of the exact endgame search, the residue class of the left countdown L at that pass start,
L = 147b + 280E - 392c - 578 with c = E - R - 1, and the smallest |L| it allows (L = 3 mod 7; even after a pass)."""
import math, endsym
from fractions import Fraction as F
for R in range(2, 1101, 2): endsym.search(R, 0)
def Lform(R): return [F(0), F(147), F(-112), F(392 * R - 186)]   # coefficients on a, b, E and the constant
res = {}
for R, x0, B, shapes in endsym.CLOSES:
    f = Lform(R)
    L0 = f[3] + sum(f[i] * x0[i] for i in range(3))
    g = [sum(f[i] * B[i][k] for i in range(3)) for k in range(3)]
    mod = 0
    for v in g: mod = math.gcd(mod, int(v))
    r0 = int(L0) % mod
    def minabs(even):
        best = None
        for x in range(-100000, 100001):
            if x % mod == r0 and x % 7 == 3 and (not even or x % 2 == 0):
                if best is None or abs(x) < abs(best): best = x
        return best
    m0, m1 = minabs(False), minabs(True)
    print(f"R {R}: L = {r0} mod {mod}; smallest |L| {abs(m0) if m0 is not None else None} (no pass before), "
          f"{abs(m1) if m1 is not None else None} (after a pass); 3 log2 R - 2 log2|L| = "
          f"{3*math.log2(R) - 2*math.log2(abs(m0)):.2f} / {(3*math.log2(R) - 2*math.log2(abs(m1))) if m1 else float('nan'):.2f}; "
          f"rounds: {' '.join(shapes)}")
