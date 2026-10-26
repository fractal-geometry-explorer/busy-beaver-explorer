import sys, io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from cyccost import setup, CYC, outs, vals
from fractions import Fraction as F
from lattice import Coset, lll
from snfcost import elem_divisors_2adic
for NC in (1, 2, 3, 4, 6):
    big = [F(v) * 2 ** 220 for v in vals]
    m = setup(big, False); m.force = outs * NC
    for c in range(NC):
        for want in CYC: m.do_round(); assert m.shape() == want
    C = Coset(4)
    for pform, res, mod in m.cong:
        f = pform.f; den = max(a.denominator for a in f)
        C.impose([int(a * den) for a in f[:4]], den * res - int(f[4] * den), den * mod, reduce=False)
    C.B = lll(C.B)
    e = elem_divisors_2adic(C.B)
    print(f"plain loop, {NC} passes: index 2^{sum(e)}, elementary divisors 2^{e}")
