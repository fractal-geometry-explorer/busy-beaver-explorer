"""Structure of the n-coefficients on a clean tape: run the mark model with n symbolic (positions = lam*N + c, N = 2n+6)
and print, at selected rounds, each mark's lam in binary and its constant c."""
import sys
from fractions import Fraction as F
from conc import Model, Pos
def bstr(x):
    # binary expansion of a dyadic rational
    num, den = x.numerator, x.denominator
    s = 0
    while den > 1: den //= 2; s += 1
    ip = num >> s if num >= 0 else -((-num) >> s)
    fr = num - (ip << s)
    b = bin(fr)[2:].zfill(s) if s else ''
    return f"{ip}." + b if s else f"{ip}"
n0 = int(sys.argv[1]); w0 = 2 * n0 + 6
m = Model(1)
# use N = 2n + 6 as the variable: W = N
m.W = Pos([F(1), F(0)], w0); m.add('G', m.const(1)); m.add('M', m.W - 2)
rounds = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 6
for r in range(1, rounds + 1):
    ne = len(m.endd); m.do_round(); mk = m.marks()
    ends = [int(d.v) for rr, d in m.endd[ne:]]
    if ends or r == rounds:
        print(f"round {r} {m.shape()} end meetings {ends}")
        for t, p in mk[1:]:
            lam, c = p.f
            print(f"    {t} lam={bstr(lam):>40s} c={c}")
        print(f"    end lam={bstr(m.W.f[0])} c={m.W.f[1]}")
    if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == m.W.v - 2: break
