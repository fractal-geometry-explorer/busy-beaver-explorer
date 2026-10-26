import sys
from conc import *
from cyccost import setup, CYC, outs, vals, big
from snf2 import v2
from fractions import Fraction as F
sys.setrecursionlimit(10000)
NC = 12
m = setup(big, False); m.force = outs * NC
for c in range(NC):
    for want in CYC: m.do_round()
cons = []
for pform, res, mod in m.cong:
    form = pform.f; den = max(a.denominator for a in form)
    M = [int(a * den) for a in form[:4]]; cc = int(form[4] * den)
    cons.append((M, den * res - cc, v2(den * mod)))
S = max(c[2] for c in cons); MOD = 1 << S
def solve_b(E, c):
    # unknowns a, b mod 2^S with E, c fixed; digit-by-digit
    def ok(a, b, k):
        x = [a, b, c, E]
        for M, t, s in cons:
            q = min(k, s)
            if (sum(p * y for p, y in zip(M, x)) - t) % (1 << q): return False
        return True
    def dfs(a, b, k):
        if k == S: return (a, b)
        for bits in range(4):
            a2 = a | ((bits & 1) << k); b2 = b | (((bits >> 1) & 1) << k)
            if ok(a2, b2, k + 1):
                r = dfs(a2, b2, k + 1)
                if r: return r
        return None
    return dfs(0, 0, 0)
def ratrec(a, m):
    import math
    r0, r1 = m, a % m; s0, s1 = 0, 1; B = math.isqrt(m // 2)
    while r1 > B:
        q = r0 // r1; r0, r1 = r1, r0 - q * r1; s0, s1 = s1, s0 - q * s1
    return F(r1, s1)
import random
random.seed(5)
for E, c in [(0, -1), (2**10, 2**10 - 1), (0, 2**49 - 1 + 2**50), (2**20 * 6, 2**20 * 6 - 1), (8, 7 + 2**49)]:
    sol = solve_b(E % MOD, c % MOD)
    if sol is None: print(E, c, "no solution"); continue
    a, b = sol
    print(f"E = {E}, c = {c}: b = {ratrec(b, MOD)} (mod 2^{S})")
