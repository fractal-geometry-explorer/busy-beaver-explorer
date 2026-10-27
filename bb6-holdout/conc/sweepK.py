"""For each width exponent K: m = floor((K - 3.6)/4) passes, word P^a Q P^b (a + b + 1 = m), end distance fixed to
R = E - d - 1 = 2^(4m+1) exactly, mod-3 condition; run the real machine through the proven rules."""
import sys, os
os.environ['MOD3'] = '1'
import mixsolve
from mixsolve import coset, set_scale, babai
from lattice import lll
from fractions import Fraction as F
sys.path.insert(0, '../rec')
import hybsim
geo = mixsolve.geo
lo, hi, st = map(int, sys.argv[1:4])
for K in range(lo, hi + 1, st):
    m = int((K - 3.6) // 4); a = (m - 1) // 2; b = m - 1 - a
    if a < 1: continue
    word = 'P' * a + 'Q' + 'P' * b
    set_scale(len(word)); C = coset(word)
    if C is None: print(K, word, "inconsistent", flush=True); continue
    R = 2 ** (4 * m + 1)
    if not C.impose([0, 0, 0, -1, 1], R + 1, 2 ** (K + 8)): print(K, "R constraint inconsistent", flush=True); continue
    C.B = lll(C.B)
    E = 2 ** K; t = [F(geo[0] * E, geo[4]), F(geo[1] * E, geo[4]), F(geo[2] * E, geo[4]), F(E - 1 - R), F(E)]
    x = [p + q for p, q in zip(C.x0, babai(C.B, [u - v for u, v in zip(t, C.x0)]))]
    if not (0 < x[0] < x[1] < x[2] < x[3] < x[4]): print(K, "point out of order", flush=True); continue
    try:
        res = hybsim.run(hybsim.config_from([('G', 1)] + [('W', p) for p in x[:-1]], x[-1]), max_rounds=20 * K + 200, log=lambda *a: None)
    except AssertionError as e:
        print(K, "invalid tape", e, flush=True); continue
    res.pop('cfg')
    print(K, f"P^{a} Q P^{b}", res['result'], res.get('rule', ''), 'rounds', res['rounds'], 'E mod 6', x[-1] % 6,
          'rel', [round(v / x[-1], 3) for v in x[:-1]], flush=True)
