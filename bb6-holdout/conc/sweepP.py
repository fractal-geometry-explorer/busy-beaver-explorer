"""Same construction with the extra-wall loop alone (P^m, no detour): where does it stop working?"""
import sys, os
os.environ['MOD3'] = '1'
import mixsolve
from mixsolve import coset, set_scale, babai
from lattice import lll, lg
from fractions import Fraction as F
sys.path.insert(0, '../rec')
import hybsim
geo = mixsolve.geo
for K in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    m = int((K - 3.6) // 4); word = 'P' * m
    set_scale(len(word)); C = coset(word); R = 2 ** (4 * m + 1)
    C.impose([0, 0, 0, -1, 1], R + 1, 2 ** (K + 8)); C.B = lll(C.B)
    longest = max(lg(sum(v * v for v in row)) / 2 for row in C.B)
    E = 2 ** K; t = [F(geo[0] * E, geo[4]), F(geo[1] * E, geo[4]), F(geo[2] * E, geo[4]), F(E - 1 - R), F(E)]
    x = [p + q for p, q in zip(C.x0, babai(C.B, [u - v for u, v in zip(t, C.x0)]))]
    if not (0 < x[0] < x[1] < x[2] < x[3] < x[4]):
        print(K, word, f"longest basis vector 2^{longest:.1f}: nearest coset point is not a valid tape", flush=True); continue
    try:
        res = hybsim.run(hybsim.config_from([('G', 1)] + [('W', p) for p in x[:-1]], x[-1]), max_rounds=20 * K + 200, log=lambda *a: None)
    except AssertionError as e:
        print(K, "invalid tape", e, flush=True); continue
    res.pop('cfg')
    print(K, word, f"longest basis vector 2^{longest:.1f}", res['result'], 'rel', [round(v / x[-1], 3) for v in x[:-1]], flush=True)
