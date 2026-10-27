"""Build the drop-route halting tape for a word at width 2^K with a pinned final end distance, report the hybsim
prediction (steps), and write the bare tape for tmfast."""
import sys, math
from fractions import Fraction as F
import mixdrop
from lattice import babai, lll
from buildtape import build
sys.path.insert(0, '../rec'); import hybsim
word, K, T, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
w = mixdrop.expand(word); scale = F(2) ** max(200, 4 * len(w) + 80)
C, err, m = mixdrop.coset(w, scale)
E = 2 ** K; t = [F(g * E, mixdrop.geo[4]) for g in mixdrop.geo]
mk = m.marks(); Rf = m.W - mk[-1][1]; D = 1
for q in Rf.f: D = D * q.denominator // math.gcd(D, q.denominator)
co = [int(q * D) for q in Rf.f[:5]]; c5 = int(Rf.f[5] * D)
assert C.impose(co, T * D - c5, D * 2 ** (K + 8))
Rt = Rf.f[5] + sum(a * b for a, b in zip(Rf.f[:5], t)); t[3] += (T - Rt) / Rf.f[3]
C.B = lll(C.B)
x = [p + q for p, q in zip(C.x0, babai(C.B, [u - v for u, v in zip(t, C.x0)]))]
print("walls", x[:4], "width", x[4], "E mod 6", x[4] % 6)
marks = [('G', 1)] + [('W', p) for p in x[:4]]
res = hybsim.run(hybsim.config_from(marks, x[4]), max_rounds=2000, log=lambda *a: None)
print("hybsim:", res['result'], res.get('rule', ''), 'rounds', res['rounds'], 'steps', res.get('steps'))
open(out, 'w').write(build(marks, x[4]))
