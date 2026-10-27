"""The hand-built halting tapes of the notes ("Halting at every scale"): word P^a Q P^b, end distance pinned to
R = 2^(4m+1), E ≡ 0 (mod 3), nearest coset point to a fixed geometry at width 2^K.  Rebuilt with the same
construction (`../conc/sweepK.py`) and run on the proved model (`Harness.lean`, the zipper model of the Lean round
theorem) instead of the Python simulator.  usage: python3 mixed_halt_lean.py K1,K2,...  [word-mode: aqb | pure]"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'conc'))
os.environ['MOD3'] = '1'
import mixsolve
from mixsolve import coset, set_scale, babai
from lattice import lll
from fractions import Fraction as F
from verify_maps import lean_runs
geo = mixsolve.geo
Ks = [int(k) for k in sys.argv[1].split(',')]
mode = sys.argv[2] if len(sys.argv) > 2 else 'aqb'
for K in Ks:
    m = int((K - 3.6) // 4); a = (m - 1) // 2; b = m - 1 - a
    word = 'P' * a + 'Q' + 'P' * b if mode == 'aqb' else 'P' * m
    set_scale(len(word)); C = coset(word)
    if C is None: print(K, word, "inconsistent", flush=True); continue
    R = 2 ** (4 * m + 1)
    if not C.impose([0, 0, 0, -1, 1], R + 1, 2 ** (K + 8)): print(K, "R constraint inconsistent", flush=True); continue
    C.B = lll(C.B)
    Ew = 2 ** K; t = [F(geo[0] * Ew, geo[4]), F(geo[1] * Ew, geo[4]), F(geo[2] * Ew, geo[4]), F(Ew - 1 - R), F(Ew)]
    x = [int(p + q) for p, q in zip(C.x0, babai(C.B, [u - v for u, v in zip(t, C.x0)]))]
    if not (0 < x[0] < x[1] < x[2] < x[3] < x[4]): print(K, word, "point out of order", flush=True); continue
    (run,) = lean_runs([x], 8 * m + 10)
    shapes = [l.split()[0] for l in run]
    want = sum(((mixsolve.P_sh if c == 'P' else mixsolve.Q_sh) for c in word), [])
    follows = shapes[:8 * m] == want
    print(f"K={K} word=P^{a}QP^{b}" if mode == 'aqb' else f"K={K} word=P^{m}", f"E={x[4]} (2^{x[4].bit_length() - 1}) E%6={x[4] % 6}",
          f"follows word on proved model: {follows}; ends: {run[-1] if run else '?'} after {len(run)} rounds", flush=True)
