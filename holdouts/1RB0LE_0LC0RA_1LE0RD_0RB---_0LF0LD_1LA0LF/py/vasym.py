"""The conserved value at the start of each round, exactly: v_k = 1/15 - c_k 2^(-k/2) + O(2^-k).

usage: python3 py/vasym.py ROUNDS            (ROUNDS = 420 takes about a minute)

Runs the token rules (py/tokz.py) and evaluates the value v of the tape at the start of every round with exact
fractions (py/tokv.py). Checks, for every round k from 40 on, that

    v_k = 1/15 - (290/127) 2^-(k+2)/2 + r_k  (k even),   v_k = 1/15 - (288/127) 2^-(k+1)/2 + r_k  (k odd),

with |r_k| < 512 * 2^-k (and < 64 * 2^-k from round 80 on), and prints r_k 2^k (it settles near -33.69 for even k and -42.13 for odd k: a second term
C 2^-k whose constant is not a small fraction) and how far r_k 2^k still moves (about 2^-k/2 relative: the
irregular third term).

Since 1/15 = 0.000100010001... and 1/127 has period 7, this is why the top of the tape (the highest digits of
the counter, at its far end) is the expansion of 1/15 for about k/2 digits and then has period 28 for about
k/2 more.
"""
import sys
from fractions import Fraction as Fr
sys.setrecursionlimit(1000000)
import tokz
import tokv
from tokz import T


def c1(k):
    return Fr(290, 127) / Fr(2) ** ((k + 2) // 2) if k % 2 == 0 else Fr(288, 127) / Fr(2) ** ((k + 1) // 2)


R = int(sys.argv[1]) if len(sys.argv) > 1 else 420
T[:] = list('LLLzLLOLOI')
bad = 0
prev = {}
for k in range(6, R + 1):
    tokz.An(1, 0); T.insert(0, 'x'); tokz.norm()
    while T and T[-1] == 'O': T.pop()
    v = tokv.val(T)
    if k < 40: continue
    r = v - Fr(1, 15) + c1(k)
    x = r * Fr(2) ** k
    if abs(x) >= (64 if k >= 80 else 512): bad += 1; print('round', k, 'BOUND FAILS', float(x))
    if k % 20 == 0 or k > R - 2:
        mv = float(x - prev[k - 2]) if k - 2 in prev else float('nan')
        print('round %d: r_k 2^k = %.12f   change since round k-2: %.3e' % (k, float(x), mv))
    prev[k] = x
print('rounds 40..%d: bound |r_k| < 512 2^-k (64 2^-k from round 80) fails %d times' % (R, bad))
