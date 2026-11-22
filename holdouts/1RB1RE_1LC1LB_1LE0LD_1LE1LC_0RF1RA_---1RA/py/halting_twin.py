"""A halting list with the same stack as the real run: the counter m alone decides.

At step 181,429 the run from blank tape is at the visit [6, 4, u^368, L0] with the stack L0 = 4 u^17 4 u^3 4 1.
For m large the epoch [6, 4, u^m, L] -> [6, 4, u^m', L'] gives an L' that depends only on L and on the parity of m,
and m' = (3m + c)/2 with c depending only on (L, parity) (py/adversary.py).  Choosing the parities freely, 247 odd
epochs in a row use the stack up (each odd epoch takes one unit from the first counter of the stack, which then
converts and refills from the next one) and leave the stack 1036; an even epoch then halts.

This script (1) follows that parity word with the epoch map, (2) solves for the residue m0 mod 2^248 that makes the
real m sequence follow it, and (3) runs the exact run-stack simulator (py/runstack.py, every machine step, sweeps
in bulk) from [6, 4, u^m0, L0] and checks that the machine halts there.

So the list [6, 4, u^m0, L0] of the domain D halts while [6, 4, u^368, L0] is the real run: an invariant that
excludes the halt has to separate the two, i.e. see m modulo 2^248 (at least); the stack and its run parities are
the same.  usage: python3 halting_twin.py
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from adversary import f, L0, fm
from runstack import Sim, B

word = [1] * 247 + [0]
L = L0; cs = []
for k, p in enumerate(word):
    r, m = f(L, p, 4 * 10 ** 9)
    if r == 'HALT':
        assert k == len(word) - 1; break
    r2, m2 = f(L, p, 10 ** 7)
    c = 2 * m - 3 * (4 * 10 ** 9 + p)
    assert r2 == r and 2 * m2 - 3 * (10 ** 7 + p) == c          # affine in m, same stack, at two sizes
    cs.append(c); L = r
print("epoch map: 247 odd epochs take the stack", fm(L0), "to", fm(L), "and an even epoch then halts")

def follows(m, K):
    for k in range(K):
        if m % 2 != word[k]: return False
        if k == len(word) - 1: return True
        if (3 * m + cs[k]) % 2: return False
        m = (3 * m + cs[k]) // 2
    return True
m0 = 0
for k in range(len(word)):
    if not follows(m0, k + 1): m0 += 2 ** k
    assert follows(m0, k + 1)
print("m0 =", m0, "(mod 2^248)")

t0 = time.time(); s = Sim(); s.st = B; s.d = -1
s.R = [list(e) for e in reversed(L0)] + [[1, m0], [4, 1], [6, 1]]
ne = 0; par = []
while True:
    if s.at_visit():
        R = s.R
        if len(R) >= 3 and R[-1] == [6, 1] and R[-2] == [4, 1] and R[-3][0] == 1: ne += 1; par.append(R[-3][1] % 2)
        s.sweep()
    if not s.step(): break
    assert ne <= len(word), "no halt"
assert par == word
print("machine from [6, 4, u^m0, %s]: HALTS after %d epochs, %d steps (a number of %d bits); %.1f s"
      % (fm(L0), ne, s.steps + 1, (s.steps + 1).bit_length(), time.time() - t0))
