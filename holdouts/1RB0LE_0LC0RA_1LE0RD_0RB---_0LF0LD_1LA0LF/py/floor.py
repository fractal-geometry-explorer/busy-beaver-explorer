"""Floor test and the digit end as a number (README, "Ninth pass").  Token rules of py/tokz.py, exact integers.

usage: python3 py/floor.py zshift ROUNDS [EVERY=20]
       python3 py/floor.py c2 ROUND
       python3 py/floor.py cut ROUND KEEP CUT_HEIGHT ROUNDS [EVERY=20]

zshift: Z_k is the digit-only end of the round tape read as a binary number, most significant digit at the far end.
  In every round whose defect dies before Z, Z_(k+1) = 16 Z_k + e_k; printed: |Z|, m, the bit length of e_k, and
  how many top digits of Z_(k+1) equal those of 16 Z_k (about m).
c2: the second-order term of the value law, r 2^(2m) with r = v(W_k) - (16/15 - c 2^-m), and its best rational
  approximations (none is small).
cut: take round ROUND's tape, keep its first KEEP words, drop every word up to the first word of Z below height
  CUT_HEIGHT, and run ROUNDS rounds from the result.  Printed: the need of each round's defect against the 2^m
  visits it gets, its death height, and the smallest death height so far.  Stops if a defect survives.
"""
import sys
from fractions import Fraction as Fr

sys.setrecursionlimit(1000000)
from conveyor import heights, visit, next_round, lead, value, zstart
from fuel import round_need

C1 = {0: Fr(288, 127), 1: Fr(145, 127)}


def tapes(R):
    """Yield (k, round tape, clean tape after the visit, death index) for k = 6..R."""
    s, k = list('LLLzLLOLOI'), 6
    while k <= R:
        W, di = visit(s)
        while W and W[-1] == 'O': W.pop()
        yield k, s, W, di
        s, k = next_round(W), k + 1


def zint(W, z):
    n = 0
    for i in range(len(W) - 1, z - 1, -1): n = 2 * n + (W[i] == 'I')
    return n


def zshift(R, every):
    for k, s, W, di in tapes(R):
        if k < 40 or k % every: continue
        zs, zw = zstart(s), zstart(W)
        if di is None or di >= zs or abs(zw - zs) > 1:
            print(k, 'defect died inside Z'); continue
        Z, Zn = zint(s, zs), zint(W, zw)
        e = Zn - 16 * Z
        top = Zn.bit_length() - abs(e).bit_length()
        print(k, '|Z|', len(s) - zs, 'm', lead(s), 'bits of e', abs(e).bit_length(), 'top digits equal to 16 Z', top)


def c2(R):
    for k, s, W, di in tapes(R):
        if k < R - 1: continue
        m = lead(s)
        r2 = (value(W, heights(W)) - (Fr(16, 15) - C1[k % 2] / 2 ** m)) * 2 ** (2 * m)
        print(k, 'r 2^2m =', float(r2))
        for d in (10 ** 4, 10 ** 6, 10 ** 8):
            q = r2.limit_denominator(d)
            print('   best fraction with denominator <=', d, ':', q, ' error', float(abs(r2 - q)))


def cut(K, keep, cuth, R, every):
    for k, s, W, di in tapes(K):
        pass
    s = next_round(W)
    hs, m, z = heights(s), lead(s), zstart(s)
    c = next(i for i in range(z, len(s)) if hs[i] < cuth)
    s = s[:keep] + s[c:]
    print('round', K + 1, 'tape: kept', keep, 'words, dropped', c - keep, 'words, from height', hs[c], 'on; m =', m)
    low = None
    for j in range(R):
        m, need = round_need(s)
        W, di = visit(s)
        hs = heights(W)
        if any(t in 'x1z' for t in W): print(j, 'DEFECT SURVIVED'); return
        hd = hs[di] if di is not None and di < len(hs) else None
        if hd is not None: low = hd if low is None else min(low, hd)
        if need > 2 ** m: print(j, 'NEED', need, 'ABOVE 2^m, m =', m); return
        if j % every == 0 or j == R - 1:
            print(j, 'm', m, 'need', need, 'death height', hd, '2m', 2 * m, 'lowest death height so far', low)
        s = next_round(W)


if __name__ == '__main__':
    a = sys.argv
    if a[1] == 'zshift': zshift(int(a[2]), int(a[3]) if len(a) > 3 else 20)
    elif a[1] == 'c2': c2(int(a[2]))
    elif a[1] == 'cut': cut(int(a[2]), int(a[3]), int(a[4]), int(a[5]), int(a[6]) if len(a) > 6 else 20)
