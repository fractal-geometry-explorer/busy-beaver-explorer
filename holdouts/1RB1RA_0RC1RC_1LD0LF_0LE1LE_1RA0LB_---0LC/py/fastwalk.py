"""Fast exact iteration of y -> ceil(3y/2) (or floor), returning parities, by divide and conquer on the low bits.

run(l, L): (y_L, bits) with y_L the L-th iterate of l and bit t of `bits` the parity of the t-th iterate (t < L).
Uses the identity  f^s(2^L h + l) = 3^s 2^(L-s) h + f^s(l)  for s <= L, valid for f = ceil(3y/2) and floor(3y/2).
"""
import sys
try:
    import gmpy2
    mpz = gmpy2.mpz
    popcount = gmpy2.popcount
except ImportError:  # plain Python ints work too, only slower
    mpz = int
    def popcount(x): return int(x).bit_count()

CEIL = True
_P3 = {}
def p3(n):
    v = _P3.get(n)
    if v is None:
        v = mpz(3) ** n
        _P3[n] = v
    return v

BASE = 48
def run(l, L):
    if L <= BASE:
        y = int(l); bits = 0
        if CEIL:
            for t in range(L):
                if y & 1: bits |= 1 << t; y = (3 * y + 1) >> 1
                else: y = (3 * y) >> 1
        else:
            for t in range(L):
                if y & 1: bits |= 1 << t
                y = (3 * y) >> 1
        return mpz(y), mpz(bits)
    L1 = L // 2
    m1 = (mpz(1) << L1) - 1
    g1, b1 = run(l & m1, L1)
    y = p3(L1) * (l >> L1) + g1
    L2 = L - L1
    m2 = (mpz(1) << L2) - 1
    g2, b2 = run(y & m2, L2)
    return p3(L2) * (y >> L2) + g2, b1 | (b2 << L1)

def bit(b, t): return (int(b >> t) & 1)
