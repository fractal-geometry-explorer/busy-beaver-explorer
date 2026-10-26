from conc import *
from cyccost import setup, CYC, outs, vals, big
from tree4 import Coset
from fractions import Fraction as F
import sys
NC = int(sys.argv[1])
m = setup(big, False); m.force = outs * NC
for c in range(NC):
    for want in CYC: m.do_round()
# impose in order on Z^4 coset; but the coset routine expects even distances: start from parity class of the sample
co = Coset([vals[0] % 2, vals[1] % 2, vals[2] % 2, vals[3] % 2], [[2,0,0,0],[0,2,0,0],[0,0,2,0],[0,0,0,2]])
for d, res, mod in m.cong:
    ok = co.impose(d.f, res)
    if not ok: print("inconsistent"); break
print("bits beyond parity:", co.bits)
# Hermite normal form of the lattice basis (columns of B)
import itertools
B = [row[:] for row in co.B]
cols = [[B[r][k] for r in range(4)] for k in range(4)]
# lower-triangular HNF by integer column operations
def hnf(cols):
    cols = [c[:] for c in cols]; n = 4
    for r in range(n):
        # among columns r..n-1, gcd-reduce row r
        while True:
            nz = [k for k in range(r, n) if cols[k][r] != 0]
            if len(nz) <= 1: break
            nz.sort(key=lambda k: abs(cols[k][r])); p = nz[0]
            for k in nz[1:]:
                q = cols[k][r] // cols[p][r]; cols[k] = [x - q * y for x, y in zip(cols[k], cols[p])]
        nz = [k for k in range(r, n) if cols[k][r] != 0]
        if nz: k = nz[0]; cols[r], cols[k] = cols[k], cols[r]
        if cols[r][r] < 0: cols[r] = [-x for x in cols[r]]
        for k in range(r):
            if cols[r][r]: q = cols[k][r] // cols[r][r]; cols[k] = [x - q * y for x, y in zip(cols[k], cols[r])]
    return cols
H = hnf(cols)
names = ['a', 'b', 'c', 'E']
print("lattice basis (columns, in a,b,c,E coordinates):")
for k in range(4): print("  ", H[k])
print("x0:", co.x0)
