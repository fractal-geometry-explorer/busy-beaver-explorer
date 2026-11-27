"""fates.py: tables from the exhaustive fates of c/fates.c (every tape B(x, y) with level n = 2x + y <= M).

    gcc -O2 -o fates c/fates.c && ./fates 32768 ex.bin hl.bin && python3 py/fates.py ex.bin hl.bin 32768

Table 1: for bands of start levels, the fraction of tapes that halt below level M, and on how many different orbits
the others leave level M (two tapes are on the same orbit there iff they leave on the same tape).
Table 2: F(L), the fraction of the tapes of levels [L/2, L) that halt on a tape of level in [L, 2L); c/back.c computes
the same number backward from the halting tapes and must agree.
"""
import sys
import numpy as np

EX, HL, M = sys.argv[1], sys.argv[2], int(sys.argv[3])
ex = np.memmap(EX, dtype=np.uint32, mode='r'); hl = np.memmap(HL, dtype=np.uint32, mode='r')
off = np.concatenate([[0], np.cumsum(np.arange(2, M + 2) // 2)])


def lev(a, n): return np.array(a[off[n - 2]:off[n - 2] + n // 2])        # index x - 1


blank = int(ex[0])                                                        # B(1, 0), the tape 8 steps after blank
print('M = %d' % M)
print('start levels | tapes (x even) | halt below M | orbits left | shares of the largest | share of the blank-tape orbit')
n0 = 64
while n0 < M:
    n1 = n0 + n0 // 8
    e = np.concatenate([lev(ex, n)[1::2] for n in range(n0, n1)])
    sv = e[e != 0]; u, c = np.unique(sv, return_counts=True); c = np.sort(c)[::-1]
    print('%d..%d | %d | %.4f | %d | %s | %.4f' % (n0, n1 - 1, len(e), (e == 0).mean(), len(u),
          ' '.join('%.3f' % (k / len(e)) for k in c[:3]), (e == blank).mean()))
    n0 *= 2
print()
print('L | tapes of levels [L/2, L) | F(L) all | F(L) x even | halting tapes that take any')
L = 64
while 2 * L <= M:
    h = np.concatenate([lev(hl, n) for n in range(L // 2, L)])
    xe = np.concatenate([np.arange(1, n // 2 + 1) % 2 == 0 for n in range(L // 2, L)])
    k = (h >= L) & (h < 2 * L)
    print('%d | %d | %.5f | %.5f | %d' % (L, len(h), k.mean(), k[xe].mean(), len(np.unique(h[k]))))
    L *= 2
