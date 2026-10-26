"""2-adic elementary divisors of the coset lattice of a pass word (k = 1 loop): the largest one is what a generic
one-parameter family pays in binary digits, the rest is the chance that the family is consistent at all."""
import sys
from mixsolve import coset, set_scale
from snf2 import v2
def elem_divisors_2adic(B):
    # 2-adic Smith form of an integer matrix: repeatedly pivot on the entry of least valuation
    M = [row[:] for row in B]; n = len(M); out = []
    rows = list(range(n)); cols = list(range(len(M[0])))
    while rows and cols:
        best = None
        for i in rows:
            for j in cols:
                if M[i][j]:
                    vv = v2(M[i][j])
                    if best is None or vv < best[0]: best = (vv, i, j)
        if best is None: break
        vv, i, j = best; out.append(vv); piv = M[i][j]
        for r in rows:
            if r != i and M[r][j]:
                # eliminate with rational factor M[r][j]/piv (2-adically integral since v2 >= vv); keep integers by scaling by odd part
                f_num = M[r][j]; f_den = piv
                g = 1
                M[r] = [a * (f_den >> vv) - b * (f_num >> vv) for a, b in zip(M[r], M[i])]   # multiply row r by odd unit
        for c in cols:
            if c != j: M[i][c] = 0
        rows.remove(i); cols.remove(j)
    return sorted(out)
for word in sys.argv[1:]:
    set_scale(len(word)); C = coset(word)
    if C is None: print(word, "inconsistent"); continue
    e = elem_divisors_2adic(C.B)
    print(f"{word:24s} index 2^{sum(e)}  elementary divisors 2^{e}  -> one-parameter cost {max(e)} digits, consistency 2^-{sum(e) - max(e)}")
