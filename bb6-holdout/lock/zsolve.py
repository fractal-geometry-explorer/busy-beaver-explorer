"""Integer solvability of a linear system A z = b (A integer m × n, b integer), by column Hermite reduction."""
from math import gcd
def solvable(A, b):
    A = [list(r) for r in A]; b = list(b); m = len(A); n = len(A[0])
    col = 0
    for i in range(m):
        # make A[i][col+1:] zero by column operations among columns col..n-1
        for j in range(col + 1, n):
            while A[i][j] != 0:
                q = A[i][col] // A[i][j] if A[i][j] else 0
                for r in range(m): A[r][col] -= q * A[r][j]
                for r in range(m): A[r][col], A[r][j] = A[r][j], A[r][col]
        if A[i][col] != 0: col += 1
        # row i now: entries only in columns < col
    # forward substitution: A is lower-trapezoidal in the sense above
    z = [0] * n; c = 0
    for i in range(m):
        s = b[i] - sum(A[i][j] * z[j] for j in range(c))
        if c < n and A[i][c] != 0 and (i == 0 or any(A[i][c] != 0 for _ in [0])):
            # pivot in column c iff this row created it
            pass
        # determine whether row i has a pivot at column c
        if c < n and A[i][c] != 0:
            if s % A[i][c]: return False
            z[c] = s // A[i][c]; c += 1
        elif s != 0: return False
    return True
