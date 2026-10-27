"""Fixed lines x*(E) = alpha*E + beta of the k=1 pass maps P and Q (T(x*(E)) = x*(E+24)), and whether they agree."""
from fractions import Fraction as F
def solve(A, y):
    n = len(A); M = [list(map(F, A[i])) + [F(y[i])] for i in range(n)]
    for c in range(n):
        p = next(i for i in range(c, n) if M[i][c] != 0); M[c], M[p] = M[p], M[c]
        pv = M[c][c]; M[c] = [x / pv for x in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0:
                f = M[i][c]; M[i] = [x - f * z for x, z in zip(M[i], M[c])]
    return [M[i][n] for i in range(n)]
# x = (a, b, c, d); x' = M x + u E + t
P = dict(M=[[0, F(1,64), F(1,64), 0], [0, F(1,64), F(5,64), F(3,16)], [0, 0, F(1,16), F(1,4)], [0, 0, 0, F(1,16)]],
         u=[0, F(1,4), F(11,16), F(15,16)], t=[F(271,64), F(899,64), F(179,8), F(369,16)])
Q = dict(M=[[0, F(1,128), 0, 0], [0, F(9,128), F(1,32), F(1,8)], [0, F(1,16), F(1,32), F(3,16)], [0, 0, 0, F(1,16)]],
         u=[0, F(1,4), F(11,16), F(15,16)], t=[F(257,64), F(855,64), F(701,32), F(369,16)])
for name, T in (('P', P), ('Q', Q)):
    IM = [[(1 if i == j else 0) - T['M'][i][j] for j in range(4)] for i in range(4)]
    al = solve(IM, T['u']); be = solve(IM, [T['t'][i] - 24 * al[i] for i in range(4)])
    print(name, 'alpha', [str(x) for x in al], 'beta', [str(x) for x in be])
