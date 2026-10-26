"""Search for conserved quantities of the machine of the form
    f = sum_i g(c[i-1], c[i], c[i+1]; i mod p) + H(state, c[j-1], c[j], c[j+1]; j mod p)   (head at j),
modulo a prime q (and over Q via a large prime).  Generalises the earlier search (single-cell weights, p <= 6, q in
2,3,5,7) to triple patterns, larger p and more moduli.  Invariants are compared by their values on random
configurations, which removes the gauge freedom (telescoping sums) automatically.
usage: invsearch2.py p q [q ...]"""
import sys, random
import numpy as np
TM = {('A', 0): (1, 1, 'B'), ('A', 1): (0, 1, 'E'), ('B', 0): (1, -1, 'C'), ('B', 1): (0, 1, 'A'), ('C', 0): (1, -1, 'A'),
      ('C', 1): (1, -1, 'D'), ('D', 0): (1, -1, 'A'), ('E', 0): (0, 1, 'F'), ('E', 1): (0, -1, 'B'), ('F', 0): (0, -1, 'D'), ('F', 1): (1, 1, 'E')}
STATES = 'ABCDEF'
p = int(sys.argv[1]); qs = [int(x) for x in sys.argv[2:] if x.isdigit()]
idx = {}
def G(x, y, z, r): return idx.setdefault(('g', x, y, z, r % p), len(idx))
def Hh(q, x, y, z, r): return idx.setdefault(('h', q, x, y, z, r % p), len(idx))
for r in range(p):
    for x in (0, 1):
        for y in (0, 1):
            for z in (0, 1):
                G(x, y, z, r)
                for q in STATES: Hh(q, x, y, z, r)
NU = len(idx)
rows = []
for (q, v), (v2, d, q2) in TM.items():
    for r in range(p):
        for ctx in range(16):
            cm2, cm1, c1, c2 = (ctx >> 3) & 1, (ctx >> 2) & 1, (ctx >> 1) & 1, ctx & 1
            row = {}
            def add(i, s): row[i] = row.get(i, 0) + s
            # triples centred at j-1, j, j+1 before and after the write
            add(G(cm2, cm1, v, r - 1), -1); add(G(cm1, v, c1, r), -1); add(G(v, c1, c2, r + 1), -1)
            add(G(cm2, cm1, v2, r - 1), 1); add(G(cm1, v2, c1, r), 1); add(G(v2, c1, c2, r + 1), 1)
            add(Hh(q, cm1, v, c1, r), -1)
            if d == 1: add(Hh(q2, v2, c1, c2, r + 1), 1)
            else: add(Hh(q2, cm2, cm1, v2, r - 1), 1)
            rows.append(row)
for r in range(p): rows.append({G(0, 0, 0, r): 1})      # the per-cell constants are gauge: force g(000; r) = 0
if '--nonbr' in sys.argv:    # head term without neighbour dependence
    for r in range(p):
        for q in STATES:
            for y in (0, 1):
                for x in (0, 1):
                    for z in (0, 1):
                        if (x, z) != (0, 0): rows.append({Hh(q, x, y, z, r): 1, Hh(q, 0, y, 0, r): -1})
M = np.zeros((len(rows), NU), dtype=np.int64)
for i, row in enumerate(rows):
    for j, s in row.items(): M[i, j] = s
# random test configurations for comparing invariants by value
random.seed(5)
tests = []
for _ in range(400):
    L = random.randint(6, 40); cells = [random.randint(0, 1) for _ in range(L)]; j = random.randrange(1, L - 1); q = random.choice(STATES)
    tests.append((cells, j, q))
def valvec(w):
    out = []
    for cells, j, q in tests:
        c = [0, 0] + cells + [0, 0]; s = 0
        for i in range(1, len(c) - 1): s += w[idx[('g', c[i - 1], c[i], c[i + 1], (i - 2) % p)]]
        jj = j + 2; s += w[idx[('h', q, c[jj - 1], c[jj], c[jj + 1], j % p)]]
        out.append(s)
    return out
def kernel_mod(M, q):
    A = M.copy() % q; m, n = A.shape; piv = []; r = 0
    for c in range(n):
        pr = None
        for i in range(r, m):
            if A[i, c] % q: pr = i; break
        if pr is None: continue
        A[[r, pr]] = A[[pr, r]]; inv = pow(int(A[r, c]), -1, q); A[r] = (A[r] * inv) % q
        nz = np.nonzero(A[:, c])[0]
        for i in nz:
            if i != r: A[i] = (A[i] - A[i, c] * A[r]) % q
        piv.append(c); r += 1
        if r == m: break
    free = [c for c in range(n) if c not in set(piv)]
    basis = []
    for fcol in free:
        w = np.zeros(n, dtype=np.int64); w[fcol] = 1
        for i, pc in enumerate(piv): w[pc] = (-A[i, fcol]) % q
        basis.append(w)
    return basis
def rank_mod(V, q):
    A = np.array(V, dtype=np.int64) % q
    if A.size == 0: return 0
    m, n = A.shape; r = 0
    for c in range(n):
        pr = None
        for i in range(r, m):
            if A[i, c] % q: pr = i; break
        if pr is None: continue
        A[[r, pr]] = A[[pr, r]]; inv = pow(int(A[r, c]), -1, q); A[r] = (A[r] * inv) % q
        for i in range(m):
            if i != r and A[i, c]: A[i] = (A[i] - A[i, c] * A[r]) % q
        r += 1
        if r == m: break
    return r
# the known invariant (number of 1s plus 2 for B and 1 for C..F) as a value vector
known = np.zeros(NU, dtype=np.int64)
for key, i in idx.items():
    if key[0] == 'g': known[i] = key[2]
    else: known[i] = {'A': 0, 'B': 2, 'C': 1, 'D': 1, 'E': 1, 'F': 1}[key[1]]
kv = valvec(known)
print(f'p = {p}: {NU} unknowns, {len(rows)} equations')
for q in qs:
    basis = kernel_mod(M, q)
    vals = [valvec(w) for w in basis]
    rk = rank_mod(vals, q) if vals else 0
    rk_known = rank_mod(vals + [kv], q) if vals else rank_mod([kv], q)
    # constants: a head term equal for all states and contexts is an invariant with constant value: count it
    const_rank = rank_mod(vals + [[1] * len(tests)], q) - rk if vals else 0
    print(f'  mod {q}: kernel dimension {len(basis)}, distinct invariants (by values) {rk}; adding the known 1s-count invariant raises it by {rk_known - rk}; the constant is {"among them" if const_rank == 0 else "not among them"}; so new ones beyond constant and known: {rk - (1 if const_rank == 0 else 0) - (0 if (rk_known - rk) else 1)}')

if __name__ == '__main__' and '--show' in sys.argv:
    q = 2147483647
    basis = kernel_mod(M, q)
    names = {i: k for k, i in idx.items()}
    def lift(x): x = int(x) % q; return x - q if x > q // 2 else x
    for bi, w in enumerate(basis):
        vv = valvec(w)
        if all(v == vv[0] for v in vv): continue     # constant
        terms_g = [(names[i], lift(w[i])) for i in range(NU) if w[i] and names[i][0] == 'g']
        terms_h = [(names[i], lift(w[i])) for i in range(NU) if w[i] and names[i][0] == 'h']
        print(f'kernel vector {bi}: values on first tests {[lift(v) for v in vv[:6]]}')
        print('   g terms:', ', '.join(f'{k[1]}{k[2]}{k[3]}:{c:+d}' for k, c in terms_g))
        print('   H terms:', ', '.join(f'{k[1]}|{k[2]}{k[3]}{k[4]}:{c:+d}' for k, c in terms_h))
