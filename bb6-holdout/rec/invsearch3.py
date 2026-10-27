"""Conserved quantities with cell weights on windows of width W (odd) and position classes mod p, head term depending
on the state and the cell under the head.  usage: invsearch3.py W p q [q ...]"""
import sys, random
import numpy as np
TM = {('A', 0): (1, 1, 'B'), ('A', 1): (0, 1, 'E'), ('B', 0): (1, -1, 'C'), ('B', 1): (0, 1, 'A'), ('C', 0): (1, -1, 'A'),
      ('C', 1): (1, -1, 'D'), ('D', 0): (1, -1, 'A'), ('E', 0): (0, 1, 'F'), ('E', 1): (0, -1, 'B'), ('F', 0): (0, -1, 'D'), ('F', 1): (1, 1, 'E')}
STATES = 'ABCDEF'
W = int(sys.argv[1]); p = int(sys.argv[2]); qs = [int(x) for x in sys.argv[3:] if x.isdigit()]; h = W // 2
idx = {}
def G(pat, r): return idx.setdefault(('g', pat, r % p), len(idx))
def Hh(q, v, r): return idx.setdefault(('h', q, v, r % p), len(idx))
for r in range(p):
    for pat in range(1 << W): G(pat, r)
    for q in STATES:
        for v in (0, 1): Hh(q, v, r)
NU = len(idx)
rows = []
span = 2 * h          # context cells j-span .. j+span excluding j
for (q, v), (v2, d, q2) in TM.items():
    for r in range(p):
        for ctx in range(1 << (2 * span)):
            cells = {}
            bit = 0
            for off in range(-span, span + 1):
                if off == 0: continue
                cells[off] = (ctx >> bit) & 1; bit += 1
            row = {}
            def add(i, s): row[i] = row.get(i, 0) + s
            for centre in range(-h, h + 1):           # windows containing cell j
                pat0 = 0; pat1 = 0
                for k in range(-h, h + 1):
                    off = centre + k
                    c0 = v if off == 0 else cells[off]; c1 = v2 if off == 0 else cells[off]
                    pat0 = pat0 * 2 + c0; pat1 = pat1 * 2 + c1
                add(G(pat0, r + centre), -1); add(G(pat1, r + centre), 1)
            add(Hh(q, v, r), -1); add(Hh(q2, cells[d], r + d), 1)
            rows.append(row)
for r in range(p): rows.append({G(0, r): 1})
M = np.zeros((len(rows), NU), dtype=np.int64)
for i, row in enumerate(rows):
    for j, s in row.items(): M[i, j] = s
random.seed(5); tests = []
for _ in range(300):
    L = random.randint(6, 40); cells = [random.randint(0, 1) for _ in range(L)]; j = random.randrange(1, L - 1); q = random.choice(STATES); tests.append((cells, j, q))
def valvec(w):
    out = []
    for cells, j, q in tests:
        c = [0] * (W + 1) + cells + [0] * (W + 1); s = 0
        for i in range(h, len(c) - h):
            pat = 0
            for k in range(-h, h + 1): pat = pat * 2 + c[i + k]
            s += w[idx[('g', pat, i % p)]]
        s += w[idx[('h', q, cells[j], (j + W + 1 - h) % p)]]; out.append(s)
    return out
def rref_rank(A, q):
    A = A % q; m, n = A.shape; r = 0; piv = []
    for c in range(n):
        pr = None
        for i in range(r, m):
            if A[i, c]: pr = i; break
        if pr is None: continue
        A[[r, pr]] = A[[pr, r]]; A[r] = (A[r] * pow(int(A[r, c]), -1, q)) % q
        nz = np.nonzero(A[:, c])[0]
        for i in nz:
            if i != r: A[i] = (A[i] - A[i, c] * A[r]) % q
        piv.append(c); r += 1
        if r == m: break
    return A, piv, r
def kernel_mod(M, q):
    A, piv, r = rref_rank(M.copy(), q); n = M.shape[1]; ps = set(piv)
    basis = []
    for fcol in [c for c in range(n) if c not in ps]:
        w = np.zeros(n, dtype=np.int64); w[fcol] = 1
        for i, pc in enumerate(piv): w[pc] = (-A[i, fcol]) % q
        basis.append(w)
    return basis
known = np.zeros(NU, dtype=np.int64)
for key, i in idx.items():
    if key[0] == 'g': known[i] = (key[1] >> h) & 1
    else: known[i] = {'A': 0, 'B': 2, 'C': 1, 'D': 1, 'E': 1, 'F': 1}[key[1]]
kv = valvec(known)
print(f'window {W}, p = {p}: {NU} unknowns, {len(rows)} equations')
for q in qs:
    basis = kernel_mod(M, q); vals = [valvec(w) for w in basis]
    rk = rref_rank(np.array(vals, dtype=np.int64), q)[2] if vals else 0
    rk_k = rref_rank(np.array(vals + [kv], dtype=np.int64), q)[2]
    rk_c = rref_rank(np.array(vals + [[1] * len(tests)], dtype=np.int64), q)[2]
    new = rk - (1 if rk_c == rk else 0) - (1 if rk_k == rk else 0)
    print(f'  mod {q}: distinct invariants {rk}; new beyond the constant and the 1s count: {new}')
if '--show' in sys.argv:
    q = 2147483647; basis = kernel_mod(M, q); names = {i: k for k, i in idx.items()}
    def lift(x): x = int(x) % q; return x - q if x > q // 2 else x
    for bi, w in enumerate(basis):
        vv = valvec(w)
        if all(v == vv[0] for v in vv): continue
        print(f'vector {bi}: test values {[lift(v) for v in vv[:8]]}')
        print('   g:', ', '.join(f'{k[1]:0{W}b}:{lift(w[i]):+d}' for i, k in names.items() if w[i] and k[0] == 'g'))
        print('   H:', ', '.join(f'{k[1]}{k[2]}:{lift(w[i]):+d}' for i, k in names.items() if w[i] and k[0] == 'h'))
