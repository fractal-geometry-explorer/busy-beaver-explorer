"""Search for conserved quantities of 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE of the form
   sum over cells f(value, index mod p) + g(state, head index mod p)  (mod m), with f(0, r) = 0."""
import itertools
TM = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE".split('_')
TR = {}
for si, s in enumerate(TM):
    for y in (0, 1):
        x = s[3 * y: 3 * y + 3]
        if x != '---': TR[(si, y)] = (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65)
def nullspace_mod_p(rows, n, p):
    # Gaussian elimination over GF(p), p prime
    rows = [[v % p for v in r] for r in rows]; piv = []; r = 0
    for c in range(n):
        k = next((i for i in range(r, len(rows)) if rows[i][c]), None)
        if k is None: continue
        rows[r], rows[k] = rows[k], rows[r]; inv = pow(rows[r][c], -1, p); rows[r] = [v * inv % p for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]: f = rows[i][c]; rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[r])]
        piv.append(c); r += 1
    free = [c for c in range(n) if c not in piv]; basis = []
    for fc in free:
        v = [0] * n; v[fc] = 1
        for i, pc in enumerate(piv): v[pc] = (-rows[i][fc]) % p
        basis.append(v)
    return basis
for per in (1, 2, 3, 4, 6):
    for m in (2, 3, 5, 7):
        # unknowns: f(1, r) for r < per  (per of them), g(s, r) (6*per)
        n = per + 6 * per
        fi = lambda r: r % per
        gi = lambda s, r: per + s * per + (r % per)
        rows = []
        for (s, y), (w, d, s2) in TR.items():
            for r in range(per):
                row = [0] * n
                if w == 1: row[fi(r)] += 1
                if y == 1: row[fi(r)] -= 1
                row[gi(s2, r + d)] += 1; row[gi(s, r)] -= 1
                rows.append(row)
        ns = nullspace_mod_p(rows, n, m)
        # remove the trivial invariant: g constant (all states equal, f = 0) shifts by a constant
        nontriv = [v for v in ns if any(v[:per])]
        if nontriv:
            print(f"period {per}, mod {m}: {len(ns)} solutions, {len(nontriv)} with f != 0; e.g. f(1,r) = {nontriv[0][:per]}, "
                  f"g = {[nontriv[0][per + s * per: per + (s + 1) * per] for s in range(6)]}")
