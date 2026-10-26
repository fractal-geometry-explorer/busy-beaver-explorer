"""2-adic density of the integer points satisfying congruences  form(x) = res (mod 4)  with dyadic-rational forms.
Returns the number of bits fixed: log2 of the index of the solution coset."""
from fractions import Fraction as F
def v2(x):
    if x == 0: return 10**9
    c = 0
    while x % 2 == 0: x //= 2; c += 1
    return c
def bits_fixed(cong, nvar):
    rows = []; mods = []
    for pform, res, mod in cong:
        form = pform.f
        den = 1
        for a in form: den = max(den, a.denominator)
        # form = (M.x + c)/den, den a power of 2; need M.x + c = den*res (mod den*mod)
        M = [int(a * den) for a in form[:nvar]]
        rows.append(M); mods.append(den * mod)
    S = max(v2(m) for m in mods)
    A = [[x * (2 ** S // m) for x in row] for row, m in zip(rows, mods)]
    MOD = 2 ** S
    A = [[x % MOD for x in row] for row in A]
    # 2-adic Smith form: pick entry of least valuation as pivot
    e = []
    rws = [r[:] for r in A]
    cols = list(range(nvar))
    while cols and rws:
        best = None
        for i, r in enumerate(rws):
            for j in cols:
                if r[j] % MOD:
                    vv = v2(r[j])
                    if best is None or vv < best[0]: best = (vv, i, j)
        if best is None: break
        vv, i, j = best; e.append(vv)
        piv = rws[i][j]; u = piv >> vv          # odd unit
        uinv = pow(u, -1, MOD)
        prow = rws.pop(i)
        newr = []
        for r in rws:
            if r[j] % MOD:
                f = ((r[j] >> vv) * uinv) % MOD
                r = [(a - f * b) % MOD for a, b in zip(r, prow)]
            newr.append(r)
        rws = newr
        # column elimination is implied (we drop column j)
        cols.remove(j)
        for r in rws: r[j] = 0
    return sum(S - min(x, S) for x in e), S

def solve_info(cong, nvar):
    """(bits fixed, solvable?) for the inhomogeneous system."""
    rows = []
    S = 0
    tmp = []
    for pform, res, mod in cong:
        form = pform.f; den = 1
        for a in form: den = max(den, a.denominator)
        M = [int(a * den) for a in form[:nvar]]; c = int(form[nvar] * den)
        tmp.append((M, den * res - c, den * mod)); S = max(S, v2(den * mod))
    MOD = 2 ** S
    rws = [[x * (MOD // m) % MOD for x in M] + [(b * (MOD // m)) % MOD] for M, b, m in tmp]
    cols = list(range(nvar)); bits = 0; ok = True
    while cols:
        best = None
        for i, r in enumerate(rws):
            for j in cols:
                if r[j] % MOD:
                    vv = v2(r[j])
                    if best is None or vv < best[0]: best = (vv, i, j)
        if best is None: break
        vv, i, j = best; bits += S - vv
        u = rws[i][j] >> vv; uinv = pow(u, -1, MOD); prow = rws.pop(i)
        if v2(prow[nvar]) < vv and prow[nvar] % MOD: ok = False
        for k, r in enumerate(rws):
            if r[j] % MOD:
                f = ((r[j] >> vv) * uinv) % MOD
                rws[k] = [(a - f * b) % MOD for a, b in zip(r, prow)]
        cols.remove(j)
    for r in rws:
        if r[nvar] % MOD: ok = False
    return bits, ok, S
