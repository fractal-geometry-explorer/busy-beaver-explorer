"""Backward search in a pclosure certificate: which parts of which pieces lead to a halt.
A region is a piece of a class cut by linear equalities on its variables.  usage: back.py CERT.json [MAXREGIONS]"""
import collections, gzip, itertools, json, sys
from fractions import Fraction as Fr

def parse_form(s, nv):
    k = 0; c = [0] * nv
    for part in s.split('+'):
        if '*x' in part:
            a, v = part.split('*x'); c[int(v)] = int(a)
        else:
            k = int(part)
    return k, c

def nvars(forms):
    m = -1
    for s in forms:
        for part in s.split('+'):
            if '*x' in part: m = max(m, int(part.split('*x')[1]))
    return m + 1

def rref(rows):
    """rows: lists of Fractions [coefs..., rhs]; returns reduced rows or None if inconsistent."""
    rows = [r[:] for r in rows]; out = []; n = len(rows[0]) - 1 if rows else 0
    for col in range(n):
        piv = next((r for r in rows if r[col] != 0), None)
        if piv is None: continue
        rows.remove(piv); piv = [v / piv[col] for v in piv]
        rows = [[a - r[col] * b for a, b in zip(r, piv)] for r in rows]
        out = [[a - r[col] * b for a, b in zip(r, piv)] for r in out]
        out.append(piv)
    if any(r[-1] != 0 for r in rows): return None
    return sorted(out)

def sample(nv, cons, extra=None, B=40):
    """a nonnegative integer point with the equalities (and predicate extra), or None (searched up to B, lines up to 400)."""
    piv = {}
    for r in cons:
        col = next(i for i in range(nv) if r[i] != 0); piv[col] = r
    free = [i for i in range(nv) if i not in piv]
    rng = range(400) if len(free) <= 1 else range(B)
    for vals in itertools.product(rng, repeat=len(free)):
        x = [None] * nv
        for i, v in zip(free, vals): x[i] = Fr(v)
        ok = True
        for col, r in piv.items():
            v = r[-1] - sum(r[i] * x[i] for i in free)
            if v < 0 or v.denominator != 1: ok = False; break
            x[col] = v
        if ok:
            x = [int(v) for v in x]
            if extra is None or extra(x): return x
    return None

def main():
    path = sys.argv[1]
    c = json.load(gzip.open(path) if path.endswith('.gz') else open(path))
    cl = {(t, tuple(r)): v for t, r, v in c['classes']}
    mod = c['mod']
    pred = collections.defaultdict(list)
    for k, v in cl.items():
        for i, lf in enumerate(v):
            if lf['kind'] == 'node': pred[lf['to']].append((k, i))
    def info(k, i):
        lf = cl[k][i]; nv = nvars(lf['start'])
        return lf, nv, [parse_form(s, nv) for s in lf['start']], [parse_form(s, nv) for s in lf.get('counts', [])]
    def member(k, i, cons, n):
        """point n (counts) in region (k, i, cons)?"""
        lf, nv, S, _ = info(k, i)
        rows = [[Fr(a) for a in cf] + [Fr(v - k0)] for (k0, cf), v in zip(S, n)] + [r[:] for r in cons]
        if nv == 0:
            return all(k0 == v for (k0, cf), v in zip(S, n))
        rr = rref(rows)
        return rr is not None and sample(nv, rr, B=3) is not None and len(rr) == nv
    regions = {}; todo = []
    for k, v in cl.items():
        for i, lf in enumerate(v):
            if lf['kind'] == 'halt':
                regions[(k, i, ())] = None; todo.append((k, i, ()))
    maxr = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    while todo and len(regions) < maxr:
        k, i, cons = todo.pop(0)
        cons_l = [list(r) for r in cons]
        lf, nv, S, _ = info(k, i)
        for k2, j in pred[k[0]]:
            lf2, nv2, S2, C2 = info(k2, j)
            # x of (k,i) and z of (k2,j):  S(x) = C2(z), cons(x)
            rows = []
            for (s0, sc), (c0, cc) in zip(S, C2):
                rows.append([Fr(a) for a in sc] + [Fr(-a) for a in cc] + [Fr(c0 - s0)])
            for r in cons_l:
                rows.append(list(r[:nv]) + [Fr(0)] * nv2 + [r[-1]])
            if not rows:
                rr = []
            else:
                rr = rref(rows)
                if rr is None: continue
            # eliminate x: rows whose x-part is zero are constraints on z; rows with x pivots just define x (need x >= 0 integer)
            pt = sample(nv + nv2, rr) if nv + nv2 else []
            if pt is None: continue
            zc = [r[nv:] for r in rr if all(a == 0 for a in r[:nv])]
            zc = tuple(tuple(r) for r in (rref(zc) or [])) if zc else ()
            key = (k2, j, zc)
            if key not in regions:
                regions[key] = (k, i, cons); todo.append(key)
    print('%d regions lead to a halt%s' % (len(regions), '' if not todo else ' (stopped, %d not expanded)' % len(todo)))
    by = collections.Counter(len(z) for (_, _, z) in regions)
    print('by number of equalities:', dict(by))
    for (k, i, z) in regions:
        lf = cl[k][i]
        if z or nvars(lf['start']) >= 2 or lf['kind'] == 'halt':
            print(k[0], k[1], 'piece', lf['start'], 'with', [' '.join('%s*x%d' % (a, n) for n, a in enumerate(r[:-1]) if a) + ' = %s' % r[-1] for r in z])

main()
