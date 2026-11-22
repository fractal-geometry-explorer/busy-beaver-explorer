"""The closed map on block counts of a class certificate (pclosure.py format), and congruence tests against it.

A certificate lists classes (a node shape and the parity of each free count) and, per class, pieces whose start counts
are affine in free variables x_i >= 0, each going to a node of another class (or halting).  Classes with one count
have, for large counts, exactly one piece, P = a + 2y -> b + 6y (or into a class with more counts), so the run through
them is determined.  `reduced` composes those chains: what is left is a map on the classes with two or more counts
(for 1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD: 16 classes on (P, Q), 2,313 pieces; for the mirror machine
1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA: 1,319 classes, 1,885 pieces).  Every piece is affine on a lattice cone.

usage (C = a classes_mod2.json.gz certificate; the start is the class and count of the first node, 0 35 for the
machine of this folder, 0 21 for the mirror machine):
  pqmap.py table C                      the reduced map, generic pieces written in the counts (P, Q)
  pqmap.py validate C N START COUNT     the reduced map against the node map along the run (N nodes)
  pqmap.py cong C START COUNT M...      smallest set of (class, counts mod M) closed under the map: is a halting
                                        piece in it?  (if not, the machine would never halt: a congruence invariant)
  pqmap.py orbit C START COUNT SECONDS [CLASS...]
                                        exact node map with cycle jumps; writes the visits of the given classes
                                        (default: all with several counts) to orbit.json.gz in the current directory
  pqmap.py lines C ORBIT LINES...       for each modulus m <= 5000, does the orbit visit a class with the line's
                                        linear form = 0 mod m?  LINES are CLASS:a,b,c,... meaning a*n1 + b*n2 + ... + c
"""
import collections
import gzip
import itertools
import math
import json
import re
import sys
import time
from fractions import Fraction as Fr

# ---- reading a certificate -----------------------------------------------------------------------------------


def parse(s):
    c0 = 0; co = {}
    for t in s.split('+'):
        m = re.fullmatch(r'(\d+)\*x(\d+)', t)
        if m: co[int(m.group(2))] = int(m.group(1))
        else: c0 += int(t)
    return c0, co


def load(path):
    c = json.load(gzip.open(path)); MOD = c['mod']; L = c['classes']
    names = {(t, tuple(r)): i for i, (t, r, p) in enumerate(L)}
    PC = []
    for i, (t, r, ps) in enumerate(L):
        out = []
        for p in ps:
            st = [parse(x) for x in p['start']]
            if p['kind'] == 'node':
                tc = [parse(x) for x in p['counts']]
                j = names[(p['to'], tuple(a % MOD for a, _ in tc))]
            else:
                tc = None; j = -1
            vs = sorted(set(v for _, co in st for v in co) | set(v for _, co in (tc or []) for v in co))
            out.append((st, tc, j, vs))
        PC.append(out)
    return L, PC


def solve(st, cs):
    """integers x >= 0 with st(x) = cs (pieces are triangular: some row always has one unknown), or None"""
    x = {}; rows = [(cs[k] - st[k][0], st[k][1]) for k in range(len(st))]
    changed = True
    while changed:
        changed = False
        for rhs, co in rows:
            co2 = {v: a for v, a in co.items() if v not in x}
            r2 = rhs - sum(a * x[v] for v, a in co.items() if v in x)
            if not co2:
                if r2 != 0: return None
                continue
            if len(co2) == 1:
                (v, a), = co2.items()
                if r2 % a or r2 < 0: return None
                x[v] = r2 // a; changed = True
    if any(v not in x for _, co in st for v in co): return None
    return x


def apply(forms, x):
    return [a + sum(b * x[v] for v, b in co.items()) for a, co in forms]


# ---- the reduced map -----------------------------------------------------------------------------------------


def sub(f, v, k, nv=None):
    """substitute v = k (+ nv)"""
    c0, co = f; co = dict(co); a = co.pop(v, 0); c0 += a * k
    if nv is not None and a: co[nv] = co.get(nv, 0) + a
    return (c0, co)


def ev_sub(f, subst):
    c0, co = f; r0 = c0; rco = {}
    for v, b in co.items():
        g0, gco = subst[v]; r0 += b * g0
        for w, c in gco.items(): rco[w] = rco.get(w, 0) + b * c
    return (r0, {w: c for w, c in rco.items() if c})


class Reducer:
    def __init__(self, L, PC):
        self.L, self.PC = L, PC
        self.NC = [len(r) for t, r, p in L]
        self.fresh = 1000

    def big1(self, i):
        out = [(st, tc, j, vs) for st, tc, j, vs in self.PC[i] if vs]
        assert len(out) == 1, i
        st, tc, j, vs = out[0]
        (a, co), = st; (y, m), = co.items()
        return a, m, y, tc, j

    def chain(self, i, forms, subst, depth=0):
        """from class i (fewer than two counts), counts `forms` affine in the variables: yield (subst, class, forms)
        at the first class with two or more counts, or (subst, 'HALT', forms)"""
        if i == -1: yield (subst, 'HALT', forms); return
        if self.NC[i] >= 2: yield (subst, i, forms); return
        assert depth < 200, 'chain too long'
        if self.NC[i] == 0:
            (st, tc, j, vs), = self.PC[i]
            if tc is None: yield (subst, 'HALT', forms); return
            yield from self.chain(j, tc, subst, depth + 1); return
        (c0, co), = forms
        a, m, y, tc, j = self.big1(i)
        if c0 >= a:
            assert (c0 - a) % m == 0 and all(b % m == 0 for b in co.values())
            if tc is None: yield (subst, 'HALT', forms); return
            yf = {y: ((c0 - a) // m, {v: b // m for v, b in co.items()})}
            yield from self.chain(j, [ev_sub(g, yf) for g in tc], subst, depth + 1)
            return
        v = next(v for v, b in co.items() if b); b = co[v]; k = -(-(a - c0) // b)
        for val in range(k): yield from self.split(i, forms, subst, v, val, None, depth)
        self.fresh += 1
        yield from self.split(i, forms, subst, v, k, self.fresh, depth)

    def split(self, i, forms, subst, v, val, nv, depth):
        s2 = {w: sub(g, v, val, nv) for w, g in subst.items()}
        f2 = [sub(g, v, val, nv) for g in forms]
        if not any(f2[0][1].values()):
            c = f2[0][0]
            for st, tc, j, vs in self.PC[i]:
                if not vs and st[0][0] == c:
                    if tc is None: yield (s2, 'HALT', f2)
                    else: yield from self.chain(j, tc, s2, depth + 1)
                    return
        yield from self.chain(i, f2, s2, depth)

    def reduced(self):
        """{class with >= 2 counts: [(start forms, target class or 'HALT', target forms)]}"""
        R = {}
        for i in range(len(self.L)):
            if self.NC[i] < 2: continue
            R[i] = []
            for st, tc, j, vs in self.PC[i]:
                subst = {v: (0, {v: 1}) for v in vs}
                if tc is None:
                    R[i].append((st, 'HALT', None)); continue
                for s2, k, forms in self.chain(j, tc, subst):
                    R[i].append(([ev_sub(f, s2) for f in st], k, forms))
        return R


def fmt(f):
    c0, co = f
    s = [str(c0)] if c0 or not co else []
    s += ['%d*x%d' % (b, v) for v, b in sorted(co.items()) if b]
    return '+'.join(s)


def in_counts(src, g, names):
    """the target form g written in the start counts (solving src = counts over the rationals)"""
    vs = sorted(set(v for _, co in src for v in co))
    rows = [[[Fr(f[1].get(v, 0)) for v in vs], {k: Fr(1)}, Fr(-f[0])] for k, f in enumerate(src)]
    xv = {}
    for ci, v in enumerate(vs):
        r = next((r for r in rows if r[0][ci] != 0 and not any(r is p for p in xv.values())), None)
        if r is None: return None
        a = r[0][ci]; r[0] = [x / a for x in r[0]]; r[1] = {k: x / a for k, x in r[1].items()}; r[2] /= a
        for o in rows:
            if o is not r and o[0][ci] != 0:
                b = o[0][ci]; o[0] = [x - b * y for x, y in zip(o[0], r[0])]
                for k, x in r[1].items(): o[1][k] = o[1].get(k, 0) - b * x
                o[2] -= b * r[2]
        xv[v] = r
    c = Fr(g[0]); co = collections.defaultdict(Fr)
    for v, b in g[1].items():
        r = xv[v]; c += b * r[2]
        for k, x in r[1].items(): co[k] += b * x
    out = []
    for k in range(len(src)):
        if co[k]: out.append(names[k] if co[k] == 1 else '-' + names[k] if co[k] == -1 else '%s*%s' % (co[k], names[k]))
    s = ' + '.join(out)
    if c: s = (s + (' + ' if c > 0 else ' - ') + str(abs(c))) if s else str(c)
    return s.replace('+ -', '- ')


def table(path):
    L, PC = load(path); red = Reducer(L, PC); R = red.reduced(); NC = red.NC
    multi = sorted(R); lab = {i: 'S%d' % n for n, i in enumerate(multi)}
    names = ['P', 'Q', 'R', 'S']
    print('%d classes with two or more counts, %d pieces' % (len(multi), sum(len(v) for v in R.values())))
    print('generic piece: start counts as affine forms in x0, x1, ... >= 0 -> target class (target counts in the start counts)')
    for i in multi:
        gen = []; low = collections.Counter()
        for src, k, forms in R[i]:
            tgt = 'HALT' if k == 'HALT' else lab[k]
            if len(set(v for _, co in src for v in co)) == NC[i]:
                img = [] if forms is None else [in_counts(src, g, names) for g in forms]
                gen.append('(%s) -> %s (%s)' % (', '.join(fmt(f) for f in src), tgt, ', '.join(img)))
            else:
                low[tgt + (':' + ','.join(fmt(f) for f in src) if tgt == 'HALT' else '')] += 1
        print('\n%s = class %d  %s  parities %s: %d pieces, %d generic' % (lab[i], i, L[i][0], L[i][1], len(R[i]), len(gen)))
        for g in gen: print('    ' + g)
        print('    lower-dimensional pieces (a count fixed or a linear relation between counts), by target:',
              ', '.join('%s %d' % kv for kv in sorted(low.items())))


# ---- node map, validation --------------------------------------------------------------------------------------


def stepk(PC, i, cs):
    hits = [(k, tc, j, x) for k, (st, tc, j, vs) in enumerate(PC[i]) for x in [solve(st, cs)] if x is not None]
    assert len(hits) == 1, (i, len(hits))
    k, tc, j, x = hits[0]
    if tc is None: return k, None, None
    return k, j, apply(tc, x)


def validate(path, N, i, c0):
    L, PC = load(path); red = Reducer(L, PC); R = red.reduced(); NC = red.NC
    cs = [c0]; multi = []
    for n in range(N):
        if NC[i] >= 2: multi.append((i, tuple(cs)))
        k, j, cs = stepk(PC, i, cs)
        if j is None: break
        i = j
    bad = 0
    for (a, ca), (b, cb) in zip(multi, multi[1:]):
        hits = [(k, forms, x) for src, k, forms in R[a] for x in [solve(src, list(ca))] if x is not None]
        if len(hits) != 1 or hits[0][0] != b or tuple(apply(hits[0][1], hits[0][2])) != cb: bad += 1
    print('%d nodes, %d visits of classes with two or more counts, %d reduced steps checked, %d mismatches'
          % (N, len(multi), len(multi) - 1, bad))


# ---- congruences -------------------------------------------------------------------------------------------------


def cong(path, i0, c0, Ms):
    L, PC = load(path)
    for M in Ms:
        E = collections.defaultdict(set)
        for i, ps in enumerate(PC):
            for st, tc, j, vs in ps:
                for xs in itertools.product(range(M), repeat=len(vs)):
                    x = dict(zip(vs, xs))
                    s = tuple(v % M for v in apply(st, x))
                    E[(i, s)].add((j, tuple(v % M for v in apply(tc, x))) if tc is not None else ('HALT', ()))
        s0 = (i0, (c0 % M,)); seen = {s0}; stack = [s0]
        while stack:
            u = stack.pop()
            for v in E.get(u, ()):
                if v not in seen: seen.add(v); stack.append(v)
        print('mod %d: %d residue states reachable, halting piece %s' % (M, len(seen), 'REACHABLE' if ('HALT', ()) in seen else 'NOT REACHABLE'))
        sys.stdout.flush()


# ---- the orbit, with cycle jumps -------------------------------------------------------------------------------


def orbit(path, i, c0, sec, watch=None):
    """Exact node map from (class i, count c0).  When the last Lc (class, piece) pairs repeat the Lc before them and
    the counts moved by the same vector d, the cycle is jumped k times, k the largest value for which one more cycle
    from counts + k*d still uses the same pieces and moves by d (then so do all smaller ones: piece domains are
    convex and the variables are affine in k, integral at k = 0 and 1).  Visits of classes with >= 2 counts inside
    a jump are written as one record per position of the cycle (class, first counts, change per cycle, k)."""
    L, PC = load(path); NC = [len(r) for t, r, p in L]
    cs = [c0]; hist = []; out = []; t0 = time.time(); nodes = 0; jumps = 0
    while time.time() - t0 < sec:
        if NC[i] >= 2 and (watch is None or i in watch): out.append([nodes, i, cs])
        k, j, cs2 = stepk(PC, i, cs)
        if j is None: print('HALT at node', nodes, i, cs); break
        hist.append((i, k, tuple(cs))); hist = hist[-200:]
        i, cs = j, cs2; nodes += 1
        for Lc in range(1, 60):
            if len(hist) < 2 * Lc: break
            a = hist[-Lc:]; b = hist[-2 * Lc:-Lc]
            pat = [(x[0], x[1]) for x in a]
            if pat != [(x[0], x[1]) for x in b] or a[0][0] != i or len(cs) != len(a[0][2]): continue
            d1 = [p - q for p, q in zip(cs, a[0][2])]
            if d1 != [p - q for p, q in zip(a[0][2], b[0][2])] or not any(d1): continue

            def ok(kk):
                s = [c + kk * d for c, d in zip(cs, d1)]
                if min(s) < 0: return False
                ii, ss, seq = i, s, []
                for _ in range(Lc):
                    try: kq, jj, ss = stepk(PC, ii, ss)
                    except AssertionError: return False
                    seq.append((ii, kq))
                    if jj is None: return False
                    ii = jj
                return seq == pat and ii == i and ss == [c + d for c, d in zip(s, d1)]
            lo, hi = 0, 1
            while ok(hi): lo, hi = hi, hi * 2
            while hi - lo > 1:
                m = (lo + hi) // 2
                if ok(m): lo = m
                else: hi = m
            if lo > 0:
                for x, y in zip(a, b):   # position p of the cycle is visited with counts x + t*(x - y), t = 1..lo
                    if NC[x[0]] >= 2 and (watch is None or x[0] in watch) and len(x[2]) == len(y[2]):
                        dp = [u - w for u, w in zip(x[2], y[2])]
                        out.append([nodes, 'jump', x[0], [u + w for u, w in zip(x[2], dp)], dp, lo])
                cs = [c + lo * d for c, d in zip(cs, d1)]; nodes += lo * Lc; jumps += 1; hist = []
            break
    json.dump({'cert': path, 'nodes': nodes, 'visits': out}, gzip.open('orbit.json.gz', 'wt'))
    print('nodes %d (%d digits), %d jumps, %d records, last counts of %s digits, %.0f s'
          % (nodes, len(str(nodes)), jumps, len(out), [len(str(v)) for v in cs], time.time() - t0))


def lines(path, orb, specs):
    o = json.load(gzip.open(orb))
    for spec in specs:
        cl, co = spec.split(':'); cls = set(map(int, cl.split(','))) if ',' in cl else {int(cl)}
        co = list(map(int, co.split(',')))
        vals = set()
        for r in o['visits']:
            if r[1] == 'jump':
                # inside a jump the cycle's first class is visited with counts cs + t*d, t < k
                _, _, i, cs, d, k = r
                if i in cls:
                    f0 = sum(a * c for a, c in zip(co, cs)) + co[-1]; fd = sum(a * c for a, c in zip(co, d))
                    vals.add(('ap', f0, fd, k))
            elif r[1] in cls:
                vals.add(sum(a * c for a, c in zip(co, r[2])) + co[-1])
        pts = [v for v in vals if not isinstance(v, tuple)]; aps = [v for v in vals if isinstance(v, tuple)]
        def apmin(f0, fd, k):   # min |f0 + t*fd| over 0 <= t < k
            if fd == 0: return abs(f0)
            t = max(0, min(k - 1, -f0 // fd)); return min(abs(f0 + u * fd) for u in (t, min(k - 1, t + 1)))
        allmin = min([abs(v) for v in pts] + [apmin(*v[1:]) for v in aps])
        def zero_mod(m):
            if any(v % m == 0 for v in pts): return True
            for _, f0, fd, k in aps:   # f0 + t*fd = 0 mod m for some 0 <= t < k
                g = math.gcd(fd, m)
                if f0 % g: continue
                mg = m // g
                t0 = (-(f0 // g) * pow(fd // g, -1, mg)) % mg if mg > 1 else 0
                if t0 < k: return True
            return False
        miss = [m for m in range(2, 5001) if not zero_mod(m)]
        print('%s: %d distinct values at single visits, %d runs of a cycle; min |value| %d' % (spec, len(pts), len(aps), allmin))
        print('    every modulus m < %s has a visit with value = 0 mod m; %d of 2..5000 have none (first: %s)'
              % (miss[0] if miss else '>5000', len(miss), miss[:12]))


if __name__ == '__main__':
    cmd, path = sys.argv[1], sys.argv[2]
    if cmd == 'table': table(path)
    elif cmd == 'validate': validate(path, int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))
    elif cmd == 'cong': cong(path, int(sys.argv[3]), int(sys.argv[4]), [int(m) for m in sys.argv[5:]])
    elif cmd == 'orbit': orbit(path, int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5]),
                               set(map(int, sys.argv[6:])) or None)
    elif cmd == 'lines': lines(path, sys.argv[3], sys.argv[4:])
