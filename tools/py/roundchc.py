#!/usr/bin/env python3
"""roundchc: one machine as a counter program over tape shapes, with tail excursions taken from rlepds summaries.

A configuration is (state, head cell, left side, right side).  A side is a list of items, nearest first: single cells
and repeated words (w)^n whose count n is an integer variable, then a tail: BLANK, or ANY (right side only).  The
*shape* forgets the counts.  Every machine step is a guarded affine update of the counts between two shapes
(popping a cell of (w)^n splits on n = 1 / n >= 2).  When the head walks into the ANY tail, the step is replaced
by the summary `rlepds MACHINE ... enter=Qh`: every way the head can come back, for every tape there.

The result is a set of constrained Horn clauses, one predicate per shape; Z3's Spacer is asked for an inductive
invariant that excludes the halting shapes.  An answer `sat` is a candidate proof only: the summaries and the
invariant have to be checked independently before anything counts.

usage: roundchc.py MACHINE START_STEP [--rlepds PATH] [--kr N] [--timeout S] [--maxshapes N] [--lmax N]
                   [--keep-right] [--dump FILE] [--no-solve]
"""
import sys, subprocess, re, argparse, collections, time

ap = argparse.ArgumentParser()
ap.add_argument('machine'); ap.add_argument('start', type=int)
ap.add_argument('--rlepds', default='./rlepds'); ap.add_argument('--kr', type=int, default=10)
ap.add_argument('--sumk', type=int, default=2)
ap.add_argument('--timeout', type=int, default=600); ap.add_argument('--maxshapes', type=int, default=200000)
ap.add_argument('--lmax', type=int, default=4); ap.add_argument('--llit', type=int, default=10); ap.add_argument('--lpat', type=int, default=2); ap.add_argument('--keep-right', action='store_true')
ap.add_argument('--check', type=int, default=0); ap.add_argument('--guide', type=int, default=0); ap.add_argument('--guidek', default=''); ap.add_argument('--clip', type=int, default=60); ap.add_argument('--dump'); ap.add_argument('--no-solve', action='store_true'); ap.add_argument('--mirror', action='store_true')
A = ap.parse_args()
M = A.machine
T = {}
for i, row in enumerate(M.split('_')):
    for b in range(2):
        x = row[3*b:3*b+3]
        if x[0] != '-' and x[2] != '-':
            d = 1 if x[1] == 'R' else -1
            if A.mirror: d = -d
            T[(i, b)] = (int(x[0]), d, ord(x[2]) - 65)

# ---- items: int cell, or (word, expr).  expr: ('v', i, c) = x_i + c | ('c', c) | ('f', id, lo, mod, res) fresh
def REP(p): return 3 if p >= 2 else 4

def primitive(w):
    n = len(w)
    return not any(n % p == 0 and w == w[:p] * (n // p) for p in range(1, n))

def add(e, k):
    if e[0] == 'v': return ('v', e[1], e[2] + k)
    if e[0] == 'c': return ('c', e[1] + k)
    if e[0] == 'f': return ('f', e[1], e[2], e[3], e[4], e[5] + k)
    raise ValueError

def esum(a, b):
    if a[0] == 'c': return add(b, a[1])
    if b[0] == 'c': return add(a, b[1])
    return None

def normalize(items):
    items = list(items)
    while True:
        ch = False
        m = 0
        while m < len(items) and isinstance(items[m], int): m += 1
        # literal copy next to a pattern (near side)
        for j in range(len(items)):
            it = items[j]
            if isinstance(it, int): continue
            w = it[0]; p = len(w)
            if j >= p and all(isinstance(items[j-p+t], int) and items[j-p+t] == w[t] for t in range(p)):
                items[j-p:j+1] = [(w, add(it[1], 1))]; ch = True; break
            if j + p < len(items) + 0 and j + p <= len(items) - 0 and all(j+1+t < len(items) and isinstance(items[j+1+t], int) and items[j+1+t] == w[t] for t in range(p)):
                items[j:j+p+1] = [(w, add(it[1], 1))]; ch = True; break
            if j + 1 < len(items) and not isinstance(items[j+1], int) and items[j+1][0] == w:
                s = esum(it[1], items[j+1][1])
                if s is not None:
                    items[j:j+2] = [(w, s)]; ch = True; break
        if ch: continue
        # new pattern in the literal prefix
        for p in range(1, A.lmax + 1):
            R = REP(p)
            if m >= R * p:
                w = tuple(items[:p])
                if primitive(w) and all(items[t] == w[t % p] for t in range(R * p)):
                    items[:R*p] = [(w, ('c', R))]; ch = True; break
        if not ch: return items

def push(side, c, right):
    items, tail = side
    if not items and tail == 'B' and c == 0: return side
    items = normalize([c] + list(items))
    if right:
        lead = 0
        while lead < len(items) and lead < 3 * A.lmax and isinstance(items[lead], int): lead += 1
        while len(items) > A.kr + lead: items.pop(); tail = 'A'
    return (items, tail)

def pop(side):
    """-> list of (cell or 'ANY', guards, side); guards: list of (expr, '==1' | '>=2')"""
    items, tail = side
    if not items:
        return [(0, [], side)] if tail == 'B' else [('ANY', [], side)]
    it = items[0]
    if isinstance(it, int): return [(it, [], (items[1:], tail))]
    w, e = it; out = []
    rest = list(w[1:])
    if e[0] == 'c':
        if e[1] == 1: return [(w[0], [], (rest + items[1:], tail))]
        return [(w[0], [], (rest + [(w, add(e, -1))] + items[1:], tail))]
    out.append((w[0], [(e, '==1')], (rest + items[1:], tail)))
    out.append((w[0], [(e, '>=2')], (rest + [(w, add(e, -1))] + items[1:], tail)))
    return out

# ---- summaries from rlepds
sumcache = {}
def summary(q, h):
    k = (q, h)
    if k in sumcache: return sumcache[k]
    cmd = [A.rlepds, M, str(A.sumk), '1', '9', '9', '3', '3', '3', '1', 'enter=%s%d' % ('ABCDEF'[q], h), 'limit=20000000']
    if A.mirror: cmd.append('mirror')
    out = subprocess.run(cmd, capture_output=True, text=True).stdout
    res = re.search(r'(NONHALT|HALTREACH|LIMIT)', out).group(1)
    exits = []
    if res == 'NONHALT':
        for l in out.splitlines():
            mm = re.match(r'\s+exit ([A-F]) \| (.*) (ANY|BLANK)$', l)
            if mm is None:
                mm2 = re.match(r'\s+exit ([A-F]) \| (ANY|BLANK)$', l)
                if mm2: exits.append((ord(mm2.group(1)) - 65, [], 'A' if mm2.group(2) == 'ANY' else 'B'))
                continue
            its = []
            for tok in mm.group(2).split():
                s, c = tok.split('^')
                if c.startswith('>='):
                    lo, rest = c[2:].split('%'); mod, r = rest.split('=')
                    its.append(('cls', int(s), int(lo), int(mod), int(r)))
                else: its += [int(s)] * int(c)
            exits.append((ord(mm.group(1)) - 65, its, 'A' if mm.group(3) == 'ANY' else 'B'))
    sumcache[k] = (res, exits); return sumcache[k]

# ---- shapes
def shape_of(q, h, L, R):
    def sh(side): return (tuple(it if isinstance(it, int) else it[0] for it in side[0]), side[1])
    return (q, h, sh(L), sh(R))
def exprs_of(L, R): return [it[1] for it in L[0] if not isinstance(it, int)] + [it[1] for it in R[0] if not isinstance(it, int)]
def identity(shape):
    q, h, (li, lt), (ri, rt) = shape; n = 0; L = []; Rr = []
    for it in li:
        if isinstance(it, int): L.append(it)
        else: L.append((it, ('v', n, 0))); n += 1
    for it in ri:
        if isinstance(it, int): Rr.append(it)
        else: Rr.append((it, ('v', n, 0))); n += 1
    return (L, lt), (Rr, rt), n

fresh_id = [0]
def successors(shape):
    """-> list of (guards, target shape or 'BAD', target exprs)"""
    q, h = shape[0], shape[1]
    L, R, n = identity(shape)
    if (q, h) not in T: return [([], 'BAD', [])]
    w, d, q2 = T[(q, h)]
    out = []
    if d > 0:
        L2 = push(L, w, False)
        for cell, g, R2 in pop(R):
            if cell != 'ANY':
                out.append((g, shape_of(q2, cell, L2, R2), exprs_of(L2, R2))); continue
            for hh in (0, 1):
                res, exits = summary(q2, hh)
                if res == 'HALTREACH': out.append((g, 'BAD', [])); continue
                if res == 'LIMIT': raise SystemExit('summary %s%d hit the limit' % ('ABCDEF'[q2], hh))
                for (q3, its, tl) in exits:
                    items = []
                    for it in its:
                        if isinstance(it, int): items.append(it)
                        else:
                            fresh_id[0] += 1
                            items.append(((it[1],), ('f', fresh_id[0], it[2], it[3], it[4], 0)))
                    items = normalize(items)
                    R3 = (items, tl)
                    for cell2, g2, L3 in pop(L2):
                        out.append((g + g2, shape_of(q3, cell2, L3, R3), exprs_of(L3, R3)))
    else:
        R2 = push(R, w, True)
        for cell, g, L2 in pop(L):
            assert cell != 'ANY'
            out.append((g, shape_of(q2, cell, L2, R2), exprs_of(L2, R2)))
    return out

# ---- initial configuration
def initial():
    tape = {}; pos = 0; q = 0
    for t in range(A.start):
        k = (q, tape.get(pos, 0))
        if k not in T: raise SystemExit('halts before the start step')
        w, d, q2 = T[k]; tape[pos] = w; pos += d; q = q2
    lo = min(tape) if tape else 0; hi = max(tape) if tape else 0
    L = ([], 'B')
    for i in range(lo, pos): L = push(L, tape.get(i, 0), False)
    R = ([], 'B')
    if A.keep_right:
        for i in range(hi, pos, -1): R = push(R, tape.get(i, 0), True)
    else: R = ([], 'A')
    return q, tape.get(pos, 0), L, R

q0, h0, L0, R0 = initial()
s0 = shape_of(q0, h0, L0, R0); v0 = [e[1] for e in exprs_of(L0, R0)]
def show(shape):
    q, h, (li, lt), (ri, rt) = shape
    f = lambda its: ' '.join(str(i) if isinstance(i, int) else '(' + ''.join(map(str, i)) + ')^n' for i in its)
    return '%s[%d]  L: %s %s   R: %s %s' % ('ABCDEF'[q], h, f(li), lt, f(ri), rt)
print('start:', show(s0), 'counts', v0)

def expand(side, vals, k):
    out = []
    for it in side[0]:
        if isinstance(it, int): out.append(it)
        else: out += list(it) * vals[k]; k += 1
    return out, k
if A.check:
    # follow the real run and the counter program side by side (use --keep-right and a large --kr)
    tape = {}; pos = 0; q = 0
    for t in range(A.start):
        w, d, q2 = T[(q, tape.get(pos, 0))]; tape[pos] = w; pos += d; q = q2
    s = s0; vals = list(v0)
    def ev(e, vals): return vals[e[1]] + e[2] if e[0] == 'v' else e[1]
    for t in range(A.check):
        lo = min(tape); hi = max(tape)
        Lc, k = expand(s[2], vals, 0); Rc, k = expand(s[3], vals, k)
        realL = [tape.get(i, 0) for i in range(pos - 1, lo - 1, -1)]; realR = [tape.get(i, 0) for i in range(pos + 1, hi + 1)]
        strip = lambda x: x[:len(x) - next((j for j, c in enumerate(reversed(x)) if c), len(x))]
        if (s[0], s[1]) != (q, tape.get(pos, 0)) or strip(Lc) != strip(realL) or strip(Rc) != strip(realR):
            print('CHECK FAIL at step', t, show(s), vals); raise SystemExit(1)
        nxt = [x for x in successors(s) if all((ev(e, vals) == 1) if op == '==1' else (ev(e, vals) >= 2) for e, op in x[0])]
        assert len(nxt) == 1, (len(nxt), show(s))
        g, tgt, ex = nxt[0]; vals = [ev(e, vals) for e in ex]; s = tgt
        w, d, q2 = T[(q, tape.get(pos, 0))]; tape[pos] = w; pos += d; q = q2
    print('CHECK OK: %d steps of the real run agree with the counter program' % A.check); raise SystemExit(0)
def within(tgt):
    return not (sum(1 for it in tgt[2][0] if isinstance(it, int)) > A.llit or sum(1 for it in tgt[2][0] if not isinstance(it, int)) > A.lpat)
succ_cache = {}
def succ(s):
    if s not in succ_cache: succ_cache[s] = successors(s)
    return succ_cache[s]
def ev(e, vals, fr):
    if e[0] == 'v': return vals[e[1]] + e[2]
    if e[0] == 'c': return e[1]
    return fr[e[1]] + e[5]
ids = {s0: 0}; order = [s0]; trans = []; bad = 0; wide = 0
t0 = time.time()
if A.guide:
    # concrete-guided: walk the counter program on numbers (every summary exit, three sizes for each fresh count) and keep
    # only the shapes met; a transition to any other shape is treated as bad and left to the solver to refute
    starts = [list(v0)]
    for kk in A.guidek.split(','):
        if kk: starts.append([int(kk)] + list(v0[1:]))
    seen = set(); work = []
    for v in starts:
        work.append((s0, tuple(v)))
    G = {s0}
    while work and len(seen) < A.guide:
        s, vals = work.pop()
        key = (s, tuple(min(v, A.clip) for v in vals))
        if key in seen: continue
        seen.add(key)
        for g, tgt, ex in succ(s):
            if tgt == 'BAD' or not within(tgt): continue
            fids = sorted(set(e[1] for e in ex if e[0] == 'f') | set(e[1] for e, op in g if e[0] == 'f'))
            fdef = {}
            for e in list(ex) + [e for e, op in g]:
                if e[0] == 'f': fdef[e[1]] = e
            combos = [{}]
            for fid in fids:
                e = fdef[fid]; base = e[2] + ((e[4] - e[2]) % e[3])
                combos = [{**c, fid: base + j * e[3]} for c in combos for j in (0, 1, 4)]
            for fr in combos:
                if all((ev(e, vals, fr) == 1) if op == '==1' else (ev(e, vals, fr) >= 2) for e, op in g):
                    G.add(tgt); work.append((tgt, tuple(ev(e, vals, fr) for e in ex)))
    print('guided walk: %d numeric states, %d shapes, %s' % (len(seen), len(G), 'stopped at the limit' if work else 'closed under the clip'))
    for s in G:
        if s not in ids: ids[s] = len(order); order.append(s)
    for s in order:
        for g, tgt, ex in succ(s):
            if tgt != 'BAD' and (tgt not in G): tgt = 'BAD'; ex = []; wide += 1
            if tgt == 'BAD': bad += 1
            trans.append((s, g, tgt, ex))
else:
    i = 0
    while i < len(order):
        s = order[i]; i += 1
        for g, tgt, ex in succ(s):
            if tgt != 'BAD' and not within(tgt): tgt = 'BAD'; ex = []; wide += 1
            if tgt == 'BAD': trans.append((s, g, 'BAD', ex)); bad += 1; continue
            if tgt not in ids:
                ids[tgt] = len(order); order.append(tgt)
                if len(order) > A.maxshapes:
                    print('too many shapes; last:', show(tgt)); raise SystemExit(3)
            trans.append((s, g, tgt, ex))
print('shapes %d, transitions %d, bad transitions %d (of which %d leave the shape set or budget), %.1fs' % (len(order), len(trans), bad, wide, time.time() - t0))
print('summaries:', {('ABCDEF'[k[0]] + str(k[1])): (v[0], len(v[1])) for k, v in sorted(sumcache.items())})
if A.dump:
    with open(A.dump, 'w') as f:
        for s in order: f.write('%d %s\n' % (ids[s], show(s)))
        for s, g, tgt, ex in trans: f.write('%d -> %s | %s | %s\n' % (ids[s], tgt if tgt == 'BAD' else ids[tgt], g, ex))
if bad == 0:
    print('RESULT NONHALT-CANDIDATE: no halting transition among the reachable shapes (no solver needed)'); raise SystemExit(0)

# ---- chain compression: only shapes with several incoming transitions (and the start) keep a predicate
def subst(e, ex):
    if e[0] == 'v': return add(ex[e[1]], e[2])
    return e
def geval(e, op):
    if e[0] == 'c': return (e[1] == 1) if op == '==1' else (e[1] >= 2)
    return None
indeg = collections.Counter(tgt for s, g, tgt, ex in trans if tgt != 'BAD')
outs = collections.defaultdict(list)
for s, g, tgt, ex in trans: outs[s].append((g, tgt, ex))
cut = set(s for s in order if indeg[s] != 1 or s == s0)
ctrans = []
for c in cut:
    stack = [(list(g), tgt, list(ex)) for g, tgt, ex in outs[c]]
    while stack:
        g, tgt, ex = stack.pop()
        if tgt == 'BAD' or tgt in cut: ctrans.append((c, g, tgt, ex)); continue
        for g2, t2, ex2 in outs[tgt]:
            gg = list(g); ok = True
            for e, op in g2:
                e2 = subst(e, ex); v = geval(e2, op)
                if v is False: ok = False; break
                if v is None: gg.append((e2, op))
            if ok: stack.append((gg, t2, [subst(e, ex) for e in ex2]))
print('after chain compression: %d predicates, %d clauses, %d bad' % (len(cut), len(ctrans), sum(1 for t in ctrans if t[2] == 'BAD')))
trans = ctrans; order = [s for s in order if s in cut]
# ---- chain compression is left to the solver; build the clauses
if A.no_solve: raise SystemExit(0)
import z3
fp = z3.Fixedpoint(); fp.set(engine='spacer'); fp.set('timeout', A.timeout * 1000)
arity = {s: sum(1 for it in s[2][0] if not isinstance(it, int)) + sum(1 for it in s[3][0] if not isinstance(it, int)) for s in order}
P = {}
for s in order:
    P[s] = z3.Function('P%d' % ids[s], *([z3.IntSort()] * arity[s] + [z3.BoolSort()])); fp.register_relation(P[s])
maxar = max(arity.values()) if arity else 0
X = [z3.Int('x%d' % j) for j in range(maxar)]
allvars = list(X)
def tr(e, fr):
    if e[0] == 'v': return X[e[1]] + e[2]
    if e[0] == 'c': return z3.IntVal(e[1])
    y = z3.Int('f%d' % e[1])
    if e[1] not in fr: fr[e[1]] = (y, z3.And(y >= e[2], y % e[3] == e[4]))
    return y + e[5]
fp.fact(P[s0](*[z3.IntVal(c) for c in v0]) if v0 else P[s0]())
nq = 0
for s, g, tgt, ex in trans:
    fr = {}
    body = [P[s](*X[:arity[s]]) if arity[s] else P[s]()]
    for e, op in g: body.append(tr(e, fr) == 1 if op == '==1' else tr(e, fr) >= 2)
    if tgt == 'BAD': head = None
    else:
        args = [tr(e, fr) for e in ex]; head = P[tgt](*args) if args else P[tgt]()
    for y, c in fr.values(): body.append(c)
    vs = X[:arity[s]] + [y for y, c in fr.values()]
    if head is None:
        Bd = z3.Function('Bad', z3.BoolSort())
        if nq == 0: fp.register_relation(Bd)
        nq += 1; fp.declare_var(*vs) if vs else None; fp.rule(Bd(), body)
    else:
        if vs: fp.declare_var(*vs)
        fp.rule(head, body)
t0 = time.time()
r = fp.query(z3.Function('Bad', z3.BoolSort())())
print('spacer: %s in %.1fs   (unsat = no halting shape is reachable in the counter program)' % (r, time.time() - t0))
if r == z3.unsat:
    print('RESULT NONHALT-CANDIDATE')
    ans = fp.get_answer()
    if A.dump: open(A.dump + '.inv', 'w').write(str(ans))
elif r == z3.sat: print('RESULT HALTREACH in the counter program (says nothing about the machine)')
else: print('RESULT UNKNOWN', fp.get_reason_unknown())
