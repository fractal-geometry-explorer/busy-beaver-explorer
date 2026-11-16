"""Iterate the node map of a class certificate (pclosure.py format) with exact big integers.

At each node, the one piece of its class that contains its counts is found (the piece's start counts are affine in
free variables x_i >= 0; they are solved for exactly) and applied.  From the first big node of the run from blank tape
(class 0, count 35 at step 20,791) this is the run itself, node by node, much faster than the accelerated simulator
(1,000,000 nodes in about 8 minutes).  It reports the visits of B with Q odd, the closest approach to the two halting
lines Q = 3P - 16 (shape A) and Q = 3P - 24 (shape B), and stops on a halting piece.

usage (D = holdouts/1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/py/closure):
  python3 D/nodemap.py D/classes_mod2.json.gz NODES [CLASS COUNTS...]
"""
import json, gzip, re, sys, collections, time
from fractions import Fraction as F

c = json.load(gzip.open(sys.argv[1])); MOD = c['mod']; L = c['classes']
names = {(t, tuple(r)): i for i, (t, r, p) in enumerate(L)}


def parse(s):
    c0 = 0; co = {}
    for t in s.split('+'):
        m = re.fullmatch(r'(\d+)\*x(\d+)', t)
        if m: co[int(m.group(2))] = int(m.group(1))
        else: c0 += int(t)
    return c0, co


PC = collections.defaultdict(list)
for i, (t, r, ps) in enumerate(L):
    for p in ps:
        st = [parse(x) for x in p['start']]
        if p['kind'] == 'node':
            tc = [parse(x) for x in p['counts']]
            j = names[(p['to'], tuple(a % MOD for a, _ in tc))]
        else:
            tc = None; j = None
        PC[i].append((st, tc, j, p.get('moves')))


def solve(st, cs):
    """x >= 0 integers with st(x) = cs, or None."""
    vs = sorted(set(v for _, co in st for v in co))
    x = {}
    rows = [(cs[k] - st[k][0], dict(st[k][1])) for k in range(len(st))]
    # rows with a single unknown first, iterate
    changed = True
    while changed:
        changed = False
        for k, (rhs, co) in enumerate(rows):
            co2 = {v: a for v, a in co.items() if v not in x}
            r2 = rhs - sum(a * x[v] for v, a in co.items() if v in x)
            if not co2:
                if r2 != 0: return None
                continue
            if len(co2) == 1:
                (v, a), = co2.items()
                if r2 % a or r2 < 0: return None
                x[v] = r2 // a; changed = True
    for v in vs:
        if v not in x: return None
    return x


def step(i, cs):
    hits = []
    for st, tc, j, mv in PC[i]:
        x = solve(st, cs)
        if x is not None:
            hits.append((st, tc, j, x))
    if len(hits) != 1:
        raise Exception('class %d counts %s: %d pieces' % (i, [len(str(v)) for v in cs], len(hits)))
    st, tc, j, x = hits[0]
    if tc is None: return None, None
    return j, [a + sum(b * x[v] for v, b in co.items()) for a, co in tc]


N = int(sys.argv[2])
i = int(sys.argv[3]) if len(sys.argv) > 3 else 0
cs = [int(v) for v in sys.argv[4:]] if len(sys.argv) > 4 else [35]
B = '00001 (1000)^n 101000010000001011 (1000)^n 101000000101'
A = '00001 (1000)^n 10100001101000 (0001)^n 01000000101'
visits = collections.Counter(); best = {}
close = {'A': None, 'B': None}; nodd = 0; firstodd = None
t0 = time.time()
import math
def lg(v): return math.log10(v) if v < 10 ** 300 else len(str(v))
for n in range(N):
    visits[i] += 1
    t, r = L[i][0], tuple(L[i][1])
    if len(cs) == 2:
        P, Q = cs
        ratio = lg(Q) - lg(P) if min(P, Q) > 0 else 0
        best[i] = max(best.get(i, -1e9), ratio)
        if t == B and r[1] == 1:
            nodd += 1
            if firstodd is None: firstodd = n
        for nm_, sh, off in (('A', A, 16), ('B', B, 24)):
            if t == sh:
                d = abs(Q - 3 * P + off)
                if close[nm_] is None or d < close[nm_][0]: close[nm_] = (d, n, len(str(P)))
        if t == A and Q == 3 * P - 16 or t == B and Q == 3 * P - 24:
            print('ON A HALTING LINE at node', n)
    j, cs2 = step(i, cs)
    if j is None:
        print('HALT at node', n); break
    i, cs = j, cs2
    if n % 100000 == 0:
        print('node', n, 'class', i, 'digits', [len(str(v)) for v in cs], '%.0f s' % (time.time() - t0)); sys.stdout.flush()
print('nodes', n + 1, 'last digits', [len(str(v)) for v in cs])
print('B with Q odd: %d visits, first at node %s' % (nodd, firstodd))
print('closest to the lines (|distance|, node, digits of P):', close)
print('visits', sorted(visits.items()))
print('max log10(Q/P) per 2-count class', {k: round(v, 2) for k, v in sorted(best.items())})
