"""Class search with the replay engine (the Python model of the Lean executor), writing a certificate that Lean
can check: a split tree of primitive splits for every class, and one executor run for every leaf.

A *node* is an event (state F at the left end) whose canonical text matches NODE.  Canonical text: as in
py/closure/pclosure.py (blocks with a count < BIG written out, big blocks made maximal and rotated left).  A *class*
is a node text with residues mod MOD for its counts: the counts BIG + r_i + MOD x_i (0 <= r_i < MOD, x_i >= 0 free).

The engine runs a piece (counts affine in the variables, coefficients >= 0) in exploration mode: where the static
engine would depend on the values of the variables it raises `Need`, and the piece is split by ONE primitive split:

  ('res', v, d)   x_v := j + d x_v          for j < d
  ('peel', v, t)  x_v := j                  for j < t,  and  x_v := t + x_v
  ('cmp', u, w)   x_u := x_u + x_w  (u >= w),  and  x_w := x_u + x_w + 1  (w > u)

and every child is run again from the start.  A leaf is a run without `Need`: it is exactly the static run (what
Lean replays).  Leaves: ('node', K, class index, counts) with counts whose coefficients are multiples of MOD (so the
class is the same for every value), or ('halt', K).

usage: python3 explore.py OUT.json [seconds]
"""
import json
import os
import re
import sys
import time
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import engine as E  # noqa: E402
from engine import Need, Halt, Undecided, cst, isconst, cadd, need_ge, need_div  # noqa: E402

BIG = int(os.environ.get('BBBIG', '20'))
MOD = int(os.environ.get('BBMOD', '2'))
NODE = re.compile(os.environ.get('BBNODE', r'^00001(?=1000| \(1000\))(1000)*( \(1000\)\^n )?(1000)*101'))
MAX_MOVES = int(os.environ.get('BBMOVES', '400000'))
START = int(os.environ.get('BBSTART', '0'))   # the state the run from blank tape starts in (0 = A)
MAXDEPTH = 80
ENVV = [10 ** 9 + 7, 10 ** 9 + 9, 998244353, 10 ** 9 + 21, 10 ** 9 + 33, 10 ** 9 + 87, 10 ** 9 + 93, 10 ** 9 + 97]


# ---------------------------------------------------------------- canonical text (pclosure.canon on engine tokens)
def canon(toks):
    """Nearest-first engine tokens -> (text, counts).  In exploration mode a count with a variable must be surely
    >= BIG (else Need)."""
    items = []
    for t in toks:
        if isinstance(t, int):
            items.append(t)
            continue
        w, n = t
        if isconst(n) and n[0] < BIG:
            items.extend(list(w) * n[0])
        else:
            if not isconst(n) and n[0] < BIG:
                need_ge(n, BIG)
            items.append([tuple(w), n])
    changed = True
    while changed:
        changed = False
        for i, t in enumerate(items):
            if not isinstance(t, list):
                continue
            w, L = t[0], len(t[0])
            if i >= L and all(isinstance(x, int) for x in items[i - L:i]) and tuple(items[i - L:i]) == w:
                del items[i - L:i]
                t[1] = cadd(t[1], cst(1))
                changed = True
                break
            if all(isinstance(x, int) for x in items[i + 1:i + 1 + L]) and tuple(items[i + 1:i + 1 + L]) == w:
                del items[i + 1:i + 1 + L]
                t[1] = cadd(t[1], cst(1))
                changed = True
                break
            if i >= 1 and isinstance(items[i - 1], int) and items[i - 1] == w[-1]:
                x = items[i - 1]
                t[0] = (x,) + w[:-1]
                del items[i - 1]
                items.insert(i, x)
                changed = True
                break
            if i + 1 < len(items) and isinstance(items[i + 1], list) and items[i + 1][0] == w:
                t[1] = cadd(t[1], items[i + 1][1])
                del items[i + 1]
                changed = True
                break
    while items and items[-1] == 0:
        items.pop()
    text = []
    counts = []
    for t in items:
        if isinstance(t, list):
            text.append('(%s)^n' % ''.join(map(str, t[0])))
            counts.append(E.ctrim(t[1]))
        else:
            text.append(str(t))
    return ' '.join(text).replace(' ', '').replace(')^n', ')^n ').replace('(', ' (').strip(), counts


def build(text, counts):
    """Nearest-first tokens of a node text with the given counts."""
    toks = []
    it = iter(counts)
    for part in text.split():
        if part.startswith('('):
            toks.append((tuple(int(c) for c in part[1:part.index(')')]), next(it)))
        else:
            toks.extend(int(c) for c in part)
    return toks


# ---------------------------------------------------------------- substitutions
def csubst(n, v, k, m):
    """n with x_v := k + sum m_i x_i (m a tuple)."""
    a = list(n[1])
    if v >= len(a) or a[v] == 0:
        return n
    p = a[v]
    a[v] = 0
    c = n[0] + p * k
    L = max(len(a), len(m))
    a = a + [0] * (L - len(a))
    for i, q in enumerate(m):
        a[i] += p * q
    return E.ctrim((c, tuple(a)))


def unit(v, coef=1):
    return tuple([0] * v + [coef])


def children(split, counts):
    kind = split[0]
    if kind == 'res':
        _, v, d = split
        return [[csubst(n, v, j, unit(v, d)) for n in counts] for j in range(d)]
    if kind == 'peel':
        _, v, t = split
        return [[csubst(n, v, j, ()) for n in counts] for j in range(t)] + \
               [[csubst(n, v, t, unit(v)) for n in counts]]
    _, u, w = split
    a = [0] * (max(u, w) + 1)
    a[u] = 1
    a[w] = 1
    a = tuple(a)
    return [[csubst(n, u, 0, a) for n in counts], [csubst(n, w, 1, a) for n in counts]]


def prim(D):
    """One primitive split towards the sign of the affine form D = (k, coefficients)."""
    k, c = D
    pos = [i for i, p in enumerate(c) if p > 0]
    neg = [i for i, p in enumerate(c) if p < 0]
    if not neg:
        assert k < 0 and pos, D
        u = pos[0]
        return ('peel', u, -(k // c[u]))           # x_u >= ceil(-k / c_u)
    if not pos:
        assert k >= 0, D
        w = neg[0]
        return ('peel', w, k // (-c[w]) + 1)
    u, w = pos[0], neg[0]
    if len(pos) == 1 and len(neg) == 1:
        cu, cw = c[u], -c[w]
        g = gcd(cu, cw)
        if cw // g > 1:
            return ('res', u, cw // g)
        if cu // g > 1:
            return ('res', w, cu // g)
        L = cu
        t = -(k // L)                               # ceil(-k / L):  D >= 0  <=>  x_u - x_w >= t
        if t > 0:
            return ('peel', u, t)
        if t < 0:
            return ('peel', w, -t)
        return ('cmp', u, w)
    return ('cmp', u, w)


# ---------------------------------------------------------------- the search
class Explorer:
    def __init__(self, shR, shL, rules, discover, log=print):
        self.shR, self.shL, self.rules = shR, shL, rules
        self.discover = discover
        self.keys = []            # class keys (text, residues)
        self.index = {}
        self.trees = {}
        self.todo = []
        self.log = log
        self.nrun = 0
        self.halts = 0
        self.undec = []
        self.nleaves = 0

    def key_index(self, key):
        if key not in self.index:
            self.index[key] = len(self.keys)
            self.keys.append(key)
            self.todo.append(key)
        return self.index[key]

    def run(self, text, counts):
        """One run of a piece: a leaf, or Need."""
        e = E.Engine(self.shR, self.shL, self.rules, self.discover)
        e.env = ENVV
        e.st = E.EV
        e.R = list(reversed(build(text, counts)))
        self.nrun += 1
        try:
            while e.moves < MAX_MOVES:
                ev = e.ev
                e.move()
                if e.ev != ev and e.st == E.EV and not e.L:
                    t, cs = canon(e.toks())
                    if NODE.match(t):
                        for n in cs:
                            need_div(n, MOD)
                        res = tuple(n[0] % MOD for n in cs)
                        return ('node', e.moves, (t, res), cs)
        except Halt:
            return ('halt', e.moves)
        except Undecided as ex:
            return ('undecided', str(ex))
        return ('undecided', 'no node in %d moves' % MAX_MOVES)

    def tree(self, text, counts, depth=0):
        try:
            leaf = self.run(text, counts)
        except Need as ex:
            sp = ex.split
            if sp[0] == 'cmp':
                sp = prim(sp[1])
            if depth > MAXDEPTH:
                self.undec.append((text, counts, 'too deep'))
                return {'leaf': ['undecided', 'too deep'], 'start': counts}
            return {'split': list(sp), 'ch': [self.tree(text, ch, depth + 1) for ch in children(sp, counts)]}
        self.nleaves += 1
        if leaf[0] == 'node':
            j = self.key_index(leaf[2])
            return {'leaf': ['node', leaf[1], j, leaf[3]], 'start': counts}
        if leaf[0] == 'halt':
            self.halts += 1
            return {'leaf': ['halt', leaf[1]], 'start': counts}
        self.undec.append((text, counts, leaf[1]))
        self.log('undecided: %s %s: %s' % (text, counts, leaf[1]))
        return {'leaf': ['undecided', leaf[1]], 'start': counts}

    def root(self, key):
        text, res = key
        return [(BIG + (r - BIG) % MOD, unit(i, MOD)) for i, r in enumerate(res)]

    def bfs(self, start, budget=None):
        self.key_index(start)
        t0 = time.time()
        while self.todo:
            if budget and time.time() - t0 > budget:
                self.log('stopped: %d shapes left' % len(self.todo))
                return False
            key = self.todo.pop(0)
            before = self.nleaves
            self.trees[key] = self.tree(key[0], self.root(key))
            if len(self.trees) % 20 == 0 or len(self.trees) < 5:
                self.log('%4d classes, queue %3d, runs %6d, leaves %6d, rules %d, %5.0f s | %d: %s %s' % (
                    len(self.trees), len(self.todo), self.nrun, self.nleaves, len(self.rules), time.time() - t0,
                    self.nleaves - before, key[0], key[1]))
        return True


def arrival(shR, shL, rules, discover, limit=10 ** 7):
    """Static run from blank tape to the first node: (moves, key, counts)."""
    e = E.Engine(shR, shL, rules, discover)
    e.st = START
    while e.moves < limit:
        ev = e.ev
        e.move()
        if e.ev != ev and e.st == E.EV and not e.L:
            t, cs = canon(e.toks())
            if NODE.match(t) and cs:
                return e.moves, (t, tuple(n[0] % MOD for n in cs)), cs
    raise RuntimeError('no node')


def fmtc(n):
    return E.cfmt(n)


def dump(path, ex, arr):
    def enc(tr):
        if 'leaf' in tr:
            lf = tr['leaf']
            out = {'leaf': lf[:3] + ([[[n[0], list(n[1])] for n in lf[3]]] if lf[0] == 'node' else [])}
            out['start'] = [[n[0], list(n[1])] for n in tr['start']]
            return out
        return {'split': tr['split'], 'ch': [enc(c) for c in tr['ch']]}
    json.dump(dict(machine=E.MACHINE, big=BIG, mod=MOD, node=NODE.pattern,
                   arrival=dict(moves=arr[0], key=list(arr[1]), counts=[n[0] for n in arr[2]], start=START),
                   classes=[dict(text=k[0], res=list(k[1]), tree=enc(ex.trees[k])) for k in ex.keys if k in ex.trees]),
              open(path, 'w'))


def save_tables(path, shR, shL, rules):
    def tab(t):
        return [[st, list(w), [[k, list(u), list(v), c] for k, u, v, c in lst]] for (st, w), lst in t.items()]

    def tm(t):
        return t if isinstance(t, int) else [t[0], list(t[1])] + list(t[2:])
    json.dump(dict(shR=tab(shR), shL=tab(shL), rules=[[r.M, [tm(t) for t in r.tmpl], r.events, r.K] for r in rules]),
              open(path, 'w'))


def load_tables(path):
    d = json.load(open(path))

    def tab(t):
        return {(st, tuple(w)): [(k, tuple(u), tuple(v), c) for k, u, v, c in lst] for st, w, lst in t}

    def tm(t):
        return t if isinstance(t, int) else (t[0], tuple(t[1])) + tuple(t[2:])
    return tab(d['shR']), tab(d['shL']), [(M, [tm(t) for t in tmpl], ev, K) for M, tmpl, ev, K in d['rules']]


def main():
    out = sys.argv[1]
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else None
    E.SPLIT = False
    shR, shL, rules = {}, {}, []
    arr = arrival(shR, shL, rules, True)
    print('arrival (discovery): %d moves, %s %s' % (arr[0], arr[1], arr[2]))
    for rnd in range(6):
        E.SPLIT = True
        nr = len(rules)
        ex = Explorer(shR, shL, rules, True)
        ex.bfs(arr[1], budget)
        print('discovery pass %d: %d classes, %d leaves, %d halting, %d undecided, rules %d -> %d' % (
            rnd, len(ex.trees), ex.nleaves, ex.halts, len(ex.undec), nr, len(rules)))
        if len(rules) == nr:
            break
    # static pass: tables fixed
    rules2 = []
    for r in rules:
        q = E.Rule(r.M, r.tmpl, r.events)
        assert E.prove_rule(q, shR, shL, False)
        rules2.append(q)
    E.SPLIT = False
    arr = arrival(shR, shL, rules2, False)
    E.SPLIT = True
    ex = Explorer(shR, shL, rules2, False)
    ok = ex.bfs(arr[1], budget)
    print('static pass: %d classes, %d leaves, %d halting, %d undecided, %d runs' % (
        len(ex.trees), ex.nleaves, ex.halts, len(ex.undec), ex.nrun))
    dump(out, ex, arr)
    save_tables(out + '.tables.json', shR, shL, rules2)
    print('written', out)


if __name__ == '__main__':
    main()
