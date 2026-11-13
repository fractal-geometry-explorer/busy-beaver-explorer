"""Closed set of node shapes with free counts (several variables), for a machine given by the environment
(BBM, BBEV, BBMIRROR as for gaccel.py; BBNODE: a regular expression that the canonical text of a node must match).

A *node* is an event whose canonical text matches BBNODE.  Canonical text: repeats with a count < BIG written out,
big repeats made maximal and rotated left, their counts replaced by n.  A *class* is a node shape with every big
count free (count_i = BIG + x_i, x_i >= 0, independent).  For a class the engine runs with the x_i as variables
until the next node.  Whenever the run needs to know something about the variables it stops, the class is split
into finitely many pieces (residues of one variable, a half-plane of two variables, or peeling one value) and each
piece is run again from the start.  The set is closed when every piece of every class reaches a node whose shape is
in the set, and no piece halts.
"""
import json
import os
import re
import sys
import time
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paccel as accel  # noqa: E402
from paccel import Driver, Lin, NeedCmp, NeedSplitVar, Sim, Undecided, compress, norm  # noqa: E402

accel.TRACK_STEPS = False
BIG = accel.BIG
NODE = re.compile(os.environ.get('BBNODE', r'^00001(?=1000| \(1000\))(1000)*( \(1000\)\^n )?(1000)*101'))
ENV = {i: p for i, p in enumerate([10 ** 9 + 7, 10 ** 9 + 9, 998244353, 10 ** 9 + 21, 10 ** 9 + 33, 10 ** 9 + 87])}
MAX_MOVES = int(os.environ.get('BBMOVES', '2000000'))
MOD = int(os.environ.get('BBMOD', '2'))
PLAIN = os.environ.get('BBPLAIN', '00001,1000,101').split(',')   # prefix, word, suffix of a node for c/round.c


def canon(toks):
    """(text, counts): cells and big repeats; raises NeedCmp if a count is not surely big or surely small."""
    items = []                   # ints and [word, count]
    for t in toks:
        if t == 'H':
            continue
        if isinstance(t, list):
            n = t[1]
            if isinstance(n, int) and n < BIG:
                items.extend(t[0] * n)
            else:
                if isinstance(n, Lin):
                    accel.ge(n, BIG)
                items.append([tuple(t[0]), n])
        else:
            items.append(t)
    # make big repeats maximal and rotated left
    changed = True
    while changed:
        changed = False
        for i, t in enumerate(items):
            if not isinstance(t, list):
                continue
            w, L = t[0], len(t[0])
            if i >= L and all(isinstance(x, int) for x in items[i - L:i]) and tuple(items[i - L:i]) == w:
                del items[i - L:i]
                t[1] = t[1] + 1
                changed = True
                break
            if all(isinstance(x, int) for x in items[i + 1:i + 1 + L]) and tuple(items[i + 1:i + 1 + L]) == w:
                del items[i + 1:i + 1 + L]
                t[1] = t[1] + 1
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
                t[1] = t[1] + items[i + 1][1]
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
            counts.append(t[1])
        else:
            text.append(str(t))
    return ' '.join(text).replace(' ', '').replace(')^n', ')^n ').replace('(', ' (').strip(), counts


def build(text, counts):
    s = Sim()
    s.st = accel.EVSTATE
    toks = []
    it = iter(counts)
    for part in text.split():
        if part.startswith('('):
            toks.append([tuple(int(c) for c in part[1:part.index(')')]), next(it)])
        else:
            toks.extend(int(c) for c in part)
    s.L = []
    s.R = list(reversed(toks))
    s.steps = Lin(0)
    s.recompress()
    return s


def subst(f, sub):
    """f: Lin or int; sub: {var: (const, {newvar: coef})}; variables not in sub stay."""
    if isinstance(f, int):
        return f
    k = f.k
    c = {}
    for v, a in f.c.items():
        if v in sub:
            k0, m = sub[v]
            k += a * k0
            for nv, b in m.items():
                c[nv] = c.get(nv, 0) + a * b
        else:
            c[v] = c.get(v, 0) + a
    return norm(Lin(k, c))


def splits(e):
    """The substitutions that split a class for exception e (they cover all values of the variables)."""
    if isinstance(e, NeedSplitVar):
        return [{e.v: (j, {e.v: e.d})} for j in range(e.d)]
    D = e.D
    pos = [v for v, a in D.c.items() if a > 0]
    neg = [v for v, a in D.c.items() if a < 0]
    if len(pos) == 1 and not neg:
        v = pos[0]
        t = -(D.k // D.c[v])                      # smallest x with D >= 0
        t = max(t, 1)
        return [{v: (j, {})} for j in range(t)] + [{v: (t, {v: 1})}]
    if len(neg) == 1 and not pos:
        v = neg[0]
        t = D.k // (-D.c[v]) + 1                  # smallest x with D < 0
        t = max(t, 1)
        return [{v: (j, {})} for j in range(t)] + [{v: (t, {v: 1})}]
    if len(pos) == 1 and len(neg) == 1:
        u, w = pos[0], neg[0]
        c0, c1 = D.c[u], -D.c[w]
        g = gcd(c0, c1)
        L = c0 * c1 // g
        out = []
        for i in range(c1 // g):
            for j in range(c0 // g):
                kap = D.k + c0 * i - c1 * j
                t = -(kap // L)                   # D >= 0  <=>  u' - w' >= t
                A, B = c1 // g, c0 // g           # x_u = A u' + i, x_w = B w' + j

                def piece(uc, um, wc, wm):
                    return {u: (A * uc + i, {v: A * b for v, b in um.items()}),
                            w: (B * wc + j, {v: B * b for v, b in wm.items()})}
                # region u' - w' >= t   (new variables: id w for w', id u for the slack)
                if t >= 0:
                    out.append(piece(t, {w: 1, u: 1}, 0, {w: 1}))
                else:
                    out.append(piece(0, {w: 1, u: 1}, -t, {w: 1}))
                    for ww in range(-t):
                        out.append(piece(0, {u: 1}, ww, {}))
                # region w' - u' >= s, s = 1 - t
                s = 1 - t
                if s >= 0:
                    out.append(piece(0, {u: 1}, s, {u: 1, w: 1}))
                else:
                    out.append(piece(-s, {u: 1}, 0, {u: 1, w: 1}))
                    for uu in range(-s):
                        out.append(piece(uu, {}, 0, {w: 1}))
        return out
    v = (pos + neg)[0]
    return [{v: (0, {})}, {v: (1, {v: 1})}]


class Explorer:
    def __init__(self, log=print):
        self.rules = {}
        self.classes = {}        # text -> list of leaves (dicts)
        self.todo = []
        self.log = log
        self.halts = []
        self.undec = []
        self.nrun = 0

    def run_leaf(self, text, counts):
        d = Driver(build(text, [c if isinstance(c, int) else Lin(c.k, c.c) for c in counts]), True)
        d.rules = self.rules
        d.env = ENV
        out = {}

        def on_event(d, toks):
            t, cs = canon(toks)
            if NODE.match(t):
                out['to'] = t
                out['counts'] = cs
                return True
            return False

        self.nrun += 1
        d.run(None, on_event, max_moves=MAX_MOVES)
        if d.s.halt:
            return dict(kind='halt')
        if not out:
            return dict(kind='undecided', why='no node within %d moves' % d.moves)
        import itertools
        vs = sorted({v for c in out['counts'] if isinstance(c, Lin) for v in c.c})
        keys = set()
        for xs in itertools.product(range(MOD), repeat=len(vs)):
            e = dict(zip(vs, xs))
            keys.add((out['to'], tuple((c if isinstance(c, int) else c.k + sum(a * e[v] for v, a in c.c.items())) % MOD
                                       for c in out['counts'])))
        return dict(kind='node', to=out['to'], counts=[repr(c) for c in out['counts']], moves=d.moves,
                    keys=sorted(keys))

    def explore(self, key):
        text, res0 = key
        leaves = []
        stack = [[Lin(BIG + (r - BIG) % MOD, {i: MOD}) for i, r in enumerate(res0)]]
        while stack:
            counts = stack.pop()
            if len(leaves) + len(stack) > 20000:
                leaves.append(dict(kind='undecided', why='too many pieces', start=[repr(c) for c in counts]))
                break
            try:
                res = self.run_leaf(text, counts)
            except (NeedSplitVar, NeedCmp) as e:
                for sub in splits(e):
                    stack.append([subst(c, sub) for c in counts])
                continue
            except Undecided as e:
                res = dict(kind='undecided', why=str(e))
            res['start'] = [repr(c) for c in counts]
            leaves.append(res)
            if res['kind'] == 'node':
                for k2 in res.pop('keys'):
                    if k2 not in self.classes and k2 not in self.todo:
                        self.todo.append(k2)
            elif res['kind'] == 'halt':
                self.halts.append((key, res['start']))
                self.log('HALT: %s with counts %s' % (key, res['start']))
            else:
                self.undec.append((key, res['start'], res['why']))
                self.log('undecided: %s with counts %s: %s' % (key, res['start'], res['why']))
        return leaves

    def bfs(self, start, budget=None, out=None):
        self.todo.append(start)
        t0 = time.time()
        while self.todo:
            if budget and time.time() - t0 > budget:
                self.log('stopped: %d shapes left' % len(self.todo))
                break
            text = self.todo.pop(0)
            if text in self.classes:
                continue
            leaves = self.explore(text)
            self.classes[text] = leaves
            self.log('%4d classes, queue %3d, runs %6d, %5.0f s | %3d pieces: %s' % (
                len(self.classes), len(self.todo), self.nrun, time.time() - t0, len(leaves), text))
            if out:
                json.dump(dict(machine=accel.MACHINE, big=BIG, mod=MOD, node=NODE.pattern, plain=PLAIN,
                               classes=[[k[0], list(k[1]), v] for k, v in self.classes.items()],
                               todo=[[k[0], list(k[1])] for k in self.todo]), open(out, 'w'))
        return not self.todo and not self.halts and not self.undec


def real_nodes(seconds, minbig=1):
    d = Driver()
    t0 = time.time()
    res = []

    def on_event(d, toks):
        t, cs = canon(toks)
        if NODE.match(t):
            res.append((d.s.steps, t, cs))
        return time.time() - t0 > seconds

    d.run(None, on_event)
    return res


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'nodes':
        for st, t, cs in real_nodes(float(sys.argv[2])):
            print(len(str(st)), t, [c if c < 10 ** 9 else '%d digits' % len(str(c)) for c in cs])
    elif cmd == 'bfs':
        nodes = real_nodes(float(sys.argv[3]) if len(sys.argv) > 3 else 5)
        st, t, cs = [x for x in nodes if x[2]][0]
        print('start: step %d, %s %s' % (st, t, cs))
        ex = Explorer()
        t = (t, tuple(c % MOD for c in cs))
        ok = ex.bfs(t, budget=float(sys.argv[4]) if len(sys.argv) > 4 else None, out=sys.argv[2])
        print('shapes %d, runs %d, halting pieces %d, undecided pieces %d, cycle rules %d' % (
            len(ex.classes), ex.nrun, len(ex.halts), len(ex.undec), sum(len(v) for v in ex.rules.values())))
        print('CLOSED, no halting piece' if ok else 'NOT CLOSED')
