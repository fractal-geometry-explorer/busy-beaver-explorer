"""Class search with free counts that have their own lower bounds, cover checks and widening (block lists).

pclosure_inner.py keys a class by a canonical text in which every count below BIG is written out.  On the F01 machines
the sets of classes keep growing as lists of short blocks: `10 (101)^n`, `10110 (101)^n`, `10110110 (101)^n`, ... are
three classes although they are one family `1 (011)^m 0 (101)^n`.  This search changes what a class is:

* A *class* is a list of items: cells 0/1 and repeats (w)^{>= lo}, each repeat with its own free count lo + x
  (x >= 0, independent).  lo may be 0 (the block may be absent).  Its language is the set of tapes it writes out.
* A *node* (the tape at the next event, with counts that may carry variables) is *covered* by a class when a
  matcher shows that every instance of it is in the class's language: cells match cells, a repeat of the class
  takes whole literal copies of its word and whole repeats of the node with the same word, and the count it takes
  is at least lo for every value of the variables.  A covered node needs no new class.
* *Widening*: when no class covers a node, but some class would if some of its lower bounds were smaller, those
  bounds are lowered (the class only grows), the old class is dropped and the wider one is explored instead.
  Otherwise a new class is made from the node: its cells are factored into repeats (count >= BBCMIN of a word of at
  most BBWMAX cells), and every repeat gets the free count min(count, BBG) + x.
* At the end every leaf of every class is checked again (strictly) against the final set: CLOSED means that every
  piece of every class reaches, as its first event, a node covered by a class of the set, and no piece halts or
  is undecided.  The start node is covered as well.

The symbolic runs are those of paccel_inner.py (inner cycle rules with BBINNER=1); the only engine change is in
`try_cross`: a repeat whose count carries a variable is crossed when its constant part is at least the number of
copies taken (it used to need a constant part of at least 6, which with small lower bounds peels every count).

Two changes of the search itself: the sign of k + sum c_v x_v with one variable of one sign and several of the other
is split on the part with one variable of each sign (`splits`; pclosure_inner.py peels one variable there, which never
ends), and a question asked by a machine step (`safe_step`, asked before anything is changed) splits the piece and
lets each part go on from that point instead of from the start (BBRESUME=1; the run's cycle history is kept, with the
point where cycles are looked for moved along the substitution).  With BBJOBS > 1 or BBCKPT the classes are explored
by worker processes and the set is saved to the checkpoint file BBCKPT now and then (a run resumes from it).

usage: BBM=... BBEV=... BBMIRROR=... BBINNER=1 python3 pclosure_list.py OUT.json [START_SECONDS] [BUDGET_SECONDS]
Environment: BBG (2), BBCMIN (2), BBWMAX (3), BBMOVES (150000), BBMAXPIECES (20000), BBCLASSTIME (30), BBWIDEN (1),
BBRESUME (1), BBJOBS (1), BBCKPT, BBCKPTEVERY (900), BBTRACE (seconds before a traceback dump and exit).
Written 16 Nov 2026 (LISTS.md in this folder).
"""
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paccel_inner as accel  # noqa: E402
from paccel_inner import Driver, Lin, NeedCmp, NeedSplitVar, Sim, Undecided, norm  # noqa: E402
from pclosure_inner import ENV, _Env, subst  # noqa: E402
from pclosure_inner import splits as splits2  # noqa: E402


def splits(e):
    """pclosure_inner.splits, and for the sign of D = k + sum c_v x_v with one variable of one sign and several of
    the other: split on the sign of the part with one variable of each sign (the other variables only push D further
    the same way in one of the halves, and the other half has the comparison again with one variable less).  The
    pieces cover all values; pclosure_inner peels one variable here (x = 0, x >= 1), which never ends."""
    if isinstance(e, NeedCmp):
        D = e.D
        pos = [v for v, a in D.c.items() if a > 0]
        neg = [v for v, a in D.c.items() if a < 0]
        if (len(neg) == 1 and len(pos) > 1) or (len(pos) == 1 and len(neg) > 1):
            p, n = pos[0], neg[0]
            D2 = Lin(D.k)
            D2.c = {p: D.c[p], n: D.c[n]}
            return splits2(NeedCmp(D2))
    return splits2(e)

accel.TRACK_STEPS = False
G = int(os.environ.get('BBG', '2'))
CMIN = int(os.environ.get('BBCMIN', '2'))
WMAX = int(os.environ.get('BBWMAX', '3'))
CLASS_TIME = float(os.environ.get('BBCLASSTIME', '30'))
MAX_MOVES = int(os.environ.get('BBMOVES', '150000'))
MAXPIECES = int(os.environ.get('BBMAXPIECES', '20000'))
MAXSPLIT = int(os.environ.get('BBMAXSPLIT', '2000'))
WIDEN = os.environ.get('BBWIDEN', '1') == '1'
FLATMAX = 1000
DEBUG = os.environ.get('BBDEBUG') == '1'


# ------------------------------------------------------------------ engine change: crossing small symbolic repeats
def try_cross(s):
    """Sim.try_cross of paccel_inner.py, with the guard on a repeat whose count carries a variable relaxed: it is
    crossed k copies at a time when its constant part is >= k (so the count is >= k for every value)."""
    def ok(n, k):
        if isinstance(n, int):
            return n >= accel.MINN
        return n.k >= k

    if s.R and isinstance(s.R[-1], list) and (not isinstance(s.R[-1][1], int) or s.R[-1][1] >= accel.MINN):
        w, n = s.R[-1]
        lit = s.lits_L(accel.MAXC)
        for k in accel.KS:
            if not ok(n, k):
                continue
            for lu in range(0, len(lit) + 1):
                u = lit[len(lit) - lu:]
                r = accel.one_right(s.st, u, w * k)
                if r:
                    v, c = r
                    m, rem = accel.div(n, k)
                    if rem:
                        s.R[-1][1] = rem
                    else:
                        s.R.pop()
                    del s.L[len(s.L) - lu:]
                    s.pushL(v, m)
                    s.L.extend(u)
                    s.steps = s.steps + c * m
                    s.last = ('R', 'ABCDEF'[s.st], u, w * k, v, m, c)
                    return True
    if s.L and isinstance(s.L[-1], list) and (not isinstance(s.L[-1][1], int) or s.L[-1][1] >= accel.MINN):
        w, n = s.L[-1]
        lit = s.lits_R(accel.MAXC)
        for k in accel.KS:
            if not ok(n, k):
                continue
            for lu in range(1, len(lit) + 1):
                u = lit[:lu]
                r = accel.one_left(s.st, u, w * k)
                if r and len(s.L) == 1 and accel.evmid[(s.st, u, w * k)]:
                    r = None
                if r:
                    v, c = r
                    m, rem = accel.div(n, k)
                    if rem:
                        s.L[-1][1] = rem
                    else:
                        s.L.pop()
                    del s.R[len(s.R) - lu:]
                    s.pushR(v, m)
                    s.R.extend(reversed(u))
                    s.steps = s.steps + c * m
                    s.last = ('L', 'ABCDEF'[s.st], u, w * k, v, m, c)
                    return True
    return False


Sim.try_cross = try_cross
_step0 = Sim.step


def safe_step(s):
    """Sim.step, but a question about a count (popping from a repeat whose count could be 1) is asked before
    anything is changed, so that after a split the run can go on from where it stopped (BBRESUME=1)."""
    if not s.try_cross():
        cell = None
        if s.R and isinstance(s.R[-1], list):
            n = s.R[-1][1]
            if isinstance(n, Lin) and n.k < 2:
                raise NeedCmp(n - 2, "pop from %r" % (n,))
            cell = s.R[-1][0][0]
        elif s.R:
            cell = s.R[-1]
        else:
            cell = 0
        t = accel.T.get((s.st, cell)) if cell in (0, 1) else None
        if t is not None and t[1] == -1 and s.L and isinstance(s.L[-1], list):
            n = s.L[-1][1]
            if isinstance(n, Lin) and n.k < 2:
                raise NeedCmp(n - 2, "pop from %r" % (n,))
        return _step0_nocross(s)
    return 'x'


def _step0_nocross(s):
    tc = s.try_cross
    s.try_cross = lambda: False
    try:
        return _step0(s)
    finally:
        del s.try_cross


RESUME = os.environ.get('BBRESUME', '1') == '1'


class Resume(Exception):
    """A split question asked by a machine step, with the state just before that step."""

    def __init__(self, e, snap):
        Exception.__init__(self, str(e))
        self.e = e
        self.snap = snap


def snapshot(d):
    s = d.s
    return dict(L=[list(t) if isinstance(t, list) else t for t in s.L],
                R=[list(t) if isinstance(t, list) else t for t in s.R], st=s.st, moves=d.moves,
                drv=(d.hist, d.chist, d.failed, d.cfailed, d.cp, d.ev), env=dict(d.env))


def subst_snap(snap, sub):
    def tk(ts):
        out = []
        for t in ts:
            if isinstance(t, list):
                n = subst(t[1], sub)
                if isinstance(n, int) and n == 0:
                    continue
                out.append([t[0], n])
            else:
                out.append(t)
        return out
    env = _Env(snap['env'])         # the point where cycles are looked for, moved with the substitution so that
    for v, (j, m) in sub.items():   # the counts there stay the same and the history of the run stays usable
        if v in m and m[v]:
            env[v] = max(1, (env[v] - j) // m[v])
    return dict(L=tk(snap['L']), R=tk(snap['R']), st=snap['st'], moves=snap['moves'], drv=snap['drv'], env=env)


def run_driver(d, on_event, max_moves):
    """Driver.run of paccel_inner.py (maxsteps None), with machine steps by safe_step: a split question asked by a
    step raises Resume with the state before the step."""
    s = d.s
    last = 0
    while not s.halt:
        if RESUME:
            try:
                r = safe_step(s)
            except (NeedCmp, NeedSplitVar) as e:
                raise Resume(e, snapshot(d))
        else:
            r = s.step()
        d.moves += 1
        if r == 'x' and accel.INNER and d.accel and not s.event(r):
            d.cp += 1
            if d.at_checkpoint():
                d.cjumps += 1
            last = d.moves
        if s.event(r):
            s.recompress()
            d.ev += 1
            toks = d.at_event()
            last = d.moves
            if on_event and on_event(d, toks):
                break
        elif d.moves - last > 2000:
            s.recompress()
            last = d.moves
        if max_moves and d.moves >= max_moves:
            break
    return s


# ------------------------------------------------------------------ nodes and classes
def primitive(w):
    for d in range(1, len(w)):
        if len(w) % d == 0 and w[:d] * (len(w) // d) == w:
            return False
    return True


def normalize(items):
    """items: ints (cells) and ['R', word, count] (count an int, a Lin, or a lower bound for classes).  Repeats absorb
    equal literal words next to them, merge with equal neighbours and are rotated as far left as they go; trailing
    zero cells are dropped.  The language (the set of tapes) does not change."""
    items = [list(t) if isinstance(t, list) else t for t in items]
    changed = True
    while changed:
        changed = False
        for i, t in enumerate(items):
            if not isinstance(t, list):
                continue
            w, L = t[1], len(t[1])
            if i >= L and all(isinstance(x, int) for x in items[i - L:i]) and tuple(items[i - L:i]) == w:
                del items[i - L:i]
                t[2] = t[2] + 1
                changed = True
                break
            if all(isinstance(x, int) for x in items[i + 1:i + 1 + L]) and len(items[i + 1:i + 1 + L]) == L \
                    and tuple(items[i + 1:i + 1 + L]) == w:
                del items[i + 1:i + 1 + L]
                t[2] = t[2] + 1
                changed = True
                break
            if i >= 1 and isinstance(items[i - 1], int) and items[i - 1] == w[-1]:
                x = items[i - 1]
                t[1] = (x,) + w[:-1]
                del items[i - 1]
                items.insert(i, x)
                changed = True
                break
            if i + 1 < len(items) and isinstance(items[i + 1], list) and items[i + 1][1] == w:
                t[2] = t[2] + items[i + 1][2]
                del items[i + 1]
                changed = True
                break
    while items and (items[-1] == 0 or (isinstance(items[-1], list) and set(items[-1][1]) == {0})):
        items.pop()
    return items


def node_form(toks):
    """The node of a token list at an event: cells, and repeats whose count carries a variable or is >= FLATMAX."""
    items = []
    for t in toks:
        if t == 'H':
            continue
        if isinstance(t, list):
            w = tuple(t[0])
            n = t[1]
            for d in range(1, len(w)):
                if len(w) % d == 0 and w[:d] * (len(w) // d) == w:
                    n = n * (len(w) // d)
                    w = w[:d]
                    break
            if isinstance(n, int) and n < FLATMAX:
                items.extend(w * n)
            else:
                items.append(['R', w, n])
        else:
            items.append(t)
    return normalize(items)


def factor(bits):
    """Shortest description of a cell list as cells and repeats (count >= CMIN, word <= WMAX cells, >= 4 cells)."""
    n = len(bits)
    INF = 10 ** 9
    cost = [INF] * (n + 1)
    choice = [None] * (n + 1)
    cost[n] = 0
    for i in range(n - 1, -1, -1):
        cost[i] = cost[i + 1] + 1
        choice[i] = None
        for L in range(1, WMAX + 1):
            w = tuple(bits[i:i + L])
            if len(w) < L or not primitive(w):
                continue
            c = 1
            while tuple(bits[i + c * L:i + (c + 1) * L]) == w:
                c += 1
                if c >= CMIN and c * L >= 4:
                    v = cost[i + c * L] + 2 + L
                    if v < cost[i]:
                        cost[i] = v
                        choice[i] = (w, c)
    out = []
    i = 0
    while i < n:
        if choice[i] is None:
            out.append(bits[i])
            i += 1
        else:
            w, c = choice[i]
            out.append(['R', w, c])
            i += len(w) * c
    return out


def class_of_node(node):
    items = []
    run = []
    for t in node + [None]:
        if isinstance(t, int):
            run.append(t)
            continue
        items.extend(factor(run))
        run = []
        if t is not None:
            items.append(t)
    out = []
    for t in items:
        if isinstance(t, list):
            n = t[2]
            k = n if isinstance(n, int) else n.k
            out.append(['R', t[1], min(k, G)])
        else:
            out.append(t)
    return normalize(out)


def key_of(items):
    out = []
    for t in items:
        if isinstance(t, int):
            if out and out[-1][0] in '01':
                out[-1] += str(t)
            else:
                out.append(str(t))
        else:
            out.append('(%s)^>=%d' % (''.join(map(str, t[1])), t[2]))
    return ' '.join(out)


def jlin(n):
    return [n, {}] if isinstance(n, int) else [n.k, {str(v): a for v, a in n.c.items()}]


def jnode(node):
    return [t if isinstance(t, int) else [list(t[1]), jlin(t[2])] for t in node]


def node_text(node):
    return ' '.join(str(t) if isinstance(t, int) else '(%s)^%r' % (''.join(map(str, t[1])), t[2]) for t in node)


def match(cls, node, widen=False):
    """Does the class cover the node?  Returns None, or the list of constant counts each class repeat takes
    (with widen=True the lower bounds are ignored, so the caller can see how far they must drop)."""
    nc, nn = len(cls), len(node)
    memo = set()

    def go(i, j):
        if (i, j) in memo:
            return None
        if i == nc:
            return [] if j == nn else None
        t = cls[i]
        if isinstance(t, int):
            if j < nn and node[j] == t:
                r = go(i + 1, j + 1)
                if r is not None:
                    return r
            memo.add((i, j))
            return None
        w, lo, L = t[1], t[2], len(t[1])
        # candidate end points: take copies greedily, remember each stop
        stops = [(j, 0, False)]
        jj, k, var = j, 0, False
        while True:
            if jj + L <= nn and all(isinstance(x, int) for x in node[jj:jj + L]) and tuple(node[jj:jj + L]) == w:
                jj += L
                k += 1
            elif jj < nn and isinstance(node[jj], list) and node[jj][1] == w:
                n = node[jj][2]
                k += n if isinstance(n, int) else n.k
                var = var or not isinstance(n, int)
                jj += 1
            else:
                break
            stops.append((jj, k, var))
        for jj, k, var in reversed(stops):
            if not widen and k < lo:
                continue
            r = go(i + 1, jj)
            if r is not None:
                return [k] + r
        memo.add((i, j))
        return None

    return go(0, 0)


def covered(cls, node):
    return match(cls, node) is not None


def build(items, counts):
    s = Sim()
    s.st = accel.EVSTATE
    toks = []
    it = iter(counts)
    for t in items:
        if isinstance(t, list):
            n = next(it)
            if isinstance(n, int) and n == 0:
                continue
            toks.append([t[1], n])
        else:
            toks.append(t)
    s.L = []
    s.R = list(reversed(toks))
    s.steps = Lin(0)
    s.recompress()
    return s


class Explorer:
    def __init__(self, log=print):
        self.rules = {}
        self.crules = {}
        self.defs = {}           # key -> items (live classes, explored or waiting)
        self.leaves = {}         # key -> leaves (explored classes)
        self.todo = []
        self.log = log
        self.nrun = 0
        self.widened = 0
        self.dropped = set()

    def find(self, node):
        for k, c in self.defs.items():
            if covered(c, node):
                return k
        return None

    def place(self, node):
        """The key of a class covering node: an existing one, a widened one, or a new one."""
        k = self.find(node)
        if k is not None:
            return k
        if WIDEN:
            best = None
            for k, c in self.defs.items():
                m = match(c, node, widen=True)
                if m is None:
                    continue
                reps = [t for t in c if isinstance(t, list)]
                drop = sum(max(0, r[2] - x) for r, x in zip(reps, m))
                if best is None or drop < best[0]:
                    best = (drop, k, m)
            if best is not None:
                _, k, m = best
                c = self.defs[k]
                new = []
                it = iter(m)
                for t in c:
                    if isinstance(t, list):
                        new.append(['R', t[1], min(t[2], next(it))])
                    else:
                        new.append(t)
                new = normalize(new)
                k2 = key_of(new)
                self.widened += 1
                self.drop(k)
                self.add(k2, new)
                assert covered(new, node), (k2, node_text(node))
                return k2
        new = class_of_node(node)
        k2 = key_of(new)
        self.add(k2, new)
        assert covered(new, node), (k2, node_text(node))
        return k2

    def drop(self, k):
        self.defs.pop(k, None)
        self.leaves.pop(k, None)
        if k in self.todo:
            self.todo.remove(k)
        self.dropped.add(k)

    def add(self, k, items):
        if k in self.defs:
            return
        self.defs[k] = items
        self.dropped.discard(k)
        self.todo.append(k)
        # classes that the new one covers are dropped (their nodes are covered by it)
        for k3, c3 in list(self.defs.items()):
            if k3 != k and len(c3) <= 3 * len(items) + 40 and self.class_in(c3, items):
                self.drop(k3)

    @staticmethod
    def class_in(c, d):
        """Is class c contained in class d?  (c written as a node with counts lo + x_i.)"""
        node = []
        i = 0
        for t in c:
            if isinstance(t, list):
                node.append(['R', t[1], Lin(t[2], {i: 1})])
                i += 1
            else:
                node.append(t)
        node = normalize(node)
        return covered(d, node)

    def run_leaf(self, items, counts, snap=None):
        sim = build(items, counts)
        d = Driver(sim, True)
        if snap is not None:
            sim.L, sim.R, sim.st = snap['L'], snap['R'], snap['st']
            d.moves = snap['moves']
            d.hist, d.chist, d.failed, d.cfailed, d.cp, d.ev = snap['drv']
        d.rules = self.rules
        d.crules = self.crules
        d.env = ENV if snap is None else snap['env']
        out = {}

        def on_event(d, toks):
            out['node'] = node_form(toks)
            return True

        self.nrun += 1
        try:
            run_driver(d, on_event, MAX_MOVES)
        finally:
            if DEBUG:
                sys.stderr.write('    %d moves, node %s\n' % (d.moves, node_text(out['node']) if out else None))
        if d.s.halt:
            return dict(kind='halt')
        if not out:
            return dict(kind='undecided', why='no node within %d moves' % d.moves)
        return dict(kind='node', node=out['node'], moves=d.moves)

    def explore(self, key):
        items = self.defs[key]
        nrep = sum(1 for t in items if isinstance(t, list))
        leaves = []
        reps = [t for t in items if isinstance(t, list)]
        stack = [([Lin(r[2], {i: 1}) for i, r in enumerate(reps)], None)]
        t0 = time.time()
        while stack:
            counts, snap = stack.pop()
            if time.time() - t0 > CLASS_TIME:
                leaves.append(dict(kind='undecided', why='class time limit', start=[repr(c) for c in counts]))
                break
            if len(leaves) + len(stack) > MAXPIECES:
                leaves.append(dict(kind='undecided', why='too many pieces', start=[repr(c) for c in counts]))
                break
            if DEBUG:
                sys.stderr.write('  piece %s (stack %d, leaves %d)\n' % ([repr(c) for c in counts], len(stack), len(leaves)))
            try:
                res = self.run_leaf(items, counts, snap)
            except (NeedSplitVar, NeedCmp, Resume) as e:
                snap2 = None
                if isinstance(e, Resume):
                    e, snap2 = e.e, e.snap
                sp = splits(e)
                if len(sp) > MAXSPLIT or any(x is None for x in sp):
                    leaves.append(dict(kind='undecided', why='split into %d pieces: %s' % (len(sp), e),
                                       start=[repr(c) for c in counts]))
                    continue
                for sub in sp:
                    stack.append(([subst(c, sub) for c in counts], None if snap2 is None else subst_snap(snap2, sub)))
                continue
            except Undecided as e:
                res = dict(kind='undecided', why=str(e))
            res['start'] = [repr(c) for c in counts]
            leaves.append(res)
        assert nrep == len(reps)
        return leaves

    def bfs(self, start_node, budget=None, out=None):
        k0 = self.place(start_node)
        t0 = time.time()
        while self.todo:
            if budget and time.time() - t0 > budget:
                self.log('stopped: %d classes waiting' % len(self.todo))
                break
            key = self.todo.pop(0)
            if key not in self.defs:
                continue
            if DEBUG:
                sys.stderr.write('class %s\n' % key)
            leaves = self.explore(key)
            if key not in self.defs:
                continue          # dropped while it was explored (a wider class covers it)
            self.leaves[key] = leaves
            bad = 0
            for lf in leaves:
                if lf['kind'] == 'node':
                    self.place(lf['node'])
                else:
                    bad += 1
            if key not in self.defs:
                continue          # one of its own nodes widened it
            self.log('%4d classes, waiting %3d, widened %4d, runs %6d, %5.0f s | %3d pieces, %d halt/undecided: %s' % (
                len(self.leaves), len(self.todo), self.widened, self.nrun, time.time() - t0, len(leaves), bad, key))
        return self.check(start_node, out, k0)

    def bfs_par(self, start_node, jobs, budget=None, out=None, ckpt=None):
        """bfs with `jobs` worker processes exploring classes at the same time (each with its own rule caches), and a
        checkpoint file (pickle of the set) written every few minutes, from which a run can be resumed."""
        import multiprocessing as mp
        import pickle
        if ckpt and os.path.exists(ckpt):
            st = pickle.load(open(ckpt, 'rb'))
            self.defs, self.leaves, self.todo, self.widened, self.dropped, start_node = (
                st['defs'], st['leaves'], st['todo'], st['widened'], st['dropped'], st['start'])
            for k in self.defs:
                if k not in self.leaves and k not in self.todo:
                    self.todo.append(k)
            self.log('resumed: %d classes, %d waiting' % (len(self.leaves), len(self.todo)))
        k0 = self.place(start_node)
        t0 = time.time()
        last = time.time()
        pool = mp.get_context('fork').Pool(jobs, initializer=_winit)
        flying = {}
        nres = 0

        def save():
            if ckpt:
                pickle.dump(dict(defs=self.defs, leaves=self.leaves, todo=self.todo, widened=self.widened,
                                 dropped=self.dropped, start=start_node), open(ckpt + '.tmp', 'wb'))
                os.replace(ckpt + '.tmp', ckpt)
        try:
            while self.todo or flying:
                over = budget and time.time() - t0 > budget
                while not over and self.todo and len(flying) < jobs:
                    key = self.todo.pop(0)
                    if key not in self.defs or key in self.leaves or key in flying:
                        continue
                    flying[key] = pool.apply_async(_wexplore, (key, self.defs[key]))
                if over and not flying:
                    break
                done = [k for k, r in flying.items() if r.ready()]
                if not done:
                    time.sleep(0.2)
                    continue
                for key in done:
                    leaves, nrun = flying.pop(key).get()
                    self.nrun += nrun
                    nres += 1
                    if key not in self.defs:
                        continue
                    self.leaves[key] = leaves
                    bad = 0
                    for lf in leaves:
                        if lf['kind'] == 'node':
                            self.place(lf['node'])
                        else:
                            bad += 1
                    if key not in self.defs:
                        continue
                    self.log('%4d classes, waiting %3d, flying %d, widened %4d, runs %7d, %6.0f s | %5d pieces, %d '
                             'halt/undecided: %s' % (len(self.leaves), len(self.todo), len(flying), self.widened,
                                                     self.nrun, time.time() - t0, len(leaves), bad, key))
                if time.time() - last > float(os.environ.get("BBCKPTEVERY", "900")):
                    save()
                    last = time.time()
            if self.todo or flying:
                self.log('stopped: %d classes waiting' % (len(self.todo) + len(flying)))
                self.todo.extend(k for k in flying if k in self.defs and k not in self.todo)
        finally:
            pool.terminate()
            save()
        return self.check(start_node, out, k0)

    def check(self, start_node, out, k0):
        """Strict recheck of the whole set: every leaf's node covered by a final class."""
        bad = []
        halts = 0
        undec = 0
        for k, leaves in self.leaves.items():
            for lf in leaves:
                if lf['kind'] == 'halt':
                    halts += 1
                elif lf['kind'] == 'undecided':
                    undec += 1
                elif self.find(lf['node']) is None or self.find(lf['node']) not in self.leaves:
                    bad.append((k, node_text(lf['node'])))
        start_ok = self.find(start_node) in self.leaves
        closed = not self.todo and not halts and not undec and not bad and start_ok
        if out:
            json.dump(dict(machine=accel.MACHINE, ev=accel.EVSTATE, mirror=accel.MIRROR, g=G, cmin=CMIN, wmax=WMAX,
                           start=node_text(start_node), closed=closed,
                           classes=[dict(key=k, items=[t if isinstance(t, int) else [list(t[1]), t[2]] for t in self.defs[k]],
                                         leaves=[dict([(a, (node_text(b) if a == 'node' else b)) for a, b in lf.items()]
                                                      + ([('nodej', jnode(lf['node']))] if 'node' in lf else []))
                                                 for lf in v]) for k, v in self.leaves.items()],
                           todo=self.todo), open(out, 'w'))
        self.log('classes %d, waiting %d, runs %d, halting pieces %d, undecided pieces %d, uncovered nodes %d, '
                 'widenings %d, cycle rules %d, inner rules %d' % (
                     len(self.leaves), len(self.todo), self.nrun, halts, undec, len(bad), self.widened,
                     sum(len(v) for v in self.rules.values()), sum(len(v) for v in self.crules.values())))
        self.log('CLOSED, no halting piece' if closed else 'NOT CLOSED')
        return closed


_WEX = None


def _winit():
    global _WEX
    _WEX = Explorer(log=lambda *a: None)


def _wexplore(key, items):
    _WEX.defs[key] = items
    n0 = _WEX.nrun
    leaves = _WEX.explore(key)
    del _WEX.defs[key]
    return leaves, _WEX.nrun - n0


def start_node(seconds):
    """The first event (after `seconds` of plain accelerated running, the last one) with a repeat in it."""
    d = Driver()
    t0 = time.time()
    res = []

    def on_event(d, toks):
        nd = node_form(toks)
        res.append((d.s.steps, nd))
        return time.time() - t0 > seconds or len(res) > 50

    d.run(None, on_event)
    return res


if __name__ == "__main__":
    import faulthandler; faulthandler.dump_traceback_later(float(os.environ.get("BBTRACE", "0")) or 10**7, exit=True)
    out = sys.argv[1]
    secs = float(sys.argv[2]) if len(sys.argv) > 2 else 5
    budget = float(sys.argv[3]) if len(sys.argv) > 3 else None
    nodes = start_node(secs)
    good = [x for x in nodes if any(isinstance(t, list) and t[2] >= 6
                                    for t in factor([c for c in x[1] if isinstance(c, int)]))]
    st, nd = (good or nodes)[0]
    print('start: step %d, %s' % (st, node_text(nd)))
    ex = Explorer()
    jobs = int(os.environ.get('BBJOBS', '1'))
    if jobs > 1 or os.environ.get('BBCKPT'):
        ok = ex.bfs_par(nd, jobs, budget=budget, out=out, ckpt=os.environ.get('BBCKPT'))
    else:
        ok = ex.bfs(nd, budget=budget, out=out)
    sys.exit(0)
