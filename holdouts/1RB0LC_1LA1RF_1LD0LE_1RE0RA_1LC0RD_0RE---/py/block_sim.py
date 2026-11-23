"""One-stack mover simulator for 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---, exact or abstract.

The tape at a right-end turn (head in E on the blank) is one stack Y (top = nearest the head) of items:
  '0' / '1'      single cells
  int g          g pairs, read outward from the head as (1,0)
  ('M', q)       a block of movers at rest `0 0 1 1 0 (01)^g`, q their gaps, the rightmost first
A bounce is one machine run from the right end back to it.  Runs of pairs are crossed by the crossing rules, and a
block by the mover lemmas: `left_all` (head in E on a 0, the block on its left) turns it into swept movers on the
right ('W', q); `right_gen` (head in D or F, a swept block on its right, gaps >= 1) turns it back into movers at
rest, with `rm1`/`fm1` for the swept movers of one-pair gap at its right end.  Anything else is run cell by cell,
opening one mover of a block when the head reads into it.

Exact mode: gaps and runs are integers.  Abstract mode: they are capped at K (K+ = K or more), and a block's gaps
are a queue with a few explicit ends and a middle that is any path of a learned graph GQ of adjacent gaps; every
choice the abstraction allows is tried (`successors`).
"""
import sys, os, collections, copy, time, itertools

MACH = "1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---"
T = {}
for s_, part in enumerate(MACH.split('_')):
    for r in range(2):
        q = part[3 * r:3 * r + 3]
        T[(s_, r)] = None if q[2] == '-' else (int(q[0]), 1 if q[1] == 'R' else -1, ord(q[2]) - 65)
A_, B_, C_, D_, E_, F_ = range(6)

class Halt(Exception): pass
class TooLong(Exception): pass
class Infeasible(Exception): pass

CFG = {'K': 6, 'NE': 2, 'NF': 3, 'MAXMOVES': 20000, 'YMAX': 60}

# ---------------------------------------------------------------- capped integers and the oracle
class Big(int):
    def __new__(cls): return int.__new__(cls, CFG['K'])
    def __repr__(self): return 'K+'
    def __sub__(self, x):
        x = int(x); K = CFG['K']
        if x <= 0: return self
        opts = list(range(max(0, K - x), K)) + [BIG]
        return opts[ORA.choose(len(opts))]
    def __add__(self, x): return self if x >= 0 else self - (-x)
    __radd__ = __add__
    def __eq__(self, o): return isinstance(o, Big)
    def __ne__(self, o): return not isinstance(o, Big)
    def __hash__(self): return hash('BIG')
    def __deepcopy__(self, memo): return self
    def __copy__(self): return self
BIG = None

def norm(x):
    if isinstance(x, Big): return x
    return BIG if x >= CFG['K'] else x

def sub(g, k):
    """g - k for k >= 0"""
    return g - k if isinstance(g, Big) else g - k

class Oracle:
    def __init__(self): self.seq = []; self.pos = 0; self.fan = []
    def reset(self, seq): self.seq = list(seq); self.pos = 0; self.fan = []
    def choose(self, n):
        if n == 1: return 0
        i = self.seq[self.pos] if self.pos < len(self.seq) else 0
        self.fan.append(n); self.pos += 1
        return i
ORA = Oracle()

GQ = set(); PQ = set(); CHANGED = [False]
def addQ(p):
    if p not in GQ: PQ.add(p)
def commit():
    ch = False
    for p in PQ:
        if p not in GQ: GQ.add(p); ch = True
    PQ.clear()
    if ch: CHANGED[0] = True
    return ch
_RC = {}
def reach(a, b):
    ck = (len(GQ), a, b)
    if ck in _RC: return _RC[ck]
    seen = {a}; st = [a]; r = False
    while st:
        x = st.pop()
        if x == b: r = True; break
        for (u, v) in GQ:
            if u == x and v not in seen: seen.add(v); st.append(v)
    _RC[ck] = r; return r
def succ(a): return sorted({v for (u, v) in GQ if u == a}, key=repr)
def pred(a): return sorted({u for (u, v) in GQ if v == a}, key=repr)

# ---------------------------------------------------------------- a block's gaps: near end E, middle, far end F
class AQ:
    __slots__ = ('E', 'mid', 'F', 'S')
    def __init__(self, gaps=()):
        self.E = collections.deque(); self.mid = None; self.F = collections.deque(gaps)
        self.S = sum(int(g) for g in self.F)    # the sum of the explicit gaps (used in exact mode, for the cost)
    def key(self): return (tuple(self.E), self.mid, tuple(self.F))
    def __bool__(self): return bool(self.E) or self.mid is not None or bool(self.F)
    def exact(self): return self.mid is None
    def gaps(self):
        assert self.mid is None
        return list(self.E) + list(self.F)
    def refill(self):
        if self.E: return
        if self.mid is not None:
            t0, tl = self.mid; opts = []
            if t0 == tl: opts.append(None)
            for v in succ(t0):
                if reach(v, tl): opts.append((v, tl))
            if not opts: raise Infeasible()
            self.mid = opts[ORA.choose(len(opts))]
            self.E.append(t0); return
        if self.F: self.E.append(self.F.popleft())
    def first(self): self.refill(); return self.E[0]
    def add_first(self, k):
        self.refill(); g = self.E[0]
        self.E[0] = norm(g + k) if k >= 0 else sub(g, -k); self.S += int(self.E[0]) - int(g)
    def pop_first(self):
        self.refill(); x = self.E.popleft(); self.S -= int(x); return x
    def pop_last(self):
        if self.F: x = self.F.pop(); self.S -= int(x); return x
        if self.mid is not None:
            t0, tl = self.mid; opts = []
            if t0 == tl: opts.append(None)
            for u in pred(tl):
                if reach(t0, u): opts.append((t0, u))
            if not opts: raise Infeasible()
            self.mid = opts[ORA.choose(len(opts))]
            return tl
        x = self.E.pop(); self.S -= int(x); return x
    def append(self, g): self.F.append(norm(g)); self.S += int(self.F[-1])
    def prepend(self, g): self.E.appendleft(norm(g)); self.S += int(self.E[0])
    def lead_ones(self):
        """pop the leading gaps of one pair: returns (k, more) -- k popped exactly, and more = True when an
        unknown number (at least one) more were popped from the abstract middle"""
        k = 0; more = False
        while True:
            if self.E:
                if self.E[0] == 1: self.E.popleft(); k += 1; self.S -= 1; continue
                return k, more
            if self.mid is not None:
                t0, tl = self.mid
                if t0 != 1:
                    self.refill(); continue
                opts = [('v', v) for v in succ(1) if v != 1 and reach(v, tl)]
                if tl == 1: opts.append(('all', None))
                if not opts: raise Infeasible()
                o = opts[ORA.choose(len(opts))]
                more = True
                if o[0] == 'v': self.mid = None if False else (o[1], tl); continue
                self.mid = None; continue
            if self.F:
                if self.F[0] == 1: self.F.popleft(); k += 1; self.S -= 1; continue
                return k, more
            return k, more
    def fold(self):
        NE, NF = CFG['NE'], CFG['NF']
        while len(self.F) > NF:
            x = self.F.popleft()
            if self.mid is None:
                if len(self.E) < NE: self.E.append(x); continue
                addQ((self.E[-1], x)); self.mid = (x, x)
            else:
                addQ((self.mid[1], x)); self.mid = (self.mid[0], x)
        while len(self.E) > NE + 1:
            # move surplus near items into the middle (keeps keys small)
            x = self.E.pop()
            if self.mid is None:
                if self.F: addQ((x, self.F[0]))
                self.mid = (x, x)
            else:
                addQ((x, self.mid[0])); self.mid = (x, self.mid[1])
    def record(self):
        seq = list(self.E) + ([('MID',) + self.mid] if self.mid is not None else []) + list(self.F)
        for a, b in zip(seq, seq[1:]):
            addQ((a[2] if isinstance(a, tuple) else a, b[1] if isinstance(b, tuple) else b))
    def cost(self):
        assert self.mid is None
        return self.S, len(self.E) + len(self.F)

def concat(q1, q2):
    """q1 then q2 (near to far)"""
    if not q1: return q2
    if not q2: return q1
    if isinstance(q1, RQ): return rq_concat(q1, q2)
    if q1.mid is None and q2.mid is None:
        # in place, into the longer one
        if len(q1.E) + len(q1.F) >= len(q2.E) + len(q2.F):
            q1.F.extend(q2.E); q1.F.extend(q2.F); q1.S += q2.S; return q1
        q2.E.extendleft(reversed(q1.F)); q2.E.extendleft(reversed(q1.E)); q2.S += q1.S; return q2
    q1.record(); q2.record()
    sq = list(q1.E) + ([('MID',) + q1.mid] if q1.mid else []) + list(q1.F) + list(q2.E) + \
        ([('MID',) + q2.mid] if q2.mid else []) + list(q2.F)
    for a, b in zip(sq, sq[1:]):
        addQ((a[2] if isinstance(a, tuple) else a, b[1] if isinstance(b, tuple) else b))
    q = AQ(); q.E = collections.deque(q1.E); q.F = collections.deque(q2.F)
    midpart = sq[len(q1.E):len(sq) - len(q2.F)]
    if midpart:
        f = midpart[0]; l = midpart[-1]
        q.mid = (f[1] if isinstance(f, tuple) else f, l[2] if isinstance(l, tuple) else l)
    return q

class RQ:
    """a block's gaps in exact mode, coded as runs of patterns: R holds [pat, count] entries, the near end first, pat a
    tuple of one or two gaps repeated count times (`(3, 11), 5000` is `3 11 3 11 ...`).  A reservoir of a hundred
    thousand one-pair gaps, or a long `(105 377)^n` stretch, is one entry.  Neighbouring entries with the same
    pattern are merged, and gaps added at either end that repeat a pair `a b a b` are folded into a `(a, b)` entry."""
    __slots__ = ('R', 'S', 'n')
    mid = None
    def __init__(self, gaps=(), runs=None):
        self.R = collections.deque(); self.S = 0; self.n = 0
        if runs is not None:
            for v, c in runs: self.append(v, c)
        else:
            for g in gaps: self.append(g)
    def key(self): return tuple((e[0], e[1]) for e in self.R)
    def __bool__(self): return self.n > 0
    def exact(self): return True
    def size(self): return self.n
    def it(self):
        for pat, c in self.R:
            for _ in range(c): yield from pat
    def gaps(self): return list(self.it())
    def runs(self): return [(e[0], e[1]) for e in self.R]
    def first(self): return self.R[0][0][0]
    def _fold_front(self):
        R = self.R
        if len(R) >= 2 and R[0][0] == R[1][0]: c = R.popleft()[1]; R[0][1] += c; return
        if len(R) >= 3 and R[0][1] == 1 and R[1][1] == 1 and len(R[0][0]) == 1 and len(R[1][0]) == 1:
            ab = R[0][0] + R[1][0]
            if R[2][0] == ab: R.popleft(); R.popleft(); R[0][1] += 1; return
            if len(R) >= 4 and ab[0] != ab[1] and R[2][1] == 1 and R[3][1] == 1 and R[2][0] + R[3][0] == ab:
                for _ in range(4): R.popleft()
                R.appendleft([ab, 2])
    def _fold_back(self):
        R = self.R
        if len(R) >= 2 and R[-1][0] == R[-2][0]: c = R.pop()[1]; R[-1][1] += c; return
        if len(R) >= 3 and R[-1][1] == 1 and R[-2][1] == 1 and len(R[-1][0]) == 1 and len(R[-2][0]) == 1:
            ab = R[-2][0] + R[-1][0]
            if R[-3][0] == ab: R.pop(); R.pop(); R[-1][1] += 1; return
            if len(R) >= 4 and ab[0] != ab[1] and R[-3][1] == 1 and R[-4][1] == 1 and R[-4][0] + R[-3][0] == ab:
                for _ in range(4): R.pop()
                R.append([ab, 2])
    def push_entry(self, pat, c, front=False):
        """add c copies of the pattern at one end"""
        if c <= 0: return
        R = self.R
        if front:
            if R and R[0][0] == pat: R[0][1] += c
            else: R.appendleft([pat, c]); self._fold_front()
        else:
            if R and R[-1][0] == pat: R[-1][1] += c
            else: R.append([pat, c]); self._fold_back()
        self.S += sum(pat) * c; self.n += len(pat) * c
    def append(self, g, c=1): self.push_entry((g,), c)
    def prepend(self, g, c=1): self.push_entry((g,), c, True)
    def pop_first(self):
        R = self.R; e = R[0]; pat = e[0]; v = pat[0]
        e[1] -= 1
        if e[1] == 0: R.popleft()
        if len(pat) > 1: R.appendleft([pat[1:], 1])
        self.S -= v; self.n -= 1; return v
    def pop_last(self):
        R = self.R; e = R[-1]; pat = e[0]; v = pat[-1]
        e[1] -= 1
        if e[1] == 0: R.pop()
        if len(pat) > 1: R.append([pat[:-1], 1])
        self.S -= v; self.n -= 1; return v
    def add_first(self, k):
        v = self.pop_first(); self.prepend(v + k)
    def lead_ones(self):
        R = self.R; k = 0
        while R and R[0][0][0] == 1:
            if R[0][0] == (1,): c = R.popleft()[1]; k += c; self.S -= c; self.n -= c
            else: self.pop_first(); k += 1
        return k, False
    def fold(self): pass
    def record(self): pass
    def cost(self): return self.S, self.n

def rq_concat(q1, q2):
    """q1 then q2 (near to far), in place into the one with more entries"""
    if len(q1.R) >= len(q2.R):
        for pat, c in list(q2.R): q1.push_entry(pat, c)
        return q1
    for pat, c in reversed(list(q1.R)): q2.push_entry(pat, c, True)
    return q2

def newQ(gaps=(), runs=None):
    if CFG.get('exact'): return RQ(gaps, runs)
    return AQ(gaps if runs is None else [v for v, c in runs for _ in range(c)])

def qsize(q): return q.size() if isinstance(q, RQ) else len(q.E) + len(q.F)
def qit(q): return q.it() if isinstance(q, RQ) else qit(q)

# ---------------------------------------------------------------- stacks
def isM(t): return isinstance(t, tuple) and t[0] == 'M' and bool(t[1])

def push(st, c):
    t = st[-1]
    if c == 0:
        if t == 'B': return
        st.append('0'); return
    if t == '0':
        st.pop(); t = st[-1]
        if isinstance(t, int): st[-1] = norm(t + 1)
        elif isM(t): t[1].add_first(1)
        else: st.append(1)
        return
    st.append('1')

def push_gap(st, g):
    if g <= 0: return
    t = st[-1]
    if isinstance(t, int): st[-1] = norm(t + g)
    elif isM(t): t[1].add_first(g)
    else: st.append(norm(g))

def push_mover(st, g):
    for x in (0, 0, 1, 1, 0): push(st, x)
    push_gap(st, g)

STAT = collections.Counter()

def pop(st):
    while True:
        t = st[-1]
        if t == 'B': return 0
        if t == '0' or t == '1': st.pop(); return int(t)
        if isinstance(t, int):
            t2 = sub(t, 1)
            if t2 >= 1: st[-1] = t2
            else: st.pop()
            st.append('0'); return 1
        if t[0] == 'W': raise RuntimeError('pop W')
        q = t[1]
        if not q: st.pop(); continue
        g = q.pop_first()
        if not q: st.pop()
        STAT['open'] += 1
        push_mover(st, g)

def bounce(Y):
    """one run from the right end back to it; returns machine steps (exact mode)"""
    L = Y; R = ['B']; s = E_; steps = 0; moves = 0
    while True:
        if moves > 0 and s == E_ and len(R) == 1 and R[0] == 'B': return steps
        if moves > CFG['MAXMOVES']: raise TooLong()
        moves += 1
        rt = R[-1]
        if s == E_ and isinstance(rt, int):
            g = R.pop(); push_gap(L, g); steps += 2 * g; continue
        if s == E_ and (rt == '0' or rt == 'B') and isM(L[-1]):
            blk = L.pop()[1]
            if blk.exact(): G, m = blk.cost(); steps += 2 * G + 15 * m
            if rt == '0': R.pop()
            R.append(('W', blk)); R.append('0'); STAT['left_all'] += 1
            continue
        if isinstance(rt, tuple):          # a swept block
            blk = rt[1]
            if s not in (D_, F_):
                g = blk.pop_last()
                if not blk: R.pop()
                for x in reversed([0, 1, 0, 1, 1] + [0, 1] * g): push(R, x)
                STAT['W open %s' % 'ABCDEF'[s]] += 1
                continue
            R.pop()
            k, more = blk.lead_ones()
            if blk:
                if blk.exact(): G, m = blk.cost(); steps += 2 * G + 5 * m
                blk.add_first(-2)
                push(L, 1 if s == D_ else 0); push(L, 0); push(L, 1); L.append(('M', blk)); push(L, 0); s = D_
                STAT['right_gen'] += 1
            if k or more:
                for x in ((1 if s == D_ else 0), 0, 1, 0, 0, 1, 1): push(L, x)
                steps += 7 * k; s = F_; STAT['rm1'] += 1
                r = k - 1 if not more else k
                if r > 0 or more:
                    if not (L[-1] == '1' and L[-2] == 1 and L[-3] == '0'): raise RuntimeError('rm1 shape')
                    del L[-3:]
                    q = newQ(runs=[(1, r)])
                    if more:
                        q.E = collections.deque(q.F); q.F = collections.deque(); q.mid = (1, 1); addQ((1, 1))
                    L.append(('M', q)); L.append('0'); L.append(1); L.append('1')
            continue
        c = pop(R)
        tr = T[(s, c)]
        if tr is None: raise Halt()
        w, d, ns = tr; steps += 1; s = ns
        if d > 0:
            push(L, w)
        else:
            push(R, w)
            if s == C_ and isinstance(L[-1], int):
                g = L.pop(); push_gap(R, g); steps += 2 * g
            x = pop(L); push(R, x)

def collapse(Y):
    """cell-form movers into blocks; neighbouring blocks merged; pairs on top of a block merged into its gap"""
    out = [Y[0]]; i = 1
    while i < len(Y):
        t = Y[i]
        if isinstance(t, tuple) and not t[1]: i += 1; continue
        if i + 5 <= len(Y) and t == '0' and Y[i + 1] == 1 and not isinstance(Y[i + 1], Big) and Y[i + 2] == '1' \
                and Y[i + 3] == '0' and isinstance(Y[i + 4], int) and Y[i + 4] >= 1:
            g = Y[i + 4]
            if isM(out[-1]): out[-1][1].prepend(g)
            else: out.append(('M', newQ([g])))
            i += 5; continue
        if isinstance(t, tuple) and isM(out[-1]):
            out[-1] = ('M', concat(t[1], out[-1][1])); i += 1; continue
        if isinstance(t, int) and isM(out[-1]):
            out[-1][1].add_first(t); i += 1; continue
        out.append(t); i += 1
    Y[:] = out

def normalize(Y):
    collapse(Y)
    if CFG.get('exact'): return
    for t in Y:
        if isinstance(t, tuple): t[1].fold(); t[1].record()
    if len(Y) > CFG['YMAX']: raise RuntimeError('tape has %d items' % len(Y))

def key(Y): return tuple(('M', t[1].key()) if isinstance(t, tuple) else t for t in Y)

def show(Y):
    out = []
    for t in Y:
        if isinstance(t, tuple):
            q = t[1]
            out.append('M%s' % ('[%d]' % len(q.gaps()) if q.exact() else str(q.key())))
        else: out.append(repr(t))
    return ' '.join(out)

def to_cells(Y):
    out = []
    for t in Y[1:]:
        if isinstance(t, int): out.extend([0, 1] * t)
        elif isinstance(t, tuple):
            for g in reversed(t[1].gaps()): out.extend([0, 0, 1, 1, 0]); out.extend([0, 1] * g)
        else: out.append(int(t))
    return out

# ---------------------------------------------------------------- abstract search
def successors(Y0, runlimit):
    out = []; fails = []; stack = [[]]; runs = 0
    while stack:
        seq = stack.pop(); runs += 1
        if runs > runlimit: fails.append(('explode', seq[:30])); break
        Y = copy.deepcopy(Y0); ORA.reset(seq)
        try:
            bounce(Y); normalize(Y); res = ('ok', Y)
        except Infeasible: res = ('infeasible', None)
        except Halt: res = ('HALT', None)
        except TooLong: res = ('toolong', None)
        except RuntimeError as e: res = ('err: ' + str(e), None)
        fan = ORA.fan
        for i in range(len(seq), len(fan)):
            base = seq + [0] * (i - len(seq))
            for alt in range(1, fan[i]): stack.append(base + [alt])
        if res[0] == 'ok': out.append(res[1])
        elif res[0] != 'infeasible': fails.append((res[0], seq))
    commit()
    return out, fails

def abstract_of(Y):
    A = [Y[0]]
    for t in Y[1:]:
        if isinstance(t, tuple):
            q = AQ([norm(g) for g in t[1].gaps()]); A.append(('M', q))
        elif isinstance(t, int): A.append(norm(t))
        else: A.append(t)
    normalize(A); commit()
    return A


# ---------------------------------------------------------------- the transfer, accelerated (exact mode)
def _show_top(Y, k=12):
    o = []
    for t in Y[-k:]:
        if isinstance(t, tuple):
            g = t[1].gaps(); o.append('M[%s%s]' % (' '.join(map(str, g[:4])), ' ..%d' % len(g) if len(g) > 4 else ''))
        else: o.append(repr(t))
    return ' '.join(o)

def _transfer_shape(Y):
    """`... M[g ..] X n M[f ..]` at the top of the stack, X a single cell; returns (g, X, n, f) or None"""
    if len(Y) < 5: return None
    a, x, n, b = Y[-4], Y[-3], Y[-2], Y[-1]
    if not (isM(a) and isM(b) and x in ('0', '1') and type(n) is int and a[1].exact() and b[1].exact()): return None
    return a[1].first(), x, n, b[1].first()

def _drain(Y, margin, room=10**40):
    """the tape is `1 M[G ..]`, one block: each bounce takes one pair off G and puts one more one-pair mover at
    the block's far end, at 20 steps more than the bounce before.  Two bounces are run and checked against that,
    then p more applied at once."""
    q = Y[2][1]; G = q.first(); n = q.size()
    s0 = bounce(Y); normalize(Y); s1 = bounce(Y); normalize(Y)
    if not (len(Y) == 3 and Y[1] == '1' and isM(Y[2]) and Y[2][1].first() == G - 2 and Y[2][1].size() == n + 2
            and Y[2][1].R[-1][0] == (1,) and s1 == s0 + 20):
        return s0 + s1, 2
    q = Y[2][1]; p = min(G - 2 - 2 * margin, room - 2)
    if p <= 0: return s0 + s1, 2
    q.add_first(-p); q.append(1, p)          # the p new movers take their pairs from G
    STAT['drain'] += 1; STAT['drain bounces'] += p
    return s0 + s1 + p * s1 + 10 * p * (p + 1), 2 + p

def run_bounces(Y, accel=True, margin=6, room=10**40):
    """one bounce, or with accel a whole stretch of a transfer: while `... M[g ..] X n M[f ..]` holds, each bounce
    takes g-1, flips X, adds 3 to n and takes f-1.  Two bounces are run and checked against that; then 2p more
    are applied at once, their cost from s(t+2) = s(t) + 16.  Returns (steps, bounces)."""
    if accel and len(Y) == 3 and Y[1] == '1' and isM(Y[2]) and isinstance(Y[2][1], RQ) and Y[2][1].first() >= 4 * margin:
        return _drain(Y, margin, room)
    sh = _transfer_shape(Y) if accel else None
    if sh is None or min(sh[0], sh[3]) < margin + 4:
        return bounce(Y), 1
    g, x, n, f = sh
    s0 = bounce(Y); normalize(Y); s1 = bounce(Y); normalize(Y)
    want = (g - 2, x, n + 6, f - 2)
    if _transfer_shape(Y) != want:
        return s0 + s1, 2
    p = min((min(g, f) - 2 - margin) // 2, (room - 2) // 2)
    if p <= 0: return s0 + s1, 2
    Y[-4][1].add_first(-2 * p); Y[-2] = n + 6 + 6 * p; Y[-1][1].add_first(-2 * p)
    STAT['transfer'] += 1; STAT['transfer bounces'] += 2 * p
    return s0 + s1 + p * (s0 + s1) + 16 * p * (p + 1), 2 + 2 * p

# ---------------------------------------------------------------- repeating stretches of bounces, extrapolated
WIN = 3          # entries tracked at each end of a block

def _sig(Y):
    """the tape as a structure and a list of numbers: every run of pairs, and for each block its entries (all of
    them if few, else WIN at each end) as pattern values and counts"""
    st = []; nums = []
    for t in Y:
        if type(t) is int: st.append('n'); nums.append(t)
        elif isinstance(t, tuple):
            R = t[1].R
            ents = list(R) if len(R) <= 2 * WIN else list(itertools.islice(R, WIN)) + list(itertools.islice(R, len(R) - WIN, len(R)))
            st.append(('M', len(R) if len(R) <= 2 * WIN else -1) + tuple(len(e[0]) for e in ents))
            for e in ents: nums.extend(e[0]); nums.append(e[1])
        else: st.append(t)
    return tuple(st), nums

def _set_sig(Y, nums):
    it_ = iter(nums)
    for i, t in enumerate(Y):
        if type(t) is int: Y[i] = next(it_)
        elif isinstance(t, tuple):
            q = t[1]; R = q.R
            idx = list(range(len(R))) if len(R) <= 2 * WIN else list(range(WIN)) + list(range(len(R) - WIN, len(R)))
            for j in idx:
                e = R[j]; q.S -= sum(e[0]) * e[1]; q.n -= len(e[0]) * e[1]
                pat = tuple(next(it_) for _ in e[0]); c = next(it_)
                R[j] = [pat, c]; q.S += sum(pat) * c; q.n += len(pat) * c

class Periodic:
    """Watches the tape after each bounce.  When for some period P the structure is the same at four points P
    bounces apart, every tracked number changes by the same amount d over each period, and each bounce costs D
    steps more than the one P bounces before, m more periods are applied at once: the numbers move by m d and the
    cost is m Q + P D m (m + 1) / 2 (Q the last period's cost).  m keeps every decreasing number, and every
    difference of two numbers that is closing, at least three periods away from zero."""
    def __init__(self, pmax=12): self.h = collections.deque(maxlen=3 * pmax + 1); self.pmax = pmax
    def clear(self): self.h.clear()
    def step(self, Y, cost, room=10**40):
        st, nums = _sig(Y); h = self.h; h.append((st, nums, cost))
        n = len(h)
        for P in range(1, self.pmax + 1):
            if n < 3 * P + 1: break
            a, b_, c, d_ = h[-1], h[-1 - P], h[-1 - 2 * P], h[-1 - 3 * P]
            if not (a[0] == b_[0] == c[0] == d_[0]) or len(a[1]) != len(d_[1]): continue
            dl = [x - y for x, y in zip(a[1], b_[1])]
            if not any(dl): continue
            if dl != [x - y for x, y in zip(b_[1], c[1])] or dl != [x - y for x, y in zip(c[1], d_[1])]: continue
            D = a[2] - b_[2]
            if any(h[-1 - j][2] - h[-1 - j - P][2] != D for j in range(2 * P)): continue
            m = min(self._room(a[1], dl), room // P)
            if m < 1: return None
            _set_sig(Y, [x + m * dx for x, dx in zip(a[1], dl)])
            Q = sum(h[-1 - j][2] for j in range(P))
            self.clear()
            STAT['periodic'] += 1; STAT['periodic bounces'] += m * P
            return m * Q + P * D * m * (m + 1) // 2, m * P
        return None
    @staticmethod
    def _room(x, dl):
        m = 10 ** 30
        for i, (xi, di) in enumerate(zip(x, dl)):
            if di < 0: m = min(m, (xi - 1) // -di - 3)
        ch = [(xi, di) for xi, di in zip(x, dl) if di]
        for xi, di in ch:
            for xj, dj in zip(x, dl):
                dd = di - dj; gap = xi - xj
                if dd and gap and (gap > 0) != (dd > 0): m = min(m, (abs(gap) - 1) // abs(dd) - 3)
        return m

PER = Periodic()

def advance(Y, accel=True, room=10**40):
    """run_bounces, then with accel a repeating stretch of bounces extrapolated (exact mode)"""
    ds, db = run_bounces(Y, accel, room=room) if room >= 3 else (bounce(Y), 1)
    normalize(Y)
    if not accel or not CFG.get('periodic', True): return ds, db
    if db != 1: PER.clear(); return ds, db
    r = PER.step(Y, ds, room - 1)
    if r: ds += r[0]; db += r[1]; normalize(Y)
    return ds, db

# ---------------------------------------------------------------- command line
def _rle(g):
    out = []
    for x in g:
        if out and out[-1][0] == x: out[-1][1] += 1
        else: out.append([x, 1])
    return ' '.join('%d^%d' % (a, b) if b > 1 else str(a) for a, b in out)

def _rle_runs(runs):
    def one(pat, c):
        t = ' '.join(map(str, pat))
        if c == 1: return t
        return ('(%s)^%d' if len(pat) > 1 else '%s^%d') % (t, c)
    return ' '.join(one(p_, c) for p_, c in runs)

def _exact_start():
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import mover_sim as ms
    CFG.update(K=10**30, NF=10**12, NE=10**12, MAXMOVES=10**12, YMAX=10**9, exact=True,
               periodic=os.environ.get('PERIODIC', '1') == '1')
    S = ms.start(); assert S.gs.m == 0 and len(S.Z) == 1
    Y = list(S.Y); normalize(Y)
    return ms, Y, S.steps

def _ones(Y):
    """(leading gaps before the first one-pair gap, one-pair gaps after them) of the leftmost block"""
    import itertools
    b = next(t[1] for t in Y if isinstance(t, tuple))
    big = 0
    for j, x in enumerate(qit(b)):
        if x == 1 and j > 0: break
        big += 1
    return big, qsize(b) - big

def main():
    mode, nb = sys.argv[1], int(float(sys.argv[2]))
    ms, Y, steps = _exact_start()
    if mode == 'check':
        t0 = time.time(); mx = 0
        i = 0; accel = os.environ.get('ACCEL', '1') == '1'
        while i < nb:
            ds, db = advance(Y, accel); steps += ds; i += db; mx = max(mx, len(Y))
        print('bounces', i, 'step', steps, 'max items', mx, dict(STAT), '%.0fs' % (time.time() - t0))
        k, st, hp, hi, cells = ms.dump(steps)
        ok = ms.strip(to_cells(Y)) == ms.strip(cells[:-1]) and st == 'E' and hp == hi
        print('tape equal to direct simulation' if ok else 'TAPE DIFFERS')
        sys.exit(0 if ok else 1)
    if mode == 'cycle':
        # the reservoir (one-pair gaps of the leftmost block): each time it stops shrinking, and every bounce
        # at which the tape is one block, with its gaps
        prev = None; trend = 0; low = None; single = False
        for i in range(nb):
            steps += bounce(Y); normalize(Y)
            big, ones = _ones(Y)
            if prev is not None:
                if ones < prev: trend = -1; low = (i, steps, ones, show(Y))
                elif ones > prev and trend == -1:
                    print('reservoir low %d at bounce %d (step %d): %s' % (low[2], low[0], low[1], low[3][:200]))
                    trend = 1
            prev = ones
            one = len(Y) == 3 and isinstance(Y[2], tuple)
            if one and not single:
                s = _rle(Y[2][1].gaps())
                print('one block at bounce %d (step %d), %d movers: %s' % (i, steps, len(Y[2][1].gaps()),
                      s if len(s) < 400 else s[:200] + ' ... ' + s[-160:]))
            single = one
        print('end: bounce', nb, 'step', steps, 'leading', big, 'one-pair', ones)
    if mode == 'goto':
        # accelerated to exactly bounce N: the step count there, the movers and their pair sum
        i = 0; t0 = time.time()
        while i < nb:
            ds, db = advance(Y, True, nb - i); i += db; steps += ds
        qs = [t[1] for t in Y if isM(t)]
        print('bounce', i, 'step', steps, 'movers', sum(q.size() for q in qs), 'gap sum', sum(q.S for q in qs),
              'items', len(Y), '%.0fs' % (time.time() - t0))
    if mode == 'blocks':
        # accelerated: every bounce at which the tape is one block, with its gaps (run length coded)
        i = 0; single = False; t0 = tp = time.time(); PROG = float(os.environ.get('PROGRESS', '0'))
        while i < nb:
            ds, db = advance(Y); i += db; steps += ds
            if PROG and time.time() - tp > PROG:
                tp = time.time(); qs = [t[1] for t in Y if isM(t)]
                print('  at bounce %d (step %.3e): %d items, %d blocks, %d movers in %d runs' % (i, steps, len(Y),
                      len(qs), sum(q.size() for q in qs), sum(len(q.R) for q in qs)), flush=True)
            one = len(Y) == 3 and isM(Y[2])
            if one and not single:
                q = Y[2][1]; s_ = _rle_runs(q.runs())
                print('one block at bounce %d (step %d), %d movers: %s' % (i, steps, q.size(),
                      s_ if len(s_) < 400 else s_[:200] + ' ... ' + s_[-160:]), '%.0fs' % (time.time() - t0), flush=True)
            single = one
        print('end: bounce', i, 'step', steps, dict(STAT))
    if mode == 'rule':
        # The rebuild transducer.  A gap's transfer starts as `M[g ..] 0 n0 M[f ..]` with n0 = 4 (S1, g whole),
        # 3 (S0, one pair already taken) or 2 (S2, after a drain end).  With fuel f larger than the gap the new gap
        # joins the right block; with less, the fuel runs out after f bounces (run n0 + 3f), a drain follows, and
        # the transfer starts again: for even f in S2 with the gap 3 pairs shorter and fuel 2 (n0 + 3f) + 7, for odd
        # f in S0 with the gap 2 pairs shorter and fuel 2 (n0 + 3f) + 6.
        def pred(st, g0):
            if st == 1: return (3 * g0 + 4, 1) if g0 % 2 == 0 else (3 * g0 + 8, 0)
            if st == 0: return (3 * g0, 1) if g0 % 2 == 1 else (3 * g0 + 4, 0)
            return (3 * g0 + 2, 1) if g0 % 2 == 0 else (3 * g0 + 6, 0)
        i = 0; prev = None; res = collections.Counter(); bad = []; pend = []; single = False; spend = None
        while i < nb:
            ds, db = run_bounces(Y); normalize(Y); i += db; steps += ds
            one = len(Y) == 3 and isM(Y[2])
            if one and not single:
                # the bottom: one block [G, h, rest...]: G drains into the reservoir, h becomes the fuel, and rest
                # is copied: S1 with fuel 2h for odd h, S0 (rest one pair shorter) with fuel 2h + 3 for even h
                G, h, r0 = list(itertools.islice(qit(Y[2][1]), 3))
                spend = (1, r0, 2 * h) if h % 2 == 1 else (0, r0 - 1, 2 * h + 3)
            single = one
            if pend and isM(Y[-1]):
                top = list(qit(Y[-1][1]))
                for p_ in pend[:]:
                    want, at = p_
                    if any(top[j:j + len(want)] == want for j in range(len(top) - len(want) + 1)):
                        res['un-nesting, as predicted'] += 1; pend.remove(p_)
                    elif i - at > 3 * want[0] + 100:
                        bad.append((at, 'un-nesting predicted', want, 'not found')); pend.remove(p_)
            sh = _transfer_shape(Y)
            if not (sh and sh[1] == '0' and sh[2] in (2, 3, 4)): continue
            st = {4: 1, 3: 0, 2: 2}[sh[2]]; g0 = sh[0] + (1 if st == 0 else 0); f = sh[3]
            if spend is not None:
                if (st, sh[0], f) == spend: res['one block, as predicted'] += 1
                else: bad.append((i, 'one block predicted', spend, 'got', (st, sh[0], f)))
                spend = None
            Lb, R = Y[-4][1], Y[-1][1]
            ll, rl = qsize(Lb), qsize(R)
            if prev is not None:
                pst, pg0, pg, pf, pn, pll, prl, pi, pgaps, prgaps = prev
                k = pll - ll
                if pg < pf <= pg + 1: res['fuel ends with the gap (f = g + 1)'] += 1
                elif pf > sum(pgaps[:k]) + 1 and k >= 1 and rl == prl + k:
                    s_, outs = pst, []
                    for j in range(k):
                        h, s_ = pred(s_, pg0 if j == 0 else pgaps[j])
                        outs.append(h)
                    got = list(itertools.islice(qit(R), rl - k, rl))
                    key = 'gap copied, as predicted' if k == 1 else 'gaps copied, as predicted (%d at once)' % k
                    if (outs, s_) == (got, st): res[key] += 1
                    else: bad.append((pi, 'S%d' % pst, pgaps[:k], pf, 'predicted', (outs, s_), 'got', (got, st)))
                elif pf < pg and ll == pll and rl == 1:
                    ne = pn + 3 * pf
                    want = (2, pg - pf - 3, 2 * ne + 7) if pf % 2 == 0 else (0, pg - pf - 2, 2 * ne + 6)
                    if (st, sh[0], f) == want: res['drain end, as predicted'] += 1
                    else: bad.append((pi, 'S%d' % pst, pg0, pf, 'drain end predicted', want, 'got', (st, sh[0], f)))
                elif pf < pg and len(prgaps) >= 3:
                    # nesting: the run freezes, the fuel block's next gap h is the new fuel, the rest a new left block
                    h = prgaps[1]; ne = pn + 3 * pf
                    want = ['1' if pf % 2 == 0 else '0', ne + 3, pg - pf - 1]
                    if h % 2 == 1: want += [prgaps[2], 1, 2 * h]
                    else: want += [prgaps[2] - 1, 0, 2 * h + 3]
                    got = [Y[-6], Y[-5], Y[-7][1].first() if isM(Y[-7]) else None, sh[0], st, f] if len(Y) >= 7 else None
                    if got == want: res['nesting, as predicted'] += 1
                    else: bad.append((pi, 'S%d' % pst, pg, pf, prgaps[:3], 'nesting predicted', want, 'got', got))
                else:
                    res['not checked (another level)'] += 1
                    if os.environ.get('SHOW'): print('unchecked at bounce', i, '\n   before:', pshow, '\n   now:   ', _show_top(Y))
            pshow = _show_top(Y) if os.environ.get('SHOW') else None
            if ll == 1 and len(Y) >= 7 and type(Y[-5]) is int and Y[-6] in ('0', '1') and isM(Y[-7]) and f > sh[0] + 1:
                # un-nesting: the inner level's last gap; then its frozen run r is copied like a gap and either
                # merges into the first gap of the block on its left or joins the right block as a gap of its own
                h, s_ = pred(st, g0); r = Y[-5]
                mid = list(itertools.islice(qit(Y[-7][1]), 3))
                if (r % 2 == 1) if s_ == 1 else (r % 2 == 0):
                    want = [h, mid[0] + 3 * r + (5 if s_ == 1 else 1) + (2 if Y[-6] == '1' else 0)] + mid[1:]
                else: want = [h, 3 * r + (4 if s_ == 1 else 0)]
                pend.append((want, i))
            prev = (st, g0, sh[0], f, sh[2], ll, rl, i, list(itertools.islice(qit(Lb), 8)),
                    list(itertools.islice(qit(R), 3)))
        print(dict(res))
        for b_ in bad: print('  differs at bounce', *b_)

if __name__ == '__main__':
    main()
