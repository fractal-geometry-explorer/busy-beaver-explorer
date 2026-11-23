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
import sys, os, collections, copy, time

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
    __slots__ = ('E', 'mid', 'F')
    def __init__(self, gaps=()):
        self.E = collections.deque(); self.mid = None; self.F = collections.deque(gaps)
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
        self.E[0] = norm(g + k) if k >= 0 else sub(g, -k)
    def pop_first(self): self.refill(); return self.E.popleft()
    def pop_last(self):
        if self.F: return self.F.pop()
        if self.mid is not None:
            t0, tl = self.mid; opts = []
            if t0 == tl: opts.append(None)
            for u in pred(tl):
                if reach(t0, u): opts.append((t0, u))
            if not opts: raise Infeasible()
            self.mid = opts[ORA.choose(len(opts))]
            return tl
        return self.E.pop()
    def append(self, g): self.F.append(norm(g))
    def prepend(self, g): self.E.appendleft(norm(g))
    def lead_ones(self):
        """pop the leading gaps of one pair: returns (k, more) -- k popped exactly, and more = True when an
        unknown number (at least one) more were popped from the abstract middle"""
        k = 0; more = False
        while True:
            if self.E:
                if self.E[0] == 1: self.E.popleft(); k += 1; continue
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
                if self.F[0] == 1: self.F.popleft(); k += 1; continue
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
        g = self.gaps(); return sum(g), len(g)

def concat(q1, q2):
    """q1 then q2 (near to far)"""
    if not q1: return q2
    if not q2: return q1
    if q1.mid is None and q2.mid is None:
        q = AQ(); q.E = collections.deque(q1.E); q.F = collections.deque(list(q1.F) + list(q2.E) + list(q2.F)); return q
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
                    q = AQ([1] * r)
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
            else: out.append(('M', AQ([g])))
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
def _transfer_shape(Y):
    """`... M[g ..] X n M[f ..]` at the top of the stack, X a single cell; returns (g, X, n, f) or None"""
    if len(Y) < 5: return None
    a, x, n, b = Y[-4], Y[-3], Y[-2], Y[-1]
    if not (isM(a) and isM(b) and x in ('0', '1') and type(n) is int and a[1].exact() and b[1].exact()): return None
    return a[1].first(), x, n, b[1].first()

def run_bounces(Y, accel=True, margin=6):
    """one bounce, or with accel a whole stretch of a transfer: while `... M[g ..] X n M[f ..]` holds, each bounce
    takes g-1, flips X, adds 3 to n and takes f-1.  Two bounces are run and checked against that; then 2p more
    are applied at once, their cost from s(t+2) = s(t) + 16.  Returns (steps, bounces)."""
    sh = _transfer_shape(Y) if accel else None
    if sh is None or min(sh[0], sh[3]) < margin + 4:
        return bounce(Y), 1
    g, x, n, f = sh
    s0 = bounce(Y); normalize(Y); s1 = bounce(Y); normalize(Y)
    want = (g - 2, x, n + 6, f - 2)
    if _transfer_shape(Y) != want:
        return s0 + s1, 2
    p = (min(g, f) - 2 - margin) // 2
    if p <= 0: return s0 + s1, 2
    Y[-4][1].add_first(-2 * p); Y[-2] = n + 6 + 6 * p; Y[-1][1].add_first(-2 * p)
    STAT['transfer'] += 1; STAT['transfer bounces'] += 2 * p
    return s0 + s1 + p * (s0 + s1) + 16 * p * (p + 1), 2 + 2 * p

# ---------------------------------------------------------------- command line
def _rle(g):
    out = []
    for x in g:
        if out and out[-1][0] == x: out[-1][1] += 1
        else: out.append([x, 1])
    return ' '.join('%d^%d' % (a, b) if b > 1 else str(a) for a, b in out)

def _exact_start():
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import mover_sim as ms
    CFG.update(K=10**30, NF=10**12, NE=10**12, MAXMOVES=10**12, YMAX=10**9, exact=True)
    S = ms.start(); assert S.gs.m == 0 and len(S.Z) == 1
    Y = list(S.Y); normalize(Y)
    return ms, Y, S.steps

def _ones(Y):
    """(leading gaps before the first one-pair gap, one-pair gaps after them) of the leftmost block"""
    import itertools
    b = next(t[1] for t in Y if isinstance(t, tuple))
    big = 0
    for j, x in enumerate(itertools.chain(b.E, b.F)):
        if x == 1 and j > 0: break
        big += 1
    return big, len(b.E) + len(b.F) - big

def main():
    mode, nb = sys.argv[1], int(float(sys.argv[2]))
    ms, Y, steps = _exact_start()
    if mode == 'check':
        t0 = time.time(); mx = 0
        i = 0; accel = os.environ.get('ACCEL', '1') == '1'
        while i < nb:
            ds, db = run_bounces(Y, accel); normalize(Y); steps += ds; i += db; mx = max(mx, len(Y))
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

if __name__ == '__main__':
    main()
