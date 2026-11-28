"""An abstract, mover-level closure search: an attempt that does not close yet.

    python3 holdouts/<M>/py/mover_cps.py [START]      (START = step of the exact run to start from, default 3e9)

The idea: an invariant in terms of movers, found by running `mover_sim.py`'s bounce on an abstract state until the
set of states is closed.  The state is mover_sim's  Y | gs  at a right-end turn, with
  * every run of pairs capped: 0..K-1 exact, K+ = "K or more" (taking a pair off K+ branches);
  * the movers the head crosses (`gs`), and every block of movers at rest in Y, as a queue: a few explicit gaps at
    each end and a middle that is any path in a global graph GQ of adjacent gaps;
  * Y's top DY items explicit, below them a static stack that is any path in a global graph GY of adjacent items
    down to the left end;
  * a block of movers at rest crossed by the head in E on a 0 is crossed in one step (`left_all`), and crossed back
    in D or F in one step (`right_gen`, when its rightmost gap is at least two pairs).
One bounce is mover_sim's (single bounces, no jumps), with an oracle that tries every choice the abstraction allows.

Result (23 November 2026): it fails.  From step 4.2e9 (3e9 asked) the search soon reaches a state whose top items are
few (`0 1 1 0 4` over the static stack) and the run into the stack does not end: the head crosses the movers of a
block one cell at a time (not in E on a 0, so `left_all` does not apply), and the abstract block can be as long as it
likes.  The abstraction has lost how far the next turning point is; the same failure as the tape-level CPS
(`c/runcps.cpp`).  A working version needs the static part as mover-level items whose crossings are lemmas in every
state the head can arrive in, not only E on a 0.
"""
import sys, os, collections, copy, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mover_sim as ms
from mover_sim import T, A_, B_, C_, D_, E_, F_, Halt, Boundary, MacroPoint

K = 6; DY = 12; NF = 3

class Big(int):
    def __new__(cls): return int.__new__(cls, K)
    def __repr__(self): return 'K+'
    def __sub__(self, x):
        x = int(x)
        if x <= 0: return self
        opts = list(range(max(0, K - x), K)) + [BIG]
        return opts[ORA.choose(len(opts))]
    def __add__(self, x): return self if x >= 0 else self - (-x)
    __radd__ = __add__
    def __eq__(self, o): return isinstance(o, Big)
    def __ne__(self, o): return not isinstance(o, Big)
    def __hash__(self): return hash('BIG')
    def __reduce__(self): return (Big, ())
    def __deepcopy__(self, memo): return self
    def __copy__(self): return self
BIG = None

def norm(x):
    if isinstance(x, Big): return x
    return BIG if x >= K else x

class Oracle:
    def __init__(self): self.seq = []; self.pos = 0; self.fan = []
    def reset(self, seq): self.seq = list(seq); self.pos = 0; self.fan = []
    def choose(self, n):
        if n == 1: return 0
        i = self.seq[self.pos] if self.pos < len(self.seq) else 0
        self.fan.append(n); self.pos += 1
        return i
ORA = Oracle()

GY = set()          # (upper token, lower token) in Y
GQ = set()          # (near, far) adjacent gaps in a mover queue
CHANGED = [False]
PY = set(); PQ = set()
def addY(p):
    if p not in GY: PY.add(p)
def addQ(p):
    if p not in GQ: PQ.add(p)
def commit():
    ch = False
    for p in PY:
        if p not in GY: GY.add(p); ch = True
    for p in PQ:
        if p not in GQ: GQ.add(p); ch = True
    PY.clear(); PQ.clear()
    if ch: CHANGED[0] = True
    return ch

RC = {}
def reach(G, a, b):
    """is there a path a -> ... -> b in G (length >= 0)?"""
    ck = (id(G), len(G), a, b)
    if ck in RC: return RC[ck]
    r = _reach(G, a, b); RC[ck] = r; return r
def _reach(G, a, b):
    seen = {a}; st = [a]
    while st:
        x = st.pop()
        if x == b: return True
        for (u, v) in G:
            if u == x and v not in seen: seen.add(v); st.append(v)
    return False

def succ(G, a): return sorted({v for (u, v) in G if u == a}, key=repr)

# ---------------------------------------------------------------- abstract queue of gaps
class AQ:
    def __init__(self): self.E = collections.deque(); self.mid = None; self.F = collections.deque()
    def key(self): return (tuple(self.E), self.mid, tuple(self.F))
    def __bool__(self): return bool(self.E) or self.mid is not None or bool(self.F)
    @property
    def m(self): return 1
    @property
    def G(self): return 0
    def refill(self):
        if self.E: return
        if self.mid is not None:
            t0, tl = self.mid
            opts = []
            if t0 == tl: opts.append(None)
            for v in succ(GQ, t0):
                if reach(GQ, v, tl): opts.append((v, tl))
            if not opts: raise RuntimeError('dead queue %r' % (self.mid,))
            self.mid = opts[ORA.choose(len(opts))]
            self.E.append(t0); return
        if self.F: self.E.append(self.F.popleft())
    def first(self): self.refill(); return self.E[0]
    def add_first(self, k):
        self.refill(); g = self.E[0]
        self.E[0] = norm(g + k) if k >= 0 else (g - (-k) if isinstance(g, Big) else g + k)
        assert not (self.E[0] < 0)
    def pop_first(self): self.refill(); return self.E.popleft()
    def append(self, g):
        g = norm(g)
        if not self and False: pass
        self.F.append(g)
        self.fold()
    def fold(self):
        while len(self.F) > NF:
            x = self.F.popleft()
            if self.mid is None:
                if self.E: addQ((self.E[-1], x))
                self.mid = (x, x)
            else:
                addQ((self.mid[1], x)); self.mid = (self.mid[0], x)
    def firsttok(self):
        if self.E: return self.E[0]
        if self.mid is not None: return self.mid[0]
        return self.F[0]
    def lasttok(self):
        if self.F: return self.F[-1]
        if self.mid is not None: return self.mid[1]
        return self.E[-1]
    def record(self):
        seq = list(self.E)
        prev = seq[-1] if seq else None
        for a, b in zip(seq, seq[1:]): addQ((a, b))
        if self.mid is not None:
            if prev is not None: addQ((prev, self.mid[0]))
            prev = self.mid[1]
        for x in self.F:
            if prev is not None: addQ((prev, x))
            prev = x
    def gaps(self): raise RuntimeError('gaps() on abstract queue')

def segs(q):
    out = list(q.E)
    if q.mid is not None: out.append(('MID',) + tuple(q.mid))
    out += list(q.F); return out

def ftok(x): return x[1] if isinstance(x, tuple) else x
def ltok(x): return x[2] if isinstance(x, tuple) else x

def concat(q1, q2):
    """q1 then q2 (near to far)."""
    if not q1: return q2
    if not q2: return q1
    sq = segs(q1) + segs(q2)
    for a, b in zip(sq, sq[1:]): addQ((ltok(a), ftok(b)))
    q = AQ(); q.E = collections.deque(q1.E); q.F = collections.deque(q2.F)
    mid = sq[len(q1.E):len(sq) - len(q2.F)]
    if mid: q.mid = (ftok(mid[0]), ltok(mid[-1]))
    return q

def collapse(Y, keep):
    """turn the cell form of movers ('0', 1, '1', '0', g with g >= 1) below the top `keep` items into blocks"""
    out = [Y[0]]; i = 1; n = len(Y) - keep
    while i < len(Y):
        if isinstance(Y[i], tuple) and not Y[i][1]: i += 1; continue
        if i + 5 <= n and Y[i] == '0' and Y[i + 1] == 1 and not isinstance(Y[i + 1], Big) and Y[i + 2] == '1' \
                and Y[i + 3] == '0' and isinstance(Y[i + 4], int) and Y[i + 4] >= 1:
            q = AQ(); q.E.append(Y[i + 4])
            if isinstance(out[-1], tuple) and out[-1][0] == 'M':
                out[-1] = ('M', concat(q, out[-1][1]))
            else: out.append(('M', q))
            i += 5; continue
        if isinstance(Y[i], tuple) and isinstance(out[-1], tuple) and out[-1][0] == 'M':
            out[-1] = ('M', concat(Y[i][1], out[-1][1])); i += 1; continue
        out.append(Y[i]); i += 1
    Y[:] = out

def aq_from(a, b):
    q = AQ(); q.mid = (a, b); return q

# ---------------------------------------------------------------- Y deep part
class Deep:
    __slots__ = ('t',)
    def __init__(self, t): self.t = t
    def __eq__(self, o): return isinstance(o, Deep) and o.t == self.t
    def __hash__(self): return hash(('Deep', self.t))
    def __repr__(self): return 'Deep(%r)' % (self.t,)

def tok(x):
    if isinstance(x, tuple): return ('M', x[1].firsttok(), x[1].lasttok())
    if isinstance(x, int): return norm(x)
    return x

def item(t):
    if isinstance(t, tuple): return ('M', aq_from(t[1], t[2]))
    return t

def reveal(st):
    """st[0] is Deep(t): make t explicit."""
    d = st[0]; t = d.t
    opts = []
    if (t, 'B') in GY: opts.append('B')
    for v in succ(GY, t):
        if v != 'B' and reach(GY, v, 'B'): opts.append(Deep(v))
    if not opts: raise RuntimeError('dead Y %r' % (t,))
    st[0] = opts[ORA.choose(len(opts))]
    st.insert(1, item(t))

def ensure(st, n):
    while len(st) <= n and isinstance(st[0], Deep): reveal(st)

def foldY(st):
    while len(st) > DY + 1:
        x = st.pop(1); t = tok(x)
        if isinstance(x, tuple): x[1].record()
        b = st[0]
        addY((t, b.t if isinstance(b, Deep) else b))
        st[0] = Deep(t)

# ---------------------------------------------------------------- stack primitives (mover_sim's, abstracted)
def top(st):
    if len(st) == 1 and isinstance(st[0], Deep): reveal(st)
    return st[-1]

def push(st, c):
    t = top(st)
    if c == 0:
        if t == 'B': return
        st.append('0'); return
    if t == '0':
        st.pop(); t = top(st)
        if isinstance(t, int): st[-1] = norm(t + 1)
        else: st.append(1)
        return
    st.append('1')

def push_gap(st, g):
    if g <= 0: return
    t = top(st)
    if isinstance(t, int): st[-1] = norm(t + g)
    else: st.append(norm(g))

def push_mover(st, g):
    for x in (0, 0, 1, 1, 0): push(st, x)
    push_gap(st, g)

def pop(st):
    while True:
        t = top(st)
        if t == 'B': return 0
        if t == 'X': raise Boundary()
        if t == '0' or t == '1': st.pop(); return int(t)
        if isinstance(t, int):
            t2 = t - 1
            if t2 >= 1: st[-1] = t2
            else: st.pop()
            st.append('0'); return 1
        if t[0] == 'W': raise RuntimeError('pop W')
        mv = t[1]
        if not mv: st.pop(); continue
        g = mv.pop_first(); push_mover(st, g)

MAXMOVES = 4000
STAT = collections.Counter()
TOPKEEP = 6
RUNLIMIT = 3000
class TooLong(Exception): pass

def run_local(L, R, s, maxmoves, stop_rightend=False, macro=False, pending=False):
    steps = 0; moves = 0
    if pending:
        x = pop(L); push(R, x)
    while True:
        if stop_rightend and moves > 0 and s == E_ and len(R) == 1 and R[0] == 'B': return steps, s
        if moves > MAXMOVES: raise TooLong()
        moves += 1
        if top(R) == 'X': return steps, s
        if s == E_ and isinstance(R[-1], int):
            g = R.pop(); push_gap(L, g); continue
        if macro and top(L) == 'X' and s == E_ and (top(R) == '0' or R[-1] == 'B'):
            raise MacroPoint(steps)
        if s == E_ and (R[-1] == '0' or R[-1] == 'B') and isinstance(top(L), tuple) and L[-1][0] == 'M':
            blk = L.pop()[1]
            if R[-1] == '0': R.pop()
            R.append(('W', blk)); R.append('0'); STAT['left_all'] += 1
            continue
        if isinstance(R[-1], tuple) and R[-1][0] == 'W':
            if s not in (D_, F_): raise RuntimeError('W in state %d' % s)
            blk = R[-1][1]
            if not (blk.first() >= 2): raise RuntimeError('W with rightmost gap %r' % (blk.first(),))
            R.pop(); blk.add_first(-2)
            push(L, 1 if s == D_ else 0); push(L, 0); push(L, 1); L.append(('M', blk)); push(L, 0); s = D_
            STAT['right_gen'] += 1
            continue
        c = pop(R)
        tr = T[(s, c)]
        if tr is None: raise Halt((list(L[-12:]), list(R[-12:])))
        w, d, ns = tr; s = ns
        if d > 0:
            push(L, w)
        else:
            push(R, w)
            if s == C_ and isinstance(top(L), int):
                g = L.pop(); push_gap(R, g)
            if top(L) == 'X': raise Boundary(steps, s)
            x = pop(L); push(R, x)

def absorb(Y, gs):
    while True:
        ensure(Y, 6)
        if len(Y) >= 6 and isinstance(Y[-1], int) and Y[-1] >= (1 if gs else 2) and Y[-2] == '0' and Y[-3] == '1' \
                and Y[-4] == 1 and Y[-5] == '0':
            g = Y[-1]; del Y[-5:]; gs.append(g)
        else: return

def walk_form(S):
    ensure(S, 4)
    return len(S) >= 4 and isinstance(S[-1], int) and S[-2] in ('0', '1') and isinstance(S[-3], int)

def do_jump1(S, mov):
    A = S[-1]; q = int(S[-2]); C = S[-3]
    S[-1] = norm(A + (3 if mov else 2)); S[-2] = str(q ^ 1)
    C2 = C - 1
    if C2 == 0:
        del S[-3]
        ensure(S, 3)
        if S[-2] == '1' and S[-3] == '0':
            a = S.pop(); S.pop(); S.pop(); push_gap(S, 1); push_gap(S, a)
    else: S[-3] = C2

# ---------------------------------------------------------------- the abstract Sim
class ASim:
    def __init__(self): self.Y = ['B']; self.gs = AQ(); self.Z = ['X']; self.swapped = False
    def merge_Z(self):
        items = self.Z[1:]
        for it in items:
            if isinstance(it, int): push_gap(self.Y, it)
            else: push(self.Y, int(it))
        self.Z = ['X']
    def macro(self):
        R = ['X', '0']
        st, s = run_local(self.Y, R, E_, 0)
        if s not in (D_, F_): raise RuntimeError('exit state %d' % s)
        for c in ((1, 0, 1) if s == D_ else (0, 0, 1)): push(self.Y, c)
    def bounce(self):
        if self.swapped:
            self.Y[:] = self.Z[:]; self.Z[:] = ['X']; self.swapped = False
        Y, gs, Z = self.Y, self.gs, self.Z
        if len(Z) == 1:
            absorb(Y, gs)
            if gs and gs.first() < 2:
                g = gs.pop_first(); push_mover(Z, g)
                if not gs: self.merge_Z()
                return self.bounce()
            if walk_form(Y):
                mov = bool(gs)
                if not mov or gs.first() - 1 >= 1:
                    do_jump1(Y, mov)
                    if mov: gs.add_first(-1)
                    return 'jump'
            if gs:
                self.macro(); gs.add_first(-1); return 'macro'
            R = ['B']
            run_local(Y, R, E_, 0, stop_rightend=True)
            # R is the whole right part now: in mover_sim R is just the blank afterwards
            return 'plain'
        if walk_form(Z) and isinstance(Z[-3], int):
            raise RuntimeError('zjump not abstracted')
        R = ['B']; touched = False; s0 = E_; pend = False
        while True:
            try:
                st, s = run_local(Z, R, s0, 0, stop_rightend=True, macro=True, pending=pend)
                break
            except MacroPoint:
                touched = True
                if gs.first() < 2:
                    self.unfold_into_Z(); s0 = E_; pend = False
                    continue
                pop(R)
                self.macro()
                gs.add_first(-2); push(Z, 0); s0 = D_; pend = False
            except Boundary as e:
                st, s = e.args; touched = True
                self.unfold_into_Z(); s0 = s; pend = True
        self.after_z(birth=not touched)
        return 'z'
    def unfold_into_Z(self):
        gs, Z = self.gs, self.Z
        if not gs: raise RuntimeError('no movers left to unfold')
        g = gs.pop_first()
        Zc = ['X']; push_mover(Zc, g)
        for it in Z[1:]:
            if isinstance(it, int): push_gap(Zc, it)
            else: push(Zc, int(it))
        Z[:] = Zc
        if not gs: self.merge_Z_live()
    def merge_Z_live(self):
        Y, Z = self.Y, self.Z
        items = Z[1:]
        Z[:] = Y[:]
        for it in items:
            if isinstance(it, int): push_gap(Z, it)
            else: push(Z, int(it))
        Y[:] = ['B']; self.swapped = True
    def after_z(self, birth):
        Y, gs, Z = self.Y, self.gs, self.Z
        if self.swapped:
            self.Y[:] = self.Z[:]; self.Z[:] = ['X']; self.swapped = False; return
        if len(Z) > 1 and isinstance(Z[1], int) and gs:
            gs.add_first(Z[1]); del Z[1]
        if birth and walk_form(Z):
            Y.append(('M', self.gs)); self.gs = AQ(); self.merge_Z()

    # canonical form between bounces
    def normalize(self):
        assert len(self.Z) == 1 and not self.swapped, (self.Z, self.swapped)
        collapse(self.Y, TOPKEEP); foldY(self.Y); self.gs.fold(); self.gs.record()
        for x in self.Y[1:]:
            if isinstance(x, tuple): x[1].fold(); x[1].record()
    def key(self):
        ys = tuple(('M', x[1].key()) if isinstance(x, tuple) else x for x in self.Y)
        return (ys, self.gs.key())

def from_concrete(S):
    A = ASim()
    def conv_q(mv):
        q = AQ()
        for i, g in enumerate(mv.gaps()):
            if i < 3: q.E.append(norm(g))
            else: q.F.append(norm(g)); q.fold()
        return q
    Y = ['B']
    for t in S.Y[1:]:
        if isinstance(t, tuple): Y.append(('M', conv_q(t[1])))
        elif isinstance(t, int): Y.append(norm(t))
        else: Y.append(t)
    collapse(Y, TOPKEEP); foldY(Y)
    A.Y = Y; A.gs = conv_q(S.gs); A.normalize(); commit()
    return A

def successors(st):
    """all abstract successors of one bounce. Returns (list of (kind, ASim), list of failures)."""
    out = []; fails = []
    stack = [[]]
    runs = 0
    while stack:
        seq = stack.pop(); runs += 1
        if runs > RUNLIMIT: fails.append(('explode', len(stack), seq[:40])); break
        A = copy.deepcopy(st)
        ORA.reset(seq)
        try:
            kind = A.bounce()
            A.normalize()
            res = ('ok', kind, A)
        except Halt as e:
            res = ('halt', e.args, None)
        except TooLong:
            res = ('toolong', None, None)
        except RuntimeError as e:
            res = ('err', str(e), None)
        except Exception as e:
            import traceback
            res = ('crash', traceback.format_exc()[-800:], None)
        # enumerate siblings: for each branch point past the forced prefix, push alternatives
        fan = ORA.fan
        for i in range(len(seq), len(fan)):
            base = (seq + [0] * (i - len(seq)))[:i] if i >= len(seq) else seq[:i]
            for alt in range(1, fan[i]):
                stack.append(base + [alt])
        if res[0] == 'ok': out.append((res[1], res[2]))
        else: fails.append((res[0], res[1], seq))
    commit()
    return out, fails

def main():
    global BIG
    BIG = Big()
    S = ms.start()
    tgt = float(sys.argv[1]) if len(sys.argv) > 1 else 3e9
    while S.steps < tgt: S.bounce()
    print('start at step', S.steps, flush=True)
    A = from_concrete(S)
    seen = {A.key(): A}; par = {A.key(): None}; t0 = time.time(); rnd = 0
    while True:
        rnd += 1; CHANGED[0] = False
        q = collections.deque(seen.values()); n = 0; new = 0
        while q:
            st = q.popleft(); n += 1
            outs, fails = successors(st)
            if fails:
                print('FAIL', str(fails[:1])[:300]); kk = st.key(); i = 0
                while kk is not None and i < 25:
                    print('  ', kk); p = par[kk]
                    if p is None: break
                    print('     <-', p[1]); kk = p[0]; i += 1
                return 1
            for kind, B in outs:
                kk = B.key()
                if kk not in seen: seen[kk] = B; par[kk] = (st.key(), kind); q.append(B); new += 1
            if n % 2000 == 0:
                print(rnd, n, 'states', len(seen), 'GY', len(GY), 'GQ', len(GQ), '%.0fs' % (time.time() - t0), flush=True)
        print('round', rnd, 'states', len(seen), 'new', new, 'graphs changed', CHANGED[0], flush=True)
        if not CHANGED[0] and new == 0: break
    print('CLOSED', len(seen), 'states')
    return 0

if __name__ == '__main__':
    sys.exit(main())
