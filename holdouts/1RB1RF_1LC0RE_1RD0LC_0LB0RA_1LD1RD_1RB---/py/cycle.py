"""Round skipping over the two-round cycle of the front (16 November 2026).

skip.py (the round-skipping simulator) leaves the old groups alone but still runs the front, the young groups next
to the front block, one round at a time.  Between events the front is a two-round cycle (with q the depth, i.e. the
number of groups to the right, lifetimes n / 3^q at the start of a round):

    [1.00, 0.00, X, Y, ...]  ->  [1.00, X + 8, Y - 1, ...]  ->  [1.00, 0.00, X + 7, Y - 2, ...]

(the newest group lasts one round, the one before it runs out, and the group after it merges into the newest one).
This file follows exactly the same round as skip.py (`Fast.round` is a transcription of `Sim.step`; the old
groups are kept as (value at round R0, R0)), and in addition skips K cycles at once:

  * after two exact rounds S0 -> S2 with the same number of groups and the same n0, put D = S2 - S0 (front
    values only) and run the two rounds once more, *symbolically*, on S0 + j*D with j an unknown in [0, K-1]:
    every number is a + b*j (class Lin); every comparison has to come out the same at j = 0 and j = K-1 (then it is
    the same for every j in between, since both sides are affine in j; an equality test also checks for a root in
    between), every floor division or remainder by c needs c | b (then it is affine as well).  If the run goes
    through and returns S0 + (j+1)*D for every j, the K cycles are applied at once: S0 + K*D.
  * the old groups must not come near running out in the skipped rounds (checked on the heap of due rounds), and
    the last group must stay >= 3; then they do not enter the computation of the round at all (skip.py).

So a skip is exactly K * (two rounds of skip.py), not a guess; anything the symbolic run cannot decide is done by
exact rounds.  A halt can only be reported by the exact model (model.py, through `slow`).

    python3 py/cycle.py test ROUNDS [START.pkl]               # every round start this simulator lands on, against skip.py
    python3 py/cycle.py run ROUNDS SECONDS [START.pkl] [CKPT_PREFIX]
"""
import heapq
import math
import os
import pickle
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model import START, bounce_lean, jump
from skip import BIG, pow3, rate, normal, first_normal
from charge import charges


class Undecided(Exception):
    pass


class Lin:
    """a + b*j + c*e for unknowns j in [0, Lin.J] and e in [0, Lin.E] (integers)."""
    J = 0
    E = 0
    __slots__ = ('a', 'b', 'c')

    def __init__(self, a, b=0, c=0):
        self.a, self.b, self.c = a, b, c

    @staticmethod
    def of(x):
        return x if isinstance(x, Lin) else Lin(x)

    def __add__(self, o):
        o = Lin.of(o)
        return Lin(self.a + o.a, self.b + o.b, self.c + o.c)
    __radd__ = __add__

    def __sub__(self, o):
        o = Lin.of(o)
        return Lin(self.a - o.a, self.b - o.b, self.c - o.c)

    def __rsub__(self, o):
        return Lin.of(o) - self

    def __neg__(self):
        return Lin(-self.a, -self.b, -self.c)

    def __mul__(self, k):
        assert not isinstance(k, Lin)
        return Lin(self.a * k, self.b * k, self.c * k)
    __rmul__ = __mul__

    def __floordiv__(self, k):
        assert not isinstance(k, Lin) and k > 0
        if self.b % k or self.c % k:
            raise Undecided('floordiv')
        return Lin(self.a // k, self.b // k, self.c // k)

    def __mod__(self, k):
        assert not isinstance(k, Lin) and k > 0
        if self.b % k or self.c % k:
            raise Undecided('mod')
        return Lin(self.a % k)

    def lo_hi(self):
        """min and max over the box (at its corners)."""
        lo = self.a + min(0, self.b * Lin.J) + min(0, self.c * Lin.E)
        hi = self.a + max(0, self.b * Lin.J) + max(0, self.c * Lin.E)
        return lo, hi

    def _sign(self, o):
        """-1, 0 or 1 for self - o, the same on the whole box, or Undecided."""
        if isinstance(o, float):                 # only +inf occurs
            return -1
        d = self - Lin.of(o)
        if d.b == 0 and d.c == 0:
            return (d.a > 0) - (d.a < 0)
        lo, hi = d.lo_hi()
        if lo > 0:
            return 1
        if hi < 0:
            return -1
        if lo == hi == 0:
            return 0
        raise Undecided('cmp')

    def __lt__(self, o):
        return self._sign(o) < 0

    def __le__(self, o):
        return self._sign(o) <= 0

    def __gt__(self, o):
        return self._sign(o) > 0

    def __ge__(self, o):
        return self._sign(o) >= 0

    def __eq__(self, o):
        if isinstance(o, (tuple, list, str)) or o is None:
            return False
        return self._sign(o) == 0

    def __ne__(self, o):
        return not self.__eq__(o)

    def __hash__(self):
        raise TypeError

    def __repr__(self):
        return 'Lin(%d,%d,%d)' % (self.a, self.b, self.c)


def lmin(a, b):
    return b if b < a else a


class Slow(Exception):
    pass


class Fast:
    """State at a round start (all digits 2).  F: front values, front first (depths m-1, ..., len(D)).
    D[q] = [base, R0, stamp]: the old group at depth q, value base - (R - R0) * rate(q)."""

    FMIN, FMAX = 8, 24

    def __init__(self, n0, G, rounds):
        self.R = rounds
        self.halted = False
        self.slow_rounds = 0
        self.skips = 0
        self.skipped = 0
        self.load(n0, G)

    # ---------------------------------------------------------------- storage
    def load(self, n0, G):
        assert normal(G)
        self.n0 = n0
        m = len(G)
        vals = [n for _, n in G]               # front first
        k = min(m, self.FMIN)
        self.F = vals[:k]
        self.D = [[n, self.R, 0] for n in reversed(vals[k:])]
        self.heap = []
        for q in range(len(self.D)):
            self.push(q)

    def m(self):
        return len(self.D) + len(self.F)

    def valD(self, q, R=None):
        b, r0, _ = self.D[q]
        return b - ((self.R if R is None else R) - r0) * rate(q)

    def push(self, q):
        g = self.D[q]
        lim = rate(q) + 2
        k = 0 if g[0] < lim else (g[0] - lim) // rate(q) + 1
        heapq.heappush(self.heap, (g[1] + k, q, g[2]))

    def due_round(self):
        """The first round at whose start some old group is below rate + 2 (it may run out in that round)."""
        h = self.heap
        while h:
            r, q, st = h[0]
            if q < len(self.D) and self.D[q][2] == st:
                return r
            heapq.heappop(h)
        return None

    def materialize(self):
        q = len(self.D) - 1
        v = self.valD(q)
        self.D.pop()
        self.F.append(v)

    def stash(self):
        v = self.F.pop()
        q = len(self.D)
        self.D.append([v, self.R, self.stamp_next()])
        self.push(q)

    _st = 0

    def stamp_next(self):
        Fast._st += 1
        return Fast._st

    def state(self):
        G = [(2, v) for v in self.F] + [(2, self.valD(q)) for q in range(len(self.D) - 1, -1, -1)]
        return self.n0, G

    def normalize(self):
        while len(self.F) < self.FMIN and self.D:
            self.materialize()
        while len(self.F) > self.FMAX:
            self.stash()

    # ---------------------------------------------------------------- one round (transcription of Sim.step)
    def round_core(self, n0, F, lenD, symbolic):
        """One round on the front.  Returns (n0', F').  Raises Slow when skip.py would hand the round to the exact
        model, and Undecided (symbolic only) when a comparison is not the same over the whole range of j."""
        m = lenD + len(F)
        if m < 8:
            raise Slow
        # due groups in the front (the old ones are checked by the caller)
        qd = None
        for i, v in enumerate(F):
            q = m - 1 - i
            if v < rate(q) + 2:
                qd = q
        if not symbolic:
            dr = self.due_round()
            if dr is not None and dr <= self.R:
                raise Slow                       # an old group is due: the caller materializes and retries
        cut = m - 2 if qd is None else min(m - 2, qd - 1)
        if cut < 2:
            raise Slow
        if cut < lenD:
            raise Slow                           # the prefix reaches the old groups (caller materializes)
        c = m - cut
        P = [(2, F[i]) for i in range(c)]
        below = F[c:]
        W = pow3(cut) - 1
        while True:
            L = [0] * (c + 1)
            for i, (d, n) in enumerate(P):
                L[i + 1] = L[i] + d * pow3(i)
            tot = L[c] + W * pow3(c)
            if tot == 0:
                break
            best = tot
            for i, (d, n) in enumerate(P):
                q3 = pow3(i + 1)
                if n >= 1:
                    ev = L[i + 1] + 1 + (n - 1) * q3
                else:
                    ev = L[i + 1] + 1
                    if d >= 1:
                        ev = lmin(ev, L[i] + 1 + (d - 1) * pow3(i))
                best = lmin(best, ev - 1)
            if best > 0:
                new = tot - best
                P = [((new // pow3(i)) % 3, n - (tot // pow3(i + 1) - new // pow3(i + 1))) for i, (d, n) in enumerate(P)]
                P = [(conc(d), n) for d, n in P]
                W, n0 = new // pow3(c), n0 + best
                if new == 0:
                    break
            if not P or P[-1][1] == 0:
                raise Slow
            r = bounce_lean(n0, P + [(W, BIG)])
            if r[0] != 'next' or r[3] is not None or not r[2] or r[2][-1][1] != BIG:
                raise Slow
            n0, P, W = r[1], r[2][:-1], r[2][-1][0]
            c = len(P)
            if c == 0:
                raise Slow
        if any(n < 2 for _, n in P):
            raise Slow
        newF = [n0] + [n - 1 for _, n in P]
        for i, v in enumerate(below):
            q = cut - 1 - i
            newF.append(v - rate(q))
        return 2, newF

    def last(self):
        return self.valD(0) if self.D else self.F[-1]

    def exact_round(self):
        """One exact round (as skip.py does it)."""
        if self.m() < 8 or self.last() < 3:
            return self.slow()
        while True:
            dr = self.due_round()
            if dr is not None and dr <= self.R:
                # an old group may run out: bring it (and all above it) into the front, down to one below it
                h = self.heap
                qs = []
                while h and h[0][0] <= self.R:
                    r, q, st = heapq.heappop(h)
                    if q < len(self.D) and self.D[q][2] == st:
                        qs.append(q)
                qmin = min(qs)
                target = max(qmin - 1, 0)
                while len(self.D) > target:
                    self.materialize()
                continue
            try:
                n0, F = self.round_core(self.n0, self.F, len(self.D), False)
            except Slow:
                lenD = len(self.D)
                m = self.m()
                # perhaps only the prefix reaches the old groups: bring them in and retry
                qd = None
                for i, v in enumerate(self.F):
                    q = m - 1 - i
                    if v < rate(q) + 2:
                        qd = q
                cut = m - 2 if qd is None else min(m - 2, qd - 1)
                if m >= 8 and cut >= 2 and cut < lenD:
                    while len(self.D) > cut:
                        self.materialize()
                    continue
                return self.slow()
            self.R += 1
            self.n0, self.F = n0, F
            self.normalize()
            return

    def slow(self):
        """Rounds with the exact model, until all digits are 2 again (skip.py, Sim.slow)."""
        n0, G = self.state()
        self.slow_rounds += 1
        while True:
            _, n0, G = jump(n0, G)
            r = bounce_lean(n0, G)
            if r[0] != 'next':
                self.halted = True
                self.halt_state = (n0, G)
                return
            n0, G = r[1], r[2]
            if r[3] == 'E':
                self.R += 1
            if r[3] in ('D', 'A') and normal(G):
                break
        self.load(n0, G)

    # ---------------------------------------------------------------- skipping
    def try_skip(self, H):
        """H: four snapshots (R, n0, F, lenD) two rounds apart, the last one (F3) the current state.  With the
        differences D1, D2, D3 and p = D3 - D2, the orbit is guessed as F(j) = F3 + j*D3 + e_j*p, where the next
        differences grow by lam^t*p (lam = p / (D2 - D1), an integer): e_0 = 0, e_(j+1) = e_j + s_j with
        s_j = (lam-1)*e_j + lam*j + lam.  The two rounds are run once, symbolically, on the box F3 + j*D3 + e*p
        (j in [0, K-1], e in [0, e_(K-1)]) and must give F(j+1), i.e. F3 + D3 + lam*p + j*(D3 + lam*p) + e*lam*p.
        Since the run is affine on the box and the orbit stays in the box, the K cycles are then exact."""
        S = H[-4:]
        if any(x[1] != S[0][1] or x[3] != S[0][3] or len(x[2]) != len(S[0][2]) for x in S):
            return 0
        if any(S[i + 1][0] != S[i][0] + 2 for i in range(3)) or len(self.D) != S[-1][3] or not self.D:
            return 0
        Fs = [x[2] for x in S]
        D = [[b - a for a, b in zip(Fs[i], Fs[i + 1])] for i in range(3)]
        lam = None
        for x1, x2, x3 in zip(*D):
            p1, p2 = x2 - x1, x3 - x2
            if p1 == 0:
                if p2 != 0:
                    return 0
                continue
            if p2 % p1:
                return 0
            if lam is None:
                lam = p2 // p1
            elif lam != p2 // p1:
                return 0
        if lam is None:
            lam = 1
        elif lam < 1:
            return 0
        d3 = D[2]
        pv = [x3 - x2 for x2, x3 in zip(D[1], D[2])]
        F3 = Fs[3]
        dr = self.due_round()
        kmax = 1 << 40 if dr is None else (dr - self.R) // 2 - 1
        kmax = min(kmax, (self.valD(0) - 3) // (2 * rate(0)) - 1)
        args = (S[-1][1], F3, d3, pv, lam)
        if kmax < 4 or not self.check_cycle(*args, 4):
            return 0
        if self.check_cycle(*args, kmax):
            K = kmax
        else:
            lo, hi = 4, kmax                     # lo works, hi does not
            while hi - lo > max(1, lo // 8):
                mid = (lo + hi) // 2
                if self.check_cycle(*args, mid):
                    lo = mid
                else:
                    hi = mid
            K = lo
        eK = ecount(lam, K)
        self.F = [f + K * a + eK * b for f, a, b in zip(F3, d3, pv)]
        self.R += 2 * K
        self.skips += 1
        self.skipped += 2 * K
        return K

    def check_cycle(self, n0, F, d3, pv, lam, K):
        Lin.J = K - 1
        Lin.E = ecount(lam, K - 1)
        Fs = [Lin(f, a, b) for f, a, b in zip(F, d3, pv)]
        try:
            a, G = self.round_core(n0, Fs, len(self.D), True)
            a, G = self.round_core(a, [Lin.of(x) for x in G], len(self.D), True)
            if a != n0 or len(G) != len(F):
                return False
            for g, f, x, y in zip(G, F, d3, pv):
                g = Lin.of(g)
                if g.a != f + x + lam * y or g.b != x + lam * y or g.c != lam * y:
                    return False
            return True
        except (Undecided, Slow):
            return False


_EC = {}


def ecount(lam, j):
    """e_j: e_0 = 0, e_(t+1) = e_t + (lam-1)*e_t + lam*t + lam."""
    key = (lam, j)
    if key not in _EC:
        if len(_EC) > 4096:
            _EC.clear()
        _EC[key] = _ecount(lam, j)
    return _EC[key]


def _ecount(lam, j):
    if lam == 1:
        return j * (j + 1) // 2
    num = lam * (lam * (lam ** j - 1) // (lam - 1) - j)
    assert num % (lam - 1) == 0
    return num // (lam - 1)


def conc(x):
    """A number that must not depend on j."""
    if isinstance(x, Lin):
        if x.b != 0:
            raise Undecided('conc')
        return x.a
    return x


class Runner:
    def __init__(self, sim):
        self.s = sim
        self.hist = []

    def snap(self):
        s = self.s
        return (s.R, s.n0, list(s.F), len(s.D))

    def advance(self):
        """One exact round, then a skip if the last two rounds look like a cycle.  Returns rounds skipped."""
        s = self.s
        s.exact_round()
        if s.halted:
            return 0
        self.hist.append(self.snap())
        if len(self.hist) > 7:
            self.hist.pop(0)
        if len(self.hist) >= 7:
            K = s.try_skip(self.hist[0::2])
            if K:
                self.hist = [self.snap()]
                return K
        return 0


def test(upto, start=None):
    from skip import Sim
    if start:
        n0, G, rounds = pickle.load(open(start, 'rb'))
        upto += rounds
    else:
        rounds, n0, G = first_normal(START[0], START[1], 0)
    ref = Sim(n0, G, rounds)
    f = Fast(n0, G, rounds)
    run = Runner(f)
    checked, t0 = 0, time.time()
    while f.R < upto and not f.halted:
        run.advance()
        while ref.rounds < f.R and not ref.halted:
            ref.step()
        if ref.rounds != f.R or ref.state() != f.state():
            print('MISMATCH at round', f.R, ref.rounds)
            return False
        checked += 1
    print('%d round starts agree with skip.py (rounds %d to %d; %d skips covering %d rounds; %d exact-model rounds) %.0f s' % (
        checked, rounds, f.R, f.skips, f.skipped, f.slow_rounds, time.time() - t0))
    return True


def summary(f):
    n0, G = f.state()
    c = [(len(G) - i, o) for i, o in charges(G)]
    return 'round %d: %d groups, last groups %s, charged pairs (position from the right, residue) %s, skips %d (%d rounds), exact-model rounds %d' % (
        f.R, len(G), [n for _, n in G[-3:]], c, f.skips, f.skipped, f.slow_rounds)


def run(upto, seconds, start=None, ckpt=None):
    if start:
        n0, G, rounds = pickle.load(open(start, 'rb'))
    else:
        rounds, n0, G = first_normal(START[0], START[1], 0)
    f = Fast(n0, G, rounds)
    r = Runner(f)
    t0 = time.time()
    tlast = t0
    slow = f.slow_rounds
    nxt = 1
    while f.R < upto and time.time() - t0 < seconds and not f.halted:
        r.advance()
        if f.slow_rounds != slow or f.R >= nxt:
            print('%.0f s ' % (time.time() - t0) + summary(f), flush=True)
            slow = f.slow_rounds
            while nxt <= f.R:
                nxt = int(nxt * 1.25) + 1
        if ckpt and time.time() - tlast > 1800:
            tlast = time.time()
            n0, G = f.state()
            pickle.dump((n0, G, f.R), open(ckpt + '.tmp', 'wb'))
            os.replace(ckpt + '.tmp', ckpt)
    if f.halted:
        print('HALT in round', f.R, flush=True)
    print('stopped: ' + summary(f) + ' after %.0f s' % (time.time() - t0), flush=True)
    if ckpt:
        n0, G = f.state()
        pickle.dump((n0, G, f.R), open(ckpt + '.tmp', 'wb'))
        os.replace(ckpt + '.tmp', ckpt)
    return f


if __name__ == '__main__':
    a = sys.argv[2:]
    if sys.argv[1] == 'test':
        sys.exit(0 if test(int(a[0]), a[1] if len(a) > 1 else None) else 1)
    run(int(a[0]), float(a[1]), a[2] if len(a) > 2 and a[2] != '-' else None, a[3] if len(a) > 3 else None)
