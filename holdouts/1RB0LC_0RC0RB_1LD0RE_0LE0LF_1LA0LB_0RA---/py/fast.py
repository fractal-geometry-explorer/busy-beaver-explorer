"""The block-list map without the tape: visits evaluated by rules on lists, the run-length simulator only as fallback.

hybrid.py runs the family's machines as a map on block lists (frame A): a *visit* (`go`) to a list l of plain blocks
is done in closed form when it is clean (cf.py, a Lean theorem) and otherwise simulated on a run-length tape, with
every visit nested in it done recursively.  Here three more kinds of visit are evaluated directly on the lists, as
the sequence of visits nested in them, with no tape at all:

* SPREAD  l = [b] ++ T, b odd >= 7:  PUSH spreads b, then five visits to T (first block bumped +1, then +3, +1,
  +1, +1 between them), POP.  Exit B/00 with [b-5] ++ (result of the fifth).  Steps 5b + 51 + the five visits;
  the first visit starts 3b + 6 steps in, the others 8, 14, 14, 14 steps after the previous one ended.
  (This is lean/Family.lean's `go` without the cleanliness condition: it holds whenever every nested visit exits
  B/00, whatever happens inside them.)
* CARRY   l = [1] ++ T:  one visit to T with its first block bumped +1, starting 9 steps in; exit A with no
  prefix and [1] ++ (its result); steps = that visit + 14.
* SWEEP   l = [m] ++ T, m even >= 6 (the left-end round, and the visit right after a merge):  the blocks of T are
  taken from the last to the first.  A new block is made first ([1] -> [2], then three CARRYs -> [8]); then for
  each block t of T, from the last: a visit to [t-1] ++ S, then three CARRYs on [1] ++ (its result); S is what is
  left after the leading 1.  Exit B/00 with [m-2] ++ S.  Steps 5m + 5 sum(T) + 2 len(T) + 7 + the nested visits;
  timing of each nested visit below.  So T = [t2..tk] becomes, when all of these visits are clean,
      [t2 - 18, t3 - 90, ..., tk - 18*5^(k-2), 12*5^(k-1) - 4]
  (H_i(S) = [t_i - 18] ++ G^4(S), folded from the end, G the five-visit map of SPREAD).

Every visit not of these kinds (merges: a first block 3 or 5, a first block 0, 2, 4, an exit other than the
expected one somewhere inside) goes to hybrid.Hybrid.go, i.e. the run-length simulator, whose nested visits come
back here.  If a rule meets an unexpected exit half way, everything it did is undone (F-events included) and the
whole visit goes to the simulator.  So the result is the same function of the list as hybrid.py's; `check` compares
the left-end events and F-events of both on a run.

usage: python3 fast.py MACHINE STEPS            run and print a summary
       python3 fast.py check MACHINE STEPS      compare with hybrid.py
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cf  # noqa: E402
import frames  # noqa: E402
import f05_run  # noqa: E402
import hybrid  # noqa: E402
import hybrid2  # noqa: E402
import rle  # noqa: E402

B, A = 1, 0
BUMPS = (3, 1, 1, 1)


class Tables:
    """cf.clean / cf.go / cf.steps with the powers of 5 kept (the same functions, checked by `selftest`)."""

    def __init__(self):
        self.p5 = [1]
        self.th = [None, 20]          # th[i] = 2 + 18*5^(i-1): least value of middle block i
        self.eff = {}

    def grow(self, k):
        while len(self.p5) <= k + 1:
            self.p5.append(self.p5[-1] * 5)
        while len(self.th) <= k:
            self.th.append(2 + 18 * self.p5[len(self.th) - 1])

    def clean(self, l):
        k = len(l)
        if k == 0 or l[0] % 2 != 1:
            return False
        if k == 1:
            return True
        if l[0] < 7 or l[-1] < 2 or l[-1] % 2:
            return False
        self.grow(k)
        th = self.th
        for i in range(1, k - 1):
            x = l[i]
            if x % 2 or x < th[i]:
                return False
        return True

    def go(self, l):
        k = len(l)
        if k == 1:
            return (l[0] + 1,)
        e = self.eff.get(k)
        if e is None:
            e = self.eff[k] = tuple(cf.eff(k))
        return tuple(b + d for b, d in zip(l, e))

    def steps(self, l):
        k = len(l)
        if k == 1:
            return 5 * l[0] + 9
        self.grow(k)
        p = self.p5
        return sum(p[i + 1] * l[i] for i in range(k)) + cf.K(k)


TAB = Tables()


def selftest(n=3000):
    import random
    random.seed(3)
    for _ in range(n):
        k = random.randint(1, 7)
        l = [random.randrange(0, 40 * 5 ** i) for i in range(k)]
        if random.random() < 0.8:
            l[0] |= 1
            l[1:] = [x & ~1 for x in l[1:]]
        assert TAB.clean(l) == cf.clean(l), l
        if cf.clean(l):
            assert list(TAB.go(l)) == cf.go(l) and TAB.steps(l) == cf.steps(l), l
    print("Tables agree with cf.py on", n, "lists")


class Fallback(Exception):
    pass


class FastMixin:
    """The rules; put in front of hybrid.Hybrid (Fast) or hybrid2.Hybrid2 (Fast2), whose `go` is the fallback."""

    def __init__(self, machine_a, **kw):
        super().__init__(machine_a, **kw)
        self.stats.update({"spread": 0, "carry": 0, "sweep": 0, "fallback": 0})

    def go(self, l, t0, depth=0):
        l = tuple(l)
        if self.use_cf and TAB.clean(l):
            self.stats["cf"] += 1
            return 1, (0, 0), TAB.go(l), TAB.steps(l) + 1
        if len(l) >= 2:
            nf = len(self.fev)
            try:
                b = l[0]
                if b % 2 == 1 and b >= 7:
                    r = self.spread(l, t0, depth)
                    self.stats["spread"] += 1
                    return r
                if b == 1:
                    r = self.carry(l, t0, depth)
                    self.stats["carry"] += 1
                    return r
                if b % 2 == 0 and b >= 6:
                    r = self.sweep(l, t0, depth)
                    self.stats["sweep"] += 1
                    return r
            except Fallback:
                del self.fev[nf:]
            self.stats["fallback"] += 1
        elif len(l) == 1 and l[0] % 2 == 0 and l[0] >= 6:
            nf = len(self.fev)
            try:
                r = self.sweep(l, t0, depth)
                self.stats["sweep"] += 1
                return r
            except Fallback:
                del self.fev[nf:]
            self.stats["fallback"] += 1
        return super().go(l, t0, depth)

    # ------------------------------------------------------------------ the rules
    def sub(self, l, t, depth, want):
        st, pre, X, T = self.go(l, t, depth + 1)
        if want == B:
            if st != 1 or pre != (0, 0) or not X:
                raise Fallback
        elif st != 0 or pre != () or not X or X[0] != 1:
            raise Fallback
        return X, T

    def spread(self, l, t0, depth):
        b = l[0]
        cur = (l[1] + 1,) + l[2:]
        t = t0 + 3 * b + 6
        tot = 5 * b + 51
        for j in range(5):
            X, T = self.sub(cur, t, depth, B)
            tot += T
            if j < 4:
                if X[0] < 1:
                    raise Fallback
                t += T + (8 if j == 0 else 14)
                cur = (X[0] + BUMPS[j],) + X[1:]
        return 1, (0, 0), (b - 5,) + X, tot

    def carry(self, l, t0, depth):
        X, T = self.sub((l[1] + 1,) + l[2:], t0 + 9, depth, B)
        return 0, (), (1,) + X, T + 14

    def sweep(self, l, t0, depth):
        m, Tl = l[0], l[1:]
        k = len(Tl)
        t = t0 + 3 * m + 3 * sum(Tl) + k + 6
        tot = 5 * m + 5 * sum(Tl) + 2 * k + 7
        # the new block: [1] -> [2], then three carries
        X, T = self.sub((1,), t, depth, B)
        tot += T
        t += T + 5
        S = X
        for blk in [None] + list(reversed(Tl)):
            if blk is not None:
                if blk < 8:
                    raise Fallback
                t += 2 * blk - 4
                X, T = self.sub((blk - 1,) + S, t, depth, B)
                if X[0] < 2:
                    raise Fallback
                tot += T
                t += T + 5
            cur = (1,) + X
            for _ in range(3):
                Y, T = self.sub(cur, t, depth, A)
                tot += T
                t += T
                cur = Y
            S = cur[1:]
        return 1, (0, 0), (m - 2,) + S, tot


class Fast(FastMixin, hybrid.Hybrid):
    pass


class Fast2(FastMixin, hybrid2.Hybrid2):
    pass


def run(machine, N, cls=None):
    fr, fa, st = frames.info(machine)
    if cls is None:
        cls = Fast2 if f05_run.needs_raw(fa) else Fast
    h = cls(fa)
    t0 = time.time()
    r = h.run(ord(st) - 65, N)
    return h, r, time.time() - t0


class Stop(Exception):
    pass


def run_list(fa, blocks, N, events=None, cls=None):
    """Run the frame-A table fa from the left-end configuration 0^inf A> 0 (10)^b1 1 ... 1 0^inf (blocks = [b1..]):
    at most N steps or until `events` more left-end events.  Returns (h, outcome) with outcome 'halt', 'events' or
    'steps'; h.top holds the left-end events, h.fev the F-events."""
    if cls is None:
        cls = Fast2 if f05_run.needs_raw(fa) else Fast
    h = cls(fa)
    sim = hybrid.FastRLE(fa)
    sim.right = hybrid.runs_of(((0,), tuple(blocks)))
    sim.q = 0
    h.top = []
    h.sim = sim

    def ev(s, l):
        if all(all(c == 0 for c in w) for w, n in s.left):
            h.top.append((s.steps, s.pos, list(l)))
            if events is not None and len(h.top) > events:
                raise Stop
    try:
        r = h._run(sim, 0, stop_left=False, N=N, on_event=ev)
        out = "halt" if r == "halt" else "steps"
    except Stop:
        out = "events"
    except rle.Halt:
        out = "halt"
    return h, out


def check(machine, N):
    fr, fa, st = frames.info(machine)
    raw = f05_run.needs_raw(fa)
    a, ra, sa = run(machine, N, hybrid2.Hybrid2 if raw else hybrid.Hybrid)
    b, rb, sb = run(machine, N, Fast2 if raw else Fast)
    ok = (a.top == b.top and a.fev == b.fev and a.halted == b.halted and a.sim.steps == b.sim.steps)
    print(machine, "%.0e" % N, "MATCH" if ok else "DIFFER", "left-end", len(a.top), len(b.top), "F", len(a.fev),
          len(b.fev), "hybrid %.1fs fast %.1fs" % (sa, sb), b.stats)
    if not ok:
        for i, (x, y) in enumerate(zip(a.top, b.top)):
            if x != y:
                print("first left-end difference", i, x, y)
                break
        for i, (x, y) in enumerate(zip(a.fev, b.fev)):
            if x != y:
                print("first F difference", i, x, y)
                break
    return ok


if __name__ == "__main__":
    if sys.argv[1] == "selftest":
        selftest()
        sys.exit(0)
    if sys.argv[1] == "check":
        sys.exit(0 if check(sys.argv[2], float(sys.argv[3])) else 1)
    from decimal import Decimal
    h, r, secs = run(sys.argv[1], int(Decimal(sys.argv[2])))
    print("steps %.3e" % h.sim.steps, "HALT" if r == "halt" else "no halt", "left-end", len(h.top), "F", len(h.fev),
          h.stats, "%.1fs" % secs)
