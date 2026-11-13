"""The end events of 1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC as a system on (wall, digits, last cell).

The Python copy of `evstep` (lean/Ends.lean, where it is proved to be the machine: `halts_iff_events`):

    the carry stops inside the digits             ->  the digits change, the wall grows by one pair
    it reaches the last cell d in state q:
      q = a, d = 0                                ->  d becomes 1
      q = a, d = 1                                ->  one more digit (extension)
      q = b, d = 0  or  q = c, d = 1              ->  HALT
      q = b, d = 1  or  q = c, d = 0              ->  conversion: the wall of n + 1 pairs becomes n digits 1,
                                                      then a 0, the marks of the carry and a 1; the wall restarts

usage:
  python3 py/events.py check          compares evstep with the machine itself on 20,000 random small arrivals
  python3 py/events.py epochs [N]     N random counters of 30 to 60 digits (default 300): the events up to the
                                      first halt or conversion, by straight-line programs for the sweeps between
  python3 py/events.py standin [W]    the same from the counter after the first end event of the run from blank
                                      tape, with stand-in walls of 1..W pairs (default 60) in place of 8,072,508,833
  python3 py/events.py twin           the run from blank tape started in state C, which is the run of
                                      1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC (132695) in a mirror
                                      (lean/Twin132695.lean): the machine's arrivals in the first 200,000 steps against
                                      the event system from (0, [1], 1), then the events up to the conversion of a
                                      wall of 410,923 pairs
  python3 py/events.py program [N]    why the next event of that run is out of reach: the exit states of each
                                      prefix of the counter 1^N 0 marks 1 (default N = 140), over one period, kept as
                                      one straight-line program; prints its size every 20 digits (about a minute)
"""
import os
import random
import sys

sys.setrecursionlimit(1000000)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import slp as S  # noqa: E402

M = "1RB0RD_1LC0RA_1LF1LD_0RE0LC_---1LB_1RB1RC"
ACT = S.ACT          # (state, digit) -> (written digit, next state or None for "stop")


def carry(xs):
    """(new digits, None) if the carry stops inside xs, else (digits written, state it leaves in)."""
    q, out = 'a', []
    for i, x in enumerate(xs):
        o, q = ACT[(q, x)]
        out.append(o)
        if q is None:
            return out + list(xs[i + 1:]), None
    return out, q


def cind(xs):
    q, out = 'a', []
    for x in xs:
        q = ACT[(q, x)][1]
        out.append(1 if q == 'c' else 0)
    return out


def evstep(n, xs, d, build=True):
    """One sweep from the arrival with a wall of n + 1 pairs: ('halt',) or (kind, n', xs', d').  With `build`
    false a conversion is only named (its counter has n more digits)."""
    ys, q = carry(xs)
    if q is None:
        return ('sweep', n + 1, ys, d)
    if q == 'a':
        return ('stop', n + 1, ys, 1) if d == 0 else ('ext', n + 1, ys + [1], 1)
    if (q, d) in (('b', 0), ('c', 1)):
        return ('halt',)
    return ('conv', 0, [1] * n + [0] + cind(xs) + [1], 1) if build else ('conv',)


def table():
    t = {}
    for s, grp in enumerate(M.split("_")):
        for r in range(2):
            w = grp[3 * r:3 * r + 3]
            t[(s, r)] = None if w[0] == "-" else (int(w[0]), 1 if w[1] == "R" else -1, ord(w[2]) - 65)
    return t


T = table()


def machine_sweep(n, xs, d, limit=10 ** 7):
    """The machine itself from the arrival (10)^(n+1) A> 1 1 x1 1 ... xk 1 d: ('halt',) or (n', xs', d') at the
    next arrival (A on a 1 with the wall (10)^(n'+1) and nothing else on its left)."""
    pad = 8 + 4 * (n + len(xs))
    tape = [0] * pad + [1, 0] * (n + 1) + [1, 1] + [v for x in xs for v in (x, 1)] + [d] + [0] * 8
    pos, st = pad + 2 * (n + 1), 0
    hi = pad + 2 * (n + 1) + 2 + 2 * len(xs)
    for i in range(limit):
        t = T[(st, tape[pos])]
        if t is None:
            return ('halt',)
        tape[pos] = t[0]
        pos += t[1]
        st = t[2]
        hi = max(hi, pos)
        if i > 0 and st == 0 and tape[pos] == 1 and tape[pos + 1] == 1:
            lo = min(j for j, v in enumerate(tape) if v)
            left = tape[lo:pos]
            if len(left) % 2 == 0 and len(left) >= 2 and left == [1, 0] * (len(left) // 2):
                rest = tape[pos + 2:hi + 1]
                if len(rest) % 2 == 1 and all(v == 1 for v in rest[1::2]):
                    return (len(left) // 2 - 1, rest[0:-1:2], rest[-1])
    raise RuntimeError("no arrival")


def check(trials=20000, seed=3):
    rng, kinds = random.Random(seed), {}
    for _ in range(trials):
        n, k = rng.randint(0, 6), rng.randint(0, 12)
        # mostly ones, so that the carry often runs to the end
        xs = [1 if rng.random() < 0.8 else 0 for _ in range(k)]
        d = rng.randint(0, 1)
        e = evstep(n, xs, d)
        m = machine_sweep(n, xs, d)
        assert (e == ('halt',) and m == ('halt',)) or (e[1:] == m), (n, xs, d, e, m)
        kinds[e[0]] = kinds.get(e[0], 0) + 1
    print(f"evstep agrees with the machine on {trials} random arrivals:", dict(sorted(kinds.items())))


def first_exit(xs):
    """(K, digits after K sweeps): the first K sweeps stop inside xs, the next one runs through all of them."""
    def runs(k):
        s = S.SLP()
        return s.run(s.power(k), xs)[1] != s.EPS
    lo, hi = 0, 1
    while not runs(hi):
        lo, hi = hi, 2 * hi
    while hi - lo > 1:
        m = (lo + hi) // 2
        lo, hi = (lo, m) if runs(m) else (m, hi)
    s = S.SLP()
    ys, w = s.run(s.power(lo), xs)
    assert w == s.EPS
    return lo, ys


def epoch(n, xs, d, max_events=10 ** 6):
    """Events from (n, xs, d) up to the first halt or conversion: (list of kinds, sweeps, digits at the end)."""
    kinds, sweeps = [], 0
    for _ in range(max_events):
        k, xs = first_exit(xs)
        n, sweeps = n + k, sweeps + k
        e = evstep(n, xs, d, build=False)
        sweeps += 1
        kinds.append(e[0])
        if e[0] in ('halt', 'conv'):
            return kinds, sweeps, len(xs)
        _, n, xs, d = e
    raise RuntimeError("too many events")


def summary(rows):
    halts = sum(1 for k, _, _ in rows if k[-1] == 'halt')
    ev = sorted(len(k) for k, _, _ in rows)
    print(f"{len(rows)} epochs: {halts} end in a halt, {len(rows) - halts} in a conversion; "
          f"events per epoch: median {ev[len(ev) // 2]}, max {ev[-1]}")
    first = {}
    for k, _, _ in rows:
        first[k[0]] = first.get(k[0], 0) + 1
    print("  first event of the epoch:", dict(sorted(first.items())))


def epochs(count=300, seed=7):
    rng, rows = random.Random(seed), []
    for _ in range(count):
        xs = [rng.randint(0, 1) for _ in range(rng.randint(30, 60))]
        rows.append(epoch(rng.randint(0, 20), xs, 1))
    summary(rows)


def read_Y0():
    import re
    text = open(os.path.join(HERE, '..', 'lean', 'Cert.lean')).read()
    m = re.search(r'def Y0 : List Bool := bits "([01]+)"', text)
    return [int(c) for c in m.group(1)]


def standin(wmax=60):
    y0 = read_Y0()
    assert carry(y0)[1] == 'b'                       # the first end event: b on the last cell 1, a conversion
    rows = []
    for w in range(1, wmax + 1):
        e = evstep(w - 1, y0, 1)
        assert e[0] == 'conv'
        r = epoch(e[1], e[2], e[3])
        rows.append(r)
        print(f"wall {w:3d}: {' '.join(r[0])}  ({r[1]:,} sweeps, {r[2]} digits at the end)", flush=True)
    summary(rows)


class Exits:
    """The carry states leaving a prefix of the counter, in time order over one period of the prefix, as a
    straight-line program (node 0 empty, 1..3 the states a, b, c, others a pair of nodes).  `level(W, x)` is the
    program for one more digit x: the old sequence acting on x, twice if once does not bring x back."""

    def __init__(self):
        self.left, self.right, self.first, self.ids, self.memo = [0] * 4, [0] * 4, [0, 1, 2, 3], {}, {}

    def cat(self, x, y):
        if x == 0 or y == 0:
            return x or y
        n = self.ids.get((x, y))
        if n is None:
            n = self.ids[(x, y)] = len(self.left)
            self.left.append(x)
            self.right.append(y)
            self.first.append(self.first[x])
        return n

    def trans(self, n, x):
        r = self.memo.get(2 * n + x)
        if r is None:
            if n == 0:
                r = (0, x)
            elif n < 4:
                o, g = ACT[(' abc'[n], x)]
                r = (' abc'.index(g) if g else 0, o)
            else:
                s1, x1 = self.trans(self.left[n], x)
                s2, x2 = self.trans(self.right[n], x1)
                r = (self.cat(s1, s2), x2)
            self.memo[2 * n + x] = r
        return r

    def level(self, w, x):
        s1, x1 = self.trans(w, x)
        if x1 == x:
            return s1
        s2, x2 = self.trans(w, x1)
        assert x2 == x
        return self.cat(s1, s2)

    def fate(self, xs, report=0):
        """The events from the counter xs with last cell 1, up to the first halt or conversion (as `epoch`)."""
        w, kinds = 1, []
        for i, x in enumerate(xs):
            w = self.level(w, x)
            if report and (i + 1) % report == 0:
                print(f"  {i + 1} digits: {len(self.left):,} nodes", flush=True)
        while True:
            q = ' abc'[self.first[w]]
            kinds.append({'a': 'ext', 'b': 'conv', 'c': 'halt'}[q])
            if q != 'a':
                return kinds
            w = self.level(w, 0)             # an extension is a carry stopping on a digit 0 that was not there


def program(n=140):
    rng = random.Random(5)
    for _ in range(100):
        xs = [rng.randint(0, 1) for _ in range(rng.randint(5, 40))]
        assert Exits().fate(xs) == epoch(0, xs, 1)[0]
    print("the exit-sequence program gives the events of `epoch` on 100 random counters")
    y = [int(c) for c in "101011011111011001101011001110000000011111111010101100011111"]   # YT, lean/Twin132695.lean
    print(f"the counter 1^{n} 0 marks 1 (the real one has 410,922 ones):")
    print("  events:", ' '.join(Exits().fate([1] * n + [0] + cind(y) + [1], report=20)))


def twin(steps=200000):
    n_cells = 1 << 16
    tape, pos, st = [0] * n_cells, n_cells // 2, 2                  # blank tape, state C
    lo = hi = pos
    arrivals = []
    for i in range(1, steps + 1):
        t = T[(st, tape[pos])]
        assert t is not None
        tape[pos] = t[0]
        pos += t[1]
        st = t[2]
        lo, hi = min(lo, pos), max(hi, pos)
        if st == 0 and tape[pos] == 1 and tape[pos + 1] == 1:
            ones = [j for j in range(lo, hi + 1) if tape[j]]
            left = tape[ones[0]:pos]
            if len(left) >= 2 and left == [1, 0] * (len(left) // 2):
                rest = tape[pos + 2:ones[-1] + 1]
                if len(rest) % 2 == 1 and all(v == 1 for v in rest[1::2]):
                    arrivals.append((i, len(left) // 2 - 1, rest[0:-1:2], rest[-1]))
    assert arrivals[0] == (16, 0, [1], 1), arrivals[0]
    cur = arrivals[0][1:]
    for i, n, xs, d in arrivals[1:]:
        e = evstep(*cur)
        assert e[1:] == (n, xs, d), (i, e, n, xs, d)
        cur = e[1:]
    print(f"state C on blank tape: first arrival at step 16 with (0, [1], 1); the event system gives the next "
          f"{len(arrivals) - 1} arrivals of the machine (to step {arrivals[-1][0]:,})")
    cur, k = (0, [1], 1), 0
    while len(cur[1]) < 100000:
        e = evstep(*cur)
        k += 1
        assert e[0] != 'halt'
        if e[0] != 'sweep':
            print(f"  sweep {k:,}: {e[0]} (wall of {cur[0] + 1:,} pairs, {len(cur[1])} digits -> {len(e[2]):,} digits)")
        cur = e[1:]
    print(f"after {k:,} sweeps: wall of {cur[0] + 1} pair, {len(cur[1]):,} digits, {sum(cur[1]):,} of them 1")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "check"
    if cmd == "check":
        check()
    elif cmd == "epochs":
        epochs(int(sys.argv[2]) if len(sys.argv) > 2 else 300)
    elif cmd == "standin":
        standin(int(sys.argv[2]) if len(sys.argv) > 2 else 60)
    elif cmd == "twin":
        twin()
    elif cmd == "program":
        program(int(sys.argv[2]) if len(sys.argv) > 2 else 140)
