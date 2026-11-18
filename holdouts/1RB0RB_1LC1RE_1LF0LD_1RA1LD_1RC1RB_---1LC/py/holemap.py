"""The hole map of 1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC.

Sample: the head in D on the leftmost visited cell, reading a 1. The visited tape is then N cells of 1 with one 0
(the hole) at position p (0-based from the left). From one sample to the next:

    p even:            N' = N + p/2 + 2,   p' = N' - 2
    p odd, p >= 5:     N' = N + 1,         p' = (p-3)/2
    p = 3:             N odd: N' = N + 4, p' = N' - 3;   N even: N' = N + 3, p' = N' - 2
    p = 1:             halts

`check`   compares the map with the machine on every (N, p) with N < LIMIT (default 120), and along the run from
          blank tape for STEPS steps (default 2e7);
`run K`   iterates the map K times from the run's first sample and reports how close it came to halting.
`rules`   the rule table in terms of S(p, r) = 0^inf D> 1^p 0 1^r 0^inf (f and cost of lean/Map.lean, the costs as
          polynomials) against direct simulation: a grid of S tapes, each run to the next S tape or the halt, and
          every S tape of the first 10^8 steps from blank (under a minute).

usage: python3 holemap.py check [LIMIT] [STEPS] | run K | rules
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.machine import Machine, Run, Tape  # noqa: E402

M = "1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC"
C = 3      # state D


def hmap(N, p):
    """The next sample (N', p'), or None for a halt."""
    if p % 2 == 0:
        N2 = N + p // 2 + 2
        return N2, N2 - 2
    if p >= 5:
        return N + 1, (p - 3) // 2
    if p == 3:
        return (N + 4, N + 1) if N % 2 else (N + 3, N + 1)
    if p == 1:
        return None
    raise ValueError((N, p))


def sample(r):
    w = r.tape.word()
    z = [i for i, c in enumerate(w) if c == 0]
    return len(w), z


def machine_next(N, p, maxs=10 ** 7):
    """Run the machine from the sample (N, p) to the next sample: (N', p'), None for a halt, '?' otherwise."""
    t = Tape()
    for i in range(N):
        t.set(i, 1)
    t.set(p, 0)
    t.lo, t.hi = 0, N - 1
    r = Run(Machine.parse(M), state=C, tape=t, head=0)
    while r.steps < maxs:
        if not r.step():
            return None
        if r.state == C and r.head == r.tape.lo and r.tape.get(r.head) == 1:
            n, z = sample(r)
            return (n, z[0]) if len(z) == 1 else "?"
    return "?"


def check(limit, steps):
    bad = 0
    for N in range(3, limit):
        for p in range(1, N - 1):
            want = hmap(N, p)
            got = machine_next(N, p)
            if got != want:
                bad += 1
                print("mismatch", N, p, want, got)
    print(f"map = machine on all samples with N < {limit}, 1 <= p <= N-2: {bad} mismatches")
    r = Run(Machine.parse(M))
    prev, n, ok = None, 0, 0
    while r.steps < steps:
        if not r.step():
            print("halted at", r.steps)
            return
        if r.state == C and r.head == r.tape.lo and r.tape.get(r.head) == 1 and r.steps > 1:
            N, z = sample(r)
            cur = (N, z[0]) if len(z) == 1 else None
            if prev is not None:
                ok += hmap(*prev) == cur
                n += 1
            prev = cur
    print(f"along the run to {steps:.0e} steps: {ok} of {n} sample transitions follow the map")


def run(k):
    N, p = 5, 2      # the run's first sample (step 11)
    closest = []
    for i in range(k):
        nxt = hmap(N, p)
        if nxt is None:
            print("halts at map step", i, "N =", N)
            return
        if p in (1, 3):
            closest.append((i, p))
        N, p = nxt
    print(f"no halt in {k} map steps; N now has {len(str(N))} digits; visits to p = 1 or 3: {closest[:20]}")


# ---- The rule table: f and cost of lean/Map.lean, with the costs written as polynomials ----

def rule(p, r):
    """S(p, r) -> (next (p', r') or 'halt', steps); p, r >= 1.  The halt counts the halting step."""
    if p == 1:
        return "halt", 8
    if p == 3:
        return ((r + 5, 2), 2 * r + 28) if r % 2 else ((r + 5, 1), 2 * r + 26)
    if p % 2 == 0:
        k = (p - 2) // 2
        return (3 * k + r + 4, 1), 6 * k * k + 4 * k * r + 22 * k + 8 * r + 17
    m = (p - 1) // 2
    return (m - 1, m + r + 3), 2 * m * m + 6 * m + 5


def lean_cost(p, r):
    """`cost` of lean/Map.lean, verbatim."""
    tri = lambda n: n * (n - 1) // 2  # noqa: E731
    if p == 3:
        return 2 * r + 28 if r % 2 == 1 else 2 * r + 26
    if p % 2 == 0:
        return (4 * ((p - 2) // 2) + 6) + ((4 * ((p - 2) // 2) + 7) * (r - 1) + ((12 * tri((p - 2) // 2)
                + 25 * ((p - 2) // 2)) + (3 * ((p - 2) // 2) + r + 18)))
    return 1 + ((4 * tri((p - 1) // 2) + 7 * ((p - 1) // 2)) + ((p - 1) // 2 + 4))


class FastSim:
    """Direct simulation on a bytearray; reports S tapes."""

    def __init__(self, cells, st, size):
        self.T = {}
        for q, grp in enumerate(M.split("_")):
            for b in (0, 1):
                t = grp[3 * b:3 * b + 3]
                self.T[(q, b)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
        self.t = bytearray(size)
        self.pos = size // 4
        self.t[self.pos:self.pos + len(cells)] = bytes(cells)
        self.st, self.n1 = st, sum(cells)
        self.lm = self.pos + cells.index(1) if 1 in cells else size

    def family(self):
        t, p = self.t, self.pos
        if self.st != C or p != self.lm:
            return None
        q, a = p, 0
        while t[q]:
            a += 1; q += 1
        q += 1
        b = 0
        while t[q]:
            b += 1; q += 1
        return (a, b) if a >= 1 and b >= 1 and a + b == self.n1 else None

    def step(self):
        t, p = self.t, self.pos
        tr = self.T[(self.st, t[p])]
        if tr is None:
            return False
        w, d, s = tr
        if w != t[p]:
            t[p] = w
            if w:
                self.n1 += 1
                if p < self.lm:
                    self.lm = p
            else:
                self.n1 -= 1
                if p == self.lm:
                    q = p
                    while self.n1 and not t[q]:
                        q += 1
                    self.lm = q if self.n1 else len(t)
        self.pos += d; self.st = s
        return True


def rules():
    bad = n = halts = lc = 0
    for p in range(1, 61):
        for r in range(1, 61):
            want = rule(p, r)
            if want[0] != "halt" and want[1] != lean_cost(p, r):
                lc += 1; print("cost differs from Lean's", p, r)
            sim = FastSim([1] * p + [0] + [1] * r, C, 4 * (p + r) + 400)
            got = ("?", 0)
            for k in range(10 ** 6):
                if not sim.step():
                    got = ("halt", k + 1); break
                fam = sim.family()
                if fam:
                    got = (fam, k + 1); break
            n += 1
            halts += want[0] == "halt"
            if got != want:
                bad += 1; print("differs:", (p, r), "simulated", got, "rule", want)
    print(f"rules grid: {n} tapes S(p, r), 1 <= p, r <= 60 ({halts} halting), {bad} failures; "
          f"polynomials = Lean's cost: {lc} differences")
    N = 10 ** 8
    sim = FastSim([0], 0, 200000)
    s, acc, nv, bad2 = None, 0, 0, 0
    for k in range(N):
        if not sim.step():
            print("halted at", k + 1); bad2 += 1; break
        fam = sim.family()
        if not fam:
            continue
        if s is None:
            ok, acc = fam == (2, 2) and k + 1 == 11, 11
        else:
            tgt, st = rule(*s)
            acc += st
            ok = tgt == fam and acc == k + 1
        if not ok:
            bad2 += 1; print("run differs at step", k + 1, fam, s, acc); acc = k + 1
        s, nv = fam, nv + 1
    print(f"rules run: {nv} S tapes in the first {N:.0e} steps (last S{s}), step counts {'ok' if not bad2 else 'FAILED'}")
    s, tot, path = (13, 2), 0, []
    while s != "halt":
        s2, k = rule(*s); path.append((s, k)); tot += k; s = s2
    sim = FastSim([1] * 13 + [0] + [1] * 2, C, 1000)
    k = 1
    while sim.step():
        k += 1
    print("example:", path, "=", tot, "; simulated:", k)
    return bad + bad2 + lc


if __name__ == "__main__":
    if sys.argv[1] == "rules":
        sys.exit(1 if rules() else 0)
    elif sys.argv[1] == "check":
        check(int(sys.argv[2]) if len(sys.argv) > 2 else 120, float(sys.argv[3]) if len(sys.argv) > 3 else 2e7)
    else:
        run(int(sys.argv[2]))
