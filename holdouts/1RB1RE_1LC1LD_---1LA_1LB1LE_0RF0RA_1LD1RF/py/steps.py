"""The rule table of 1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF with exact step counts, against direct simulation.

Tape family (P of lean/Phase.lean), u = 2 or 3:
  P(c, u, x) = 0^inf 1^c (01)^u 0 0 (10)^x F> 0^inf          (P(1, 2, x) and P(0, 3, x) are the same tape)
P(1, 3, x) is also the tape P(0, 4, x), which a phase from P(4, u, x) passes through; it is not counted as a visit:
from it the machine bounces once more (4x + 14 steps) to P(0, 2, x + 3), and the halt row of P(1, 3, x) adds up the
two.  Halting rows are checked by simulating to the halt.
Rules (lean/Phase.lean: `phase`, and the epoch ends `endv`), with X = x + u + 4 and h = floor(X/2):
  0^inf A> 0^inf   --139-->                         P(3, 3, 5)
  P(c+4, u, x)     --12x + 8u + 6h^2 + 4h + 50-->   P(c, 2 + X mod 2, 3h - 1)      x >= 1          (phase)
  P(0, 3, x)       --8x + 131-->                    P(2x + 5, 3, 5)                (= P(1, 2, x))
  P(3, 2, x)       --12x + 157-->                   P(2x + 8, 3, 5)
  P(3, 3, x)       --12x + 165-->                   P(2x + 10, 3, 5)
  P(0, 2, x)       --6x + 24-->                     halt
  P(1, 3, x)       --10x + 56-->                    halt
  P(2, 2, x)       --10x + 52-->                    halt
  P(2, 3, x)       --10x + 58-->                    halt                           (the ends: x >= 16 in Lean)

usage: python3 py/steps.py     checks the rules and the step counts: a grid of P tapes, each simulated to the next
                               P tape or the halt, and every P tape of the first 10^8 steps from blank (under a minute)
"""
import sys

M = "1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF"
F = 5


def table():
    T = {}
    for s, grp in enumerate(M.split("_")):
        for r in (0, 1):
            t = grp[3 * r:3 * r + 3]
            T[(s, r)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


def canon(s):
    return (0, 3, s[2]) if s[:2] == (1, 2) else s


def rule(s):
    """P(c, u, x) -> (next P tape or 'halt', steps)."""
    c, u, x = s
    if c >= 4:
        X = x + u + 4
        h = X // 2
        return (c - 4, 2 + X % 2, 3 * h - 1), 12 * x + 8 * u + 6 * h * h + 4 * h + 50
    s = canon(s)
    return {(0, 3): ((2 * x + 5, 3, 5), 8 * x + 131), (3, 2): ((2 * x + 8, 3, 5), 12 * x + 157),
            (3, 3): ((2 * x + 10, 3, 5), 12 * x + 165), (0, 2): ("halt", 6 * x + 24), (1, 3): ("halt", 10 * x + 56),
            (2, 2): ("halt", 10 * x + 52), (2, 3): ("halt", 10 * x + 58)}[s[:2]]


def expected(s):
    """The first P tape reached, with the steps: as `rule`, but P(1, 3, y) is passed through (it is the same tape as
    P(0, 4, y), the middle of a phase): one more bounce, 4y + 14 steps, to P(0, 2, y + 3)."""
    t, k = rule(s)
    if t != "halt" and t[:2] == (1, 3):
        t, k = (0, 2, t[2] + 3), k + 4 * t[2] + 14
    return (t if t == "halt" else canon(t)), k


class Sim:
    def __init__(self, cells, st, size):
        self.off = size // 4
        self.t = bytearray(size)
        self.t[self.off:self.off + len(cells)] = bytes(cells)
        self.pos, self.st = self.off + len(cells), st
        self.n1 = sum(cells)
        self.hi = self.pos   # cells at or right of hi are blank

    def family(self):
        t, p = self.t, self.pos
        if self.st != F or p < self.hi:
            return None
        q, x = p - 1, 0
        while t[q] == 0 and t[q - 1] == 1:
            x += 1; q -= 2
        if t[q] or t[q - 1]:
            return None
        q -= 2
        u = 0
        while t[q] == 1 and t[q - 1] == 0:
            u += 1; q -= 2
        c = 0
        while t[q]:
            c += 1; q -= 1
        if u not in (2, 3) or c + u + x != self.n1:
            return None
        return (c, u, x)

    def step(self, T):
        t, p = self.t, self.pos
        tr = T[(self.st, t[p])]
        if tr is None:
            return False
        w, d, s = tr
        self.n1 += w - t[p]
        t[p] = w
        if w and p >= self.hi:
            self.hi = p + 1
        self.pos += d; self.st = s
        if self.pos > self.hi:
            self.hi = self.pos
        return True


def cells_of(s):
    c, u, x = s
    return [1] * c + [0, 1] * u + [0, 0] + [1, 0] * x


def sim_next(T, s, limit=10 ** 7, to_halt=False):
    """Simulate from P tape s to the next P tape (or only to the halt), (tape or 'halt', steps)."""
    cells = cells_of(s)
    sim = Sim(cells, F, 4 * len(cells) + 800)
    for k in range(limit):
        if not sim.step(T):
            return "halt", k + 1
        if not to_halt:
            f = sim.family()
            if f:
                return canon(f), k + 1
    return "?", limit


def main():
    T = table()
    bad = n = halts = 0
    small = {}
    for c in range(0, 16):
        for u in (2, 3):
            for x in range(1, 81):
                s = (c, u, x)
                if rule(s)[0] == "halt":
                    got, want = sim_next(T, s, to_halt=True), rule(s)
                else:
                    got, want = sim_next(T, s), expected(s)
                if c < 4 and x < 16:   # the ends are proved for x >= 16 only: report separately
                    small[s] = got == want
                    continue
                n += 1
                halts += want[0] == "halt"
                if got != want:
                    bad += 1; print("differs:", s, "simulated", got, "rule", want)
    print(f"rules grid: {n} tapes P(c, u, x), c <= 15, u = 2, 3, x <= 80 (ends: x >= 16; {halts} halting), "
          f"{bad} failures")
    print(f"  ends below x = 16 (not in Lean): the table also holds for {sum(small.values())} of {len(small)}",
          sorted(s for s, ok in small.items() if not ok))
    print(f"  in all {n + len(small)} tapes, {halts + sum(1 for s in small if rule(s)[0] == 'halt')} halting, "
          f"{bad + len(small) - sum(small.values())} failures")
    bad += len(small) - sum(small.values())

    N = 10 ** 8
    sim = Sim([], 0, 200000)
    sim.pos = sim.hi = sim.off
    s, acc, nv, bad2 = None, 0, 0, 0
    for k in range(N):
        if not sim.step(T):
            print("halted at", k + 1); bad2 += 1; break
        f = sim.family()
        if not f:
            continue
        if s is None:
            ok, acc = f == (3, 3, 5) and k + 1 == 139, 139
        else:
            tgt, st = expected(s)
            acc += st
            ok = tgt == canon(f) and acc == k + 1
        if not ok:
            bad2 += 1; print("run differs at step", k + 1, f, s, acc); acc = k + 1
        s, nv = f, nv + 1
    print(f"rules run: {nv} P tapes in the first {N:.0e} steps (last P{s}), step counts {'ok' if not bad2 else 'FAILED'}")

    # Worked example: P(6, 2, 16): a phase, then an end that halts.
    s, tot, path = (6, 2, 16), 0, []
    while s != "halt":
        s2, k = rule(s); path.append((s, k)); tot += k; s = s2
    sim = Sim(cells_of((6, 2, 16)), F, 2000)
    k = 1
    while sim.step(T):
        k += 1
    print("example:", path, "=", tot, "; simulated:", k)
    return bad + bad2


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
