"""The rule table of 1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB with exact step counts, against direct simulation.

Tape families (A as on the bbchallenge wiki page of the machine, which writes it `0^inf <E 1^x 0 1^y 0^inf`):
  P(n)    = 0^inf 1^n B> 0^inf
  A(b, c) = 0^inf E> 0 1^b 0 1^c 0^inf          (X(0, b, c) of lean/Macro.lean)
Rules (the map g of lean/Macro.lean, one step of its recursion per row):
  0^inf A> 0^inf  --1-->              P(1)               (then A(0, 2), and P(4) at step 9)
  P(n)            --n+3-->            A(n-1, 2)              n >= 1
  A(2i+3, c)      --2i^2+10i+13-->    A(i, c+i+4)
  A(1, c)         --7-->              halt
  A(2i+2, c)      --6i^2+19i+11+c(4i+7)-->   P(c+3i+5)
  A(0, 2j)        --2j+2-->           P(2j+2)
  A(0, 2j+1)      --4j+7-->           A(2j+2, 1)             (through Q(2j+3) = 0^inf 1^(2j+3) F> 0^inf)

usage: python3 py/steps.py        checks the rules and the step counts: a grid of P and A tapes, each simulated to the
                                  next P or A tape or the halt, and every P/A visit of the first 10^8 steps from blank (a minute)
"""
import sys

M = "1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB"


def table():
    T = {}
    for s, grp in enumerate(M.split("_")):
        for r in (0, 1):
            t = grp[3 * r:3 * r + 3]
            T[(s, r)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


B, E = 1, 4


def rule(s):
    """One rule: ('P', n) or ('A', b, c) -> (target or 'halt', steps)."""
    if s[0] == "P":
        n = s[1]
        return ("A", n - 1, 2), n + 3
    _, b, c = s
    if b == 1:
        return "halt", 7
    if b % 2 == 1:
        i = (b - 3) // 2
        return ("A", i, c + i + 4), 2 * i * i + 10 * i + 13
    if b > 0:
        i = (b - 2) // 2
        return ("P", c + 3 * i + 5), 6 * i * i + 19 * i + 11 + c * (4 * i + 7)
    j = c // 2
    return (("P", c + 2), c + 2) if c % 2 == 0 else (("A", c + 1, 1), 4 * j + 7)


class Sim:
    """Direct simulation; reports each P or A tape it passes through."""

    def __init__(self, cells, pos, st, size):
        self.off = size // 2
        self.t = bytearray(size)
        for i, x in enumerate(cells):
            self.t[self.off + i] = x
        self.pos, self.st = self.off + pos, st
        ones = [i for i in range(size) if self.t[i]]
        self.n1 = len(ones)
        self.lm = ones[0] if ones else size
        self.rm = ones[-1] if ones else -1

    def family(self):
        t, p = self.t, self.pos
        if t[p]:
            return None
        if self.st == B and self.rm == p - 1 and self.n1 == p - self.lm:
            return ("P", self.n1)
        if self.st == E and self.lm > p:
            q = p + 1
            b = 0
            while t[q]:
                b += 1; q += 1
            q += 1
            c = 0
            while t[q]:
                c += 1; q += 1
            if self.n1 == b + c:
                return ("A", b, c)
        return None

    def step(self, T):
        """One step; False if it is the halting step."""
        t, p = self.t, self.pos
        tr = T[(self.st, t[p])]
        if tr is None:
            return False
        w, d, s = tr
        if w != t[p]:
            t[p] = w
            if w:
                self.n1 += 1
                self.lm = min(self.lm, p); self.rm = max(self.rm, p)
            else:
                self.n1 -= 1
                if p == self.lm:
                    q = p
                    while q <= self.rm and not t[q]:
                        q += 1
                    self.lm = q
                if p == self.rm:
                    q = p
                    while q >= self.lm and not t[q]:
                        q -= 1
                    self.rm = q
        self.pos += d; self.st = s
        return True


def cells_of(s):
    if s[0] == "P":
        return [1] * s[1], s[1], B
    _, b, c = s
    return [0] + [1] * b + [0] + [1] * c, 0, E


def sim_next(T, s, limit=10 ** 7):
    """Simulate from tape s to the next P or A tape, or the halt: (target or 'halt', steps)."""
    cells, pos, st = cells_of(s)
    sim = Sim(cells, pos, st, 4 * len(cells) + 400)
    for k in range(limit):
        if not sim.step(T):
            return "halt", k + 1
        f = sim.family()
        if f:
            return f, k + 1
    return "?", limit


def main():
    T = table()
    bad = n = 0
    starts = [("P", m) for m in range(1, 301)] + [("A", b, c) for b in range(0, 61) for c in range(0, 61)]
    for s in starts:
        got = sim_next(T, s)
        want = rule(s)
        n += 1
        if got != want:
            bad += 1
            print("differs:", s, "simulated", got, "rule", want)
    print(f"rules grid: {n} tapes ({n - 300} A, 300 P), {bad} failures")
    halts = sum(1 for s in starts if rule(s)[0] == "halt")
    print(f"  of which {halts} halting instances A(1, c)")

    # The run from blank tape: every P/A tape of the first N steps, the cumulative step counts against the rules.
    N = 10 ** 8
    sim = Sim([], 0, 0, 40000)
    s, acc, nv, bad2 = None, 0, 0, 0
    for k in range(N):
        if not sim.step(T):
            print("halted at", k + 1); bad2 += 1; break
        f = sim.family()
        if not f:
            continue
        if s is None:
            ok = f == ("P", 1) and k + 1 == 1
            acc = 1
        else:
            tgt, st = rule(s)
            acc += st
            ok = tgt == f and acc == k + 1
        if not ok:
            bad2 += 1; print("run differs at step", k + 1, f, s, acc); acc = k + 1
        s, nv = f, nv + 1
    print(f"rules run: {nv} P/A tapes in the first {N:.0e} steps (last {s}), step counts "
          f"{'ok' if not bad2 else 'FAILED'}")

    # Worked example: P(14) halts (14 + 2 = 16).
    s, tot, path = ("P", 14), 0, []
    while s != "halt":
        s2, k = rule(s); path.append(k); tot += k; s = s2
    print("example P(14):", " + ".join(map(str, path)), "=", tot, "; simulated:", sim_total(T, ("P", 14)))
    return bad + bad2


def sim_total(T, s):
    cells, pos, st = cells_of(s)
    sim = Sim(cells, pos, st, 1000)
    k = 0
    while sim.step(T):
        k += 1
    return k + 1


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
