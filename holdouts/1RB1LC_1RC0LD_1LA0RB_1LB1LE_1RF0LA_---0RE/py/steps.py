"""The rule table of 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE with exact step counts, against direct simulation.

Tape family (X of lean/Orbit.lean):
  X(K, m) = 0^inf D> (10)^K 1^m 0^inf
Rules (the map `phase` of lean/Orbit.lean, one step of its recursion per row; m even, K >= 1):
  0^inf A> 0^inf  --21-->                 X(1, 6)          (then X(1, 22) at step 208)
  X(K, m)         --4K^2 + 22K + 26-->    X(2K + 4, m - 2K - 6)      m >= 2K + 6       (doubling)
  X(K, m)         --3m^2 + 4Km + 9m + 1-->  X(1, 2K + 3m + 2)        2 <= m < 2K + 6   (end of round)
  X(K, 0)         --2K + 3-->             halt                                         (F reads 0)

usage: python3 py/steps.py     checks the rules and the step counts: a grid of X tapes, each simulated to the next
                               X tape or the halt, and every X tape of the first 10^8 steps from blank (about a minute)
"""
import sys

M = "1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE"
D = 3


def table():
    T = {}
    for s, grp in enumerate(M.split("_")):
        for r in (0, 1):
            t = grp[3 * r:3 * r + 3]
            T[(s, r)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


def rule(s):
    """X(K, m) -> (next X tape or 'halt', steps)."""
    K, m = s
    if m == 0:
        return "halt", 2 * K + 3
    if m >= 2 * K + 6:
        return (2 * K + 4, m - 2 * K - 6), 4 * K * K + 22 * K + 26
    return (1, 2 * K + 3 * m + 2), 3 * m * m + 4 * K * m + 9 * m + 1


class Sim:
    """Direct simulation on a bytearray, keeping the leftmost 1 and the number of 1s."""

    def __init__(self, cells, st, size):
        self.off = size // 2
        self.t = bytearray(size)
        self.t[self.off:self.off + len(cells)] = bytes(cells)
        self.pos, self.st = self.off, st
        self.n1 = sum(cells)
        self.lm = self.off + cells.index(1) if 1 in cells else size

    def family(self):
        """X(K, m) if the machine is now at one, else None."""
        t, p = self.t, self.pos
        if self.st != D or p != self.lm:
            return None
        q, K = p, 0
        while t[q] == 1 and t[q + 1] == 0:
            K += 1; q += 2
        m = 0
        while t[q]:
            m += 1; q += 1
        if K == 0 or K + m != self.n1:
            return None
        return (K, m)

    def step(self, T):
        t, p = self.t, self.pos
        tr = T[(self.st, t[p])]
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
                    while not t[q] and self.n1:
                        q += 1
                    self.lm = q if self.n1 else len(t)
        self.pos += d; self.st = s
        return True


def cells_of(s):
    K, m = s
    return [1, 0] * K + [1] * m


def sim_next(T, s, limit=10 ** 7):
    cells = cells_of(s)
    sim = Sim(cells, D, 4 * len(cells) + 400)
    for k in range(limit):
        if not sim.step(T):
            return "halt", k + 1
        f = sim.family()
        if f:
            return f, k + 1
    return "?", limit


def main():
    T = table()
    bad = n = halts = 0
    for K in range(1, 41):
        for m in range(0, 121, 2):
            s = (K, m)
            got, want = sim_next(T, s), rule(s)
            n += 1
            halts += want[0] == "halt"
            if got != want:
                bad += 1; print("differs:", s, "simulated", got, "rule", want)
    print(f"rules grid: {n} tapes X(K, m), 1 <= K <= 40, m even <= 120 ({halts} halting), {bad} failures")

    N = 10 ** 8
    sim = Sim([0], 0, 60000)
    s, acc, nv, bad2 = None, 0, 0, 0
    for k in range(N):
        if not sim.step(T):
            print("halted at", k + 1); bad2 += 1; break
        f = sim.family()
        if not f:
            continue
        if s is None:
            ok, acc = f == (1, 6) and k + 1 == 21, 21
        else:
            tgt, st = rule(s)
            acc += st
            ok = tgt == f and acc == k + 1
        if not ok:
            bad2 += 1; print("run differs at step", k + 1, f, s, acc); acc = k + 1
        s, nv = f, nv + 1
    print(f"rules run: {nv} X tapes in the first {N:.0e} steps (last X{s}), step counts {'ok' if not bad2 else 'FAILED'}")

    # Worked example: X(1, 26) halts (26 = 10*2^2 - 2*2 - 10).
    s, tot, path = (1, 26), 0, []
    while s != "halt":
        s2, k = rule(s); path.append(k); tot += k; s = s2
    sim = Sim(cells_of((1, 26)), D, 1000)
    k = 1
    while sim.step(T):
        k += 1
    print("example X(1, 26):", " + ".join(map(str, path)), "=", tot, "; simulated:", k)
    return bad + bad2


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
