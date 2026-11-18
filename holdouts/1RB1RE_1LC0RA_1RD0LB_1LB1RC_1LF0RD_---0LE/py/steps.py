"""The rule table of 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE with exact step counts, against direct simulation.

Tape families (S and V of lean/Phase2.lean and lean/Phase1.lean):
  S(n)       = 0^inf C> 0 (10)^n 1 0^inf
  V(K, i, m) = 0^inf 1^(2K) 0 A> 0 (10)^(2i) 111 0 (10)^m 1 0^inf
Rules (the map `ph` of lean/Phase1.lean, one step of its recursion per row):
  0^inf A> 0^inf    --4-->                         S(1)
  S(n + 1)          --2n + 17-->                   V(n, 0, 0)
  V(K+1, i, m+1)    --8i + 12-->                   V(K, i + 1, m)          (bounce)
  V(K+4, i, 0)      --24i + 62-->                  V(K, 0, 2i + 5)         (refill)
  V(0, i, m)        --16i^2 + 8im + 72i + 12m + 72-->  S(4i + m + 7)       (rules b3 and e0)
  V(1, i, 0)        --16i^2 + 104i + 152-->        S(4i + 10)              (e1)
  V(2, i, 0)        --24i + 57-->                  halt                    (e2, F reads 0)
  V(3, i, 0)        --32i + 98-->                  S(2i + 9)               (e3)

usage: python3 py/steps.py     checks the rules and the step counts: a grid of S and V tapes, each simulated to the
                               next S or V tape or the halt, and every S/V tape of the first 10^8 steps from blank (under a minute)
"""
import sys

M = "1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE"
A, C = 0, 2


def table():
    T = {}
    for s, grp in enumerate(M.split("_")):
        for r in (0, 1):
            t = grp[3 * r:3 * r + 3]
            T[(s, r)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


def rule(s):
    """('S', n) or ('V', K, i, m) -> (next S or V tape, or 'halt'; steps)."""
    if s[0] == "S":
        n = s[1] - 1
        return ("V", n, 0, 0), 2 * n + 17
    _, K, i, m = s
    if K >= 1 and m >= 1:
        return ("V", K - 1, i + 1, m - 1), 8 * i + 12
    if K == 0:
        return ("S", 4 * i + m + 7), 16 * i * i + 8 * i * m + 72 * i + 12 * m + 72
    if K == 1:
        return ("S", 4 * i + 10), 16 * i * i + 104 * i + 152
    if K == 2:
        return "halt", 24 * i + 57
    if K == 3:
        return ("S", 2 * i + 9), 32 * i + 98
    return ("V", K - 4, 0, 2 * i + 5), 24 * i + 62


class Sim:
    def __init__(self, cells, pos, st, size):
        self.off = size // 2
        self.t = bytearray(size)
        self.t[self.off:self.off + len(cells)] = bytes(cells)
        self.pos, self.st = self.off + pos, st
        self.n1 = sum(cells)

    def pairs(self, q):
        """Number of pairs 10 starting at q (greedy), and the index after them."""
        t, k = self.t, 0
        while t[q] == 1 and t[q + 1] == 0:
            k += 1; q += 2
        return k, q

    def family(self):
        t, p = self.t, self.pos
        if t[p]:
            return None
        if self.st == C:
            if any(t[p - 40:p]) or t[p - 1]:
                return None
            k, q = self.pairs(p + 1)
            # 0 (10)^n 1 then blank: greedy pairs swallow the last 1 with the blank after it
            if k >= 1 and k == self.n1 and not t[q] and not t[q + 1]:
                return ("S", k - 1)
            return None
        if self.st == A and not t[p - 1]:
            q, k1 = p - 2, 0
            while t[q]:
                k1 += 1; q -= 1
            if k1 % 2:
                return None
            c1, q = self.pairs(p + 1)
            if c1 % 2 or not (t[q] and t[q + 1] and t[q + 2] and not t[q + 3]):
                return None
            P2, q2 = self.pairs(q + 4)
            if P2 >= 1 and k1 + c1 + 3 + P2 == self.n1 and not t[q2]:
                return ("V", k1 // 2, c1 // 2, P2 - 1)
        return None

    def step(self, T):
        t, p = self.t, self.pos
        tr = T[(self.st, t[p])]
        if tr is None:
            return False
        w, d, s = tr
        self.n1 += w - t[p]
        t[p] = w
        self.pos += d; self.st = s
        return True


def cells_of(s):
    if s[0] == "S":
        return [0] + [1, 0] * s[1] + [1], 0, C
    _, K, i, m = s
    return [1] * (2 * K) + [0, 0] + [1, 0] * (2 * i) + [1, 1, 1, 0] + [1, 0] * m + [1], 2 * K + 1, A


def sim_next(T, s, limit=10 ** 7):
    cells, pos, st = cells_of(s)
    sim = Sim(cells, pos, st, 4 * len(cells) + 600)
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
    starts = [("S", k) for k in range(1, 301)] + \
        [("V", K, i, m) for K in range(0, 21) for i in range(0, 16) for m in range(0, 21)]
    for s in starts:
        got, want = sim_next(T, s), rule(s)
        n += 1
        halts += want[0] == "halt"
        if got != want:
            bad += 1; print("differs:", s, "simulated", got, "rule", want)
    print(f"rules grid: {n} tapes (300 S(n), n <= 300; V(K, i, m), K <= 20, i <= 15, m <= 20; {halts} halting), "
          f"{bad} failures")

    N = 10 ** 8
    sim = Sim([0], 0, 0, 40000)
    s, acc, nv, bad2 = None, 0, 0, 0
    for k in range(N):
        if not sim.step(T):
            print("halted at", k + 1); bad2 += 1; break
        f = sim.family()
        if not f:
            continue
        if s is None:
            ok, acc = f == ("S", 1) and k + 1 == 4, 4
        else:
            tgt, st = rule(s)
            acc += st
            ok = tgt == f and acc == k + 1
        if not ok:
            bad2 += 1; print("run differs at step", k + 1, f, s, acc); acc = k + 1
        s, nv = f, nv + 1
    print(f"rules run: {nv} S/V tapes in the first {N:.0e} steps (last {s}), step counts {'ok' if not bad2 else 'FAILED'}")

    # Worked example: S(3) halts (3 = c_1).
    s, tot, path = ("S", 3), 0, []
    while s != "halt":
        s2, k = rule(s); path.append(k); tot += k; s = s2
    cells, pos, st = cells_of(("S", 3))
    sim = Sim(cells, pos, st, 1000)
    k = 1
    while sim.step(T):
        k += 1
    print("example S(3):", " + ".join(map(str, path)), "=", tot, "; simulated:", k)
    return bad + bad2


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
