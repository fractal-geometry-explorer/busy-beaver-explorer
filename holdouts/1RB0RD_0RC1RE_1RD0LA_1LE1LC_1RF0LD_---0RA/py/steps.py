"""The rule table of 1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA with exact step counts, against direct simulation.

Tape family (P of lean/Map.lean):
  P(m, n) = 0^inf (1011)^m 1^n (10)^3 A> 1 0^inf
Rules (the map `next` of lean/Map.lean), n = 3k + 3 + r, r < 3:
  0^inf A> 0^inf  --73-->                   P(0, 5)             (then P(0, 18), and P(14, 5) at step 1098)
  P(m+1, 3k+3)    --12k^2 + 101k + 182-->   P(m, 8k + 19)
  P(0,   3k+3)    --12k^2 + 77k + 158-->    P(2k + 4, 5)        (reset)
  P(m+2, 3k+4)    --12k^2 + 125k + 305-->   P(m, 8k + 29)
  P(1,   3k+4)    --12k^2 + 101k + 194-->   halt                (F reads 0)
  P(0,   3k+4)    --12k^2 + 101k + 184-->   P(0, 8k + 18)
  P(m+2, 3k+5)    --12k^2 + 149k + 434-->   P(m, 8k + 35)
  P(1,   3k+5)    --12k^2 + 125k + 362-->   P(2k + 8, 5)        (reset)
  P(0,   3k+5)    --12k^2 + 101k + 182-->   P(0, 8k + 18)
Each is the bouncer `loop` (k + 1 rounds of `cycle`, 6p + 37 steps each: 12k^2 + 61k + 49 in all) followed by the
pieces of lean/Rules.lean that `next_reach` uses (b1, b2, b3, z1, z2 + `finish` 42; reset; r1a, r1b, reset; h_pre).

usage: python3 py/steps.py     checks the rules and the step counts: a grid of P tapes, each simulated to the next
                               P tape or the halt, and every P tape of the first 10^8 steps from blank (about a minute)
"""
import re
import sys

M = "1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA"
A = 0
PAT = bytes([1, 0, 1, 0, 1, 0])
WORDS = re.compile(rb"((?:\x01\x00\x01\x01)*)(\x01*)\x01\x00\x01\x00\x01\x00\x01")


def table():
    T = {}
    for s, grp in enumerate(M.split("_")):
        for b in (0, 1):
            t = grp[3 * b:3 * b + 3]
            T[(s, b)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


def rule(s):
    """P(m, n) -> (next (m', n') or 'halt', steps); n >= 3."""
    m, n = s
    k, r = (n - 3) // 3, (n - 3) % 3
    L = 12 * k * k + 61 * k + 49
    if r == 0:
        return ((2 * k + 4, 5), L + 16 * k + 109) if m == 0 else ((m - 1, 8 * k + 19), L + 40 * k + 133)
    if r == 1:
        if m == 0:
            return (0, 8 * k + 18), L + 40 * k + 135
        if m == 1:
            return "halt", L + 40 * k + 145
        return (m - 2, 8 * k + 29), L + 64 * k + 256
    if m == 0:
        return (0, 8 * k + 18), L + 40 * k + 133
    if m == 1:
        return (2 * k + 8, 5), L + 64 * k + 313
    return (m - 2, 8 * k + 35), L + 88 * k + 385


class Sim:
    def __init__(self, cells, pos, st, size):
        self.off = size // 4
        self.t = bytearray(size)
        self.t[self.off:self.off + len(cells)] = bytes(cells)
        self.pos, self.st = self.off + pos, st
        self.n1 = sum(cells)
        self.rm = self.off + max([i for i, c in enumerate(cells) if c], default=-self.off)

    def family(self):
        """P(m, n) if the machine is at one now, else None."""
        t, p = self.t, self.pos
        if self.st != A or p != self.rm or not t[p]:
            return None
        if bytes(t[p - 6:p]) != PAT:
            return None
        q = p - 6
        while t[q] or t[q - 1]:      # inside the written part no two 0s are adjacent
            q -= 1
        mt = WORDS.fullmatch(bytes(t[q + 1:p + 1]))
        if not mt:
            return None
        m, n = len(mt.group(1)) // 4, len(mt.group(2))
        return (m, n) if 3 * m + n + 4 == self.n1 else None

    def step(self, T):
        t, p = self.t, self.pos
        tr = T[(self.st, t[p])]
        if tr is None:
            return False
        w, d, s = tr
        if w != t[p]:
            t[p] = w
            self.n1 += 1 if w else -1
            if w and p > self.rm:
                self.rm = p
            elif not w and p == self.rm:
                q = p
                while q > 0 and not t[q]:
                    q -= 1
                self.rm = q
        self.pos += d; self.st = s
        return True


def cells_of(s):
    m, n = s
    c = [1, 0, 1, 1] * m + [1] * n + [1, 0] * 3 + [1]
    return c, len(c) - 1, A


def sim_next(T, s, limit=10 ** 7, to_halt=False):
    cells, pos, st = cells_of(s)
    sim = Sim(cells, pos, st, 8 * len(cells) + 800)
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
    for m in range(0, 21):
        for nn in range(3, 91):
            s = (m, nn)
            got, want = sim_next(T, s), rule(s)
            n += 1
            halts += want[0] == "halt"
            if got != want:
                bad += 1; print("differs:", s, "simulated", got, "rule", want)
    print(f"rules grid: {n} tapes P(m, n), m <= 20, 3 <= n <= 90 ({halts} halting), {bad} failures")

    N = 10 ** 8
    sim = Sim([0], 0, 0, 200000)
    sim.rm = 0
    s, acc, nv, bad2 = None, 0, 0, 0
    for k in range(N):
        if not sim.step(T):
            print("halted at", k + 1); bad2 += 1; break
        f = sim.family()
        if not f:
            continue
        if s is None:
            ok, acc = f == (0, 5) and k + 1 == 73, 73
        else:
            tgt, st = rule(s)
            acc += st
            ok = tgt == f and acc == k + 1
        if not ok:
            bad2 += 1; print("run differs at step", k + 1, f, s, acc); acc = k + 1
        s, nv = f, nv + 1
    print(f"rules run: {nv} P tapes in the first {N:.0e} steps (last P{s}), step counts {'ok' if not bad2 else 'FAILED'}")

    s, tot, path = (3, 7), 0, []
    while s != "halt":
        s2, k = rule(s); path.append((s, k)); tot += k; s = s2
    print("example:", path, "=", tot, "; simulated:", sim_total(T, (3, 7)))
    return bad + bad2


def sim_total(T, s):
    cells, pos, st = cells_of(s)
    sim = Sim(cells, pos, st, 4000)
    k = 1
    while sim.step(T):
        k += 1
    return k


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
