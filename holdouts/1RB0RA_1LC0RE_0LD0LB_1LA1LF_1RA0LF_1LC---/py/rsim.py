"""Exact fast simulator of 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC--- on a run-length tape.

The tape is stored as maximal runs of alternating cells (start bit, length) on each side of the head.  Besides single
machine steps it makes the three sweep moves proved in lean/Rules.lean: A crossing 4k alternating cells to the right
(flipping them, `a_right`), B crossing 2n cells `(01)^n` to the left and C crossing `(10)^n` (`b_left`, `c_left`).
So it is the machine itself, only faster: tested against a plain cell simulator (same step of every visit of the left
end in state A over the first 4*10^9 steps; see the README).

usage (from the repo root):
  python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/rsim.py STEPS [EVERY]
prints every EVERY-th visit of the left end in state A (the start of a trip): visit number, step, the run lengths of
the tape (left to right, the first run starting with 0); and HALT if the machine halts.
"""
import sys
import time

M = "1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---"
A, B, C, D, E, F = range(6)


def parse(m):
    t = {}
    for s, part in enumerate(m.split("_")):
        for r in range(2):
            x = part[3 * r:3 * r + 3]
            t[(s, r)] = None if x[2] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65)
    return t


T = parse(M)


class Sim:
    def __init__(self):
        self.L = []   # runs [start bit, length] left of the head, left to right (last = next to the head)
        self.R = []   # runs right of the head, right to left (last = next to the head)
        self.h = 0
        self.st = A
        self.steps = 0
        self.pos = self.lo = self.hi = 0

    def pushL(self, b, n):
        L = self.L
        if L and (L[-1][0] ^ ((L[-1][1] - 1) & 1)) != b:
            L[-1][1] += n
        else:
            L.append([b, n])

    def pushR(self, b, n):
        R = self.R
        e = b ^ ((n - 1) & 1)
        if R and R[-1][0] != e:
            R[-1][0] = b
            R[-1][1] += n
        else:
            R.append([b, n])

    def popL(self):
        if not self.L:
            return 0
        r = self.L[-1]
        e = r[0] ^ ((r[1] - 1) & 1)
        r[1] -= 1
        if r[1] == 0:
            self.L.pop()
        return e

    def popR(self):
        if not self.R:
            return 0
        r = self.R[-1]
        b = r[0]
        r[0] ^= 1
        r[1] -= 1
        if r[1] == 0:
            self.R.pop()
        return b

    def step(self):
        """One move: a sweep move when one applies, else one machine step.  False on a halt."""
        st, h = self.st, self.h
        if st == A and self.R and self.R[-1][0] != h and self.R[-1][1] >= 4:      # a_right
            r = self.R[-1]
            k = r[1] // 4
            self.pushL(1 - h, 4 * k)
            r[1] -= 4 * k
            if r[1] == 0:
                self.R.pop()
            self.steps += 4 * k
            self.pos += 4 * k
            self.hi = max(self.hi, self.pos)
            return True
        if (st == B and h == 0 or st == C and h == 1) and self.L:                  # b_left, c_left
            r = self.L[-1]
            if (r[0] ^ ((r[1] - 1) & 1)) == 1 - h and r[1] >= 2:
                n = r[1] // 2
                r[1] -= 2 * n
                if r[1] == 0:
                    self.L.pop()
                self.pushR(h, 2 * n)
                self.steps += 2 * n
                self.pos -= 2 * n
                self.lo = min(self.lo, self.pos)
                return True
        t = T[(st, h)]
        if t is None:
            return False
        w, d, s2 = t
        if d == 1:
            self.pushL(w, 1)
            self.h = self.popR()
        else:
            self.pushR(w, 1)
            self.h = self.popL()
        self.st = s2
        self.steps += 1
        self.pos += d
        self.lo = min(self.lo, self.pos)
        self.hi = max(self.hi, self.pos)
        return True

    def at_left(self):
        return self.st == A and self.pos == self.lo

    def runs(self):
        """Run lengths of the visited tape, left to right (meant for the head at the left end)."""
        out, cur = [], None
        for b, n in [list(x) for x in self.L] + [[self.h, 1]] + [list(x) for x in reversed(self.R)]:
            if cur and (cur[0] ^ ((cur[1] - 1) & 1)) != b:
                cur[1] += n
            else:
                if cur:
                    out.append(cur[1])
                cur = [b, n]
        out.append(cur[1])
        return out


def main():
    n = float(sys.argv[1])
    every = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    s, visits, t0 = Sim(), 0, time.time()
    while s.steps < n:
        if not s.step():
            print("HALT after", s.steps + 1, "steps")
            return
        if s.at_left():
            visits += 1
            if every and visits % every == 0:
                print(visits, s.steps, s.runs(), flush=True)
    print(f"no halt in {s.steps} steps; {visits} trips; {s.hi - s.lo + 1} cells; {time.time() - t0:.0f} s")


if __name__ == "__main__":
    main()
