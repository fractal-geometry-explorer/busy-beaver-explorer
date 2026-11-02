"""A fast simulator: the tape cut into blocks of k cells and run-length coded (a "macro machine").

The head sits between two blocks, facing one of them.  One macro step runs the machine on the block it faces until
the head leaves the block; the result (new block, state, side it left by, steps) depends only on the state, the
block and the side, so it is cached.  When the head leaves on the far side in the state it came in with, it would
do the same on every copy of that block in the run ahead, so the whole run is crossed at once.  A machine whose
sweeps cross long runs of one word (here the pairs `10` of 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---) then takes
a number of macro steps of the order of the number of runs, not of cells.

Exact: the step count and the tape are those of the plain simulator (`bbtools.machine.Run`) at the end of each
macro step, which tools/tests/test_tools.py checks cell for cell.  Step counts follow the bbchallenge convention
(the halting transition counts).

usage: python3 -m bbtools.macro MACHINE K STEPS      progress and the run-length tape at powers of ten
"""
import sys

from .machine import Machine, STATES


class MacroRun:
    def __init__(self, machine, k):
        self.m = Machine.parse(machine) if isinstance(machine, str) else machine
        self.k = k
        self.cache = {}
        zero = (0,) * k
        # stacks of [block, count], nearest the head last; the bottom entry is blank tape, endless
        self.left = [[zero, 1]]
        self.right = [[zero, 1]]
        self.state, self.dir = 0, 1     # dir +1: the head faces the right stack
        self.pos = 0                    # the cell boundary the head sits on
        self.steps = 0
        self.msteps = 0
        self.halted = False

    def _trans(self, q, x, d):
        key = (q, x, d)
        r = self.cache.get(key)
        if r is not None:
            return r
        k, c, n, seen = self.k, list(x), 0, set()
        i = 0 if d == 1 else k - 1
        while 0 <= i < k:
            t = self.m.table[q][c[i]]
            if t is None:
                r = ("halt", n + 1, tuple(c), i, q)
                break
            if (q, i, tuple(c)) in seen:
                r = ("loop",)
                break
            seen.add((q, i, tuple(c)))
            c[i], mv, q = t
            i += mv
            n += 1
        else:
            r = (q, tuple(c), 1 if i >= k else -1, n)
        self.cache[key] = r
        return r

    @staticmethod
    def _push(st, x, c):
        if st[-1][0] == x and len(st) > 1:
            st[-1][1] += c
        else:
            st.append([x, c])

    def step(self):
        """One macro step; False once the machine has halted (or loops inside a block, which raises)."""
        if self.halted:
            return False
        q, d = self.state, self.dir
        front, back = (self.right, self.left) if d == 1 else (self.left, self.right)
        top = front[-1]
        x = top[0]
        if len(front) > 1:
            top[1] -= 1
            if top[1] == 0:
                front.pop()
        r = self._trans(q, x, d)
        if r[0] == "halt":
            self.halted = True
            self.steps += r[1]
            self.halt_info = r
            # leave the half-run block on the tape as it was when the machine stopped
            self._push(front, r[2], 1)
            return False
        if r[0] == "loop":
            raise RuntimeError("the machine loops inside one block")
        q2, y, d2, n = r
        self.msteps += 1
        if q2 == q and d2 == d:
            c = 1
            if len(front) > 1 and front[-1][0] == x:
                c += front[-1][1]
                front.pop()
            self.steps += c * n
            self._push(back, y, c)
            self.pos += d * c * self.k
        else:
            self.steps += n
            if d2 == d:
                self.pos += d * self.k
            self._push(self.left if d2 == 1 else self.right, y, 1)
        self.state, self.dir = q2, d2
        return True

    def run(self, steps):
        """Macro steps until at least `steps` machine steps have run (or the machine halts)."""
        while self.steps < steps and self.step():
            pass
        return self

    def head(self):
        """The cell the head reads next."""
        return self.pos if self.dir == 1 else self.pos - 1

    def cells(self):
        """{position: symbol} for every cell written so far (including blanks the machine wrote)."""
        out, k = {}, self.k
        p = self.pos
        for x, c in reversed(self.left[1:]):
            for _ in range(c):
                p -= k
                for i, b in enumerate(x):
                    out[p + i] = b
        p = self.pos
        for x, c in reversed(self.right[1:]):
            for _ in range(c):
                for i, b in enumerate(x):
                    out[p + i] = b
                p += k
        return out

    def runs(self):
        """The tape as run-length blocks, left to right: (left runs, right runs), each a list of (word, count)."""
        lw = [("".join(map(str, x)), c) for x, c in self.left[1:]]
        rw = [("".join(map(str, x)), c) for x, c in reversed(self.right[1:])]
        return lw, rw

    def __str__(self):
        lw, rw = self.runs()
        arrow = ">" if self.dir == 1 else "<"
        side = f"{STATES[self.state]}{arrow}"
        return " ".join(f"{w}^{c}" for w, c in lw) + f" {side} " + " ".join(f"{w}^{c}" for w, c in rw)


def main(argv):
    if len(argv) != 3:
        sys.exit(__doc__)
    machine, k, steps = argv[0], int(argv[1]), int(float(argv[2]))
    r = MacroRun(machine, k)
    nxt = 10
    while r.steps < steps:
        if not r.step():
            print(f"halts after {r.steps} steps")
            return
        if r.steps >= nxt:
            print(f"{r.steps:.3e} steps  {r.msteps} macro steps  {len(r.left) + len(r.right) - 2} runs")
            nxt *= 10
    print(r)


if __name__ == "__main__":
    main(sys.argv[1:])
