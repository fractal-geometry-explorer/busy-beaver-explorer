"""The macro simulator of bbtools.macro with one more kind of chain step: a run crossed with a one-block context.

`bbtools.macro.MacroRun` crosses a whole run w^n at once when one block is crossed without leaving it,
`q> w -> w' q>`.  On this machine the head dips back into the block behind it while it crosses a block, so many
runs are crossed block by block.  `CtxMacroRun` adds the rule with the block c behind the head as context:

    c q> w  ->  x c q>      (the head stays inside the two blocks until it leaves on the far side, in state q)
    so  c q> w^n  ->  x^n c q>   in n*s steps        (and the mirror image for a head moving left)

The rule is found by running the machine on the two blocks (cached per (q, c, w, direction)); it is exact, and
`check()` compares the run cell for cell with the plain macro simulator.  The interface is MacroRun's, so
`bbtools.cycles.Accelerator` drives it unchanged.

usage: python3 ctxmacro.py check [MACHINE [K [STEPS]]]     compare with bbtools.macro (default: this machine, 12, 1e8)
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.macro import MacroRun  # noqa: E402

M = "1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC"


class CtxMacroRun(MacroRun):
    LIMIT = 4000        # steps inside the two blocks before a candidate rule is given up

    def __init__(self, machine, k):
        super().__init__(machine, k)
        self.cache2 = {}
        self.nctx = 0

    def _trans2(self, q, c, w, d):
        """(x, s) if `c q> w -> x c q>` in s steps (d = 1; mirrored for d = -1), else None."""
        key = (q, c, w, d)
        if key in self.cache2:
            return self.cache2[key]
        k = self.k
        cells = list(c + w) if d == 1 else list(w + c)
        i = k if d == 1 else k - 1
        q0, n, r = q, 0, None
        while 0 <= i < 2 * k and n < self.LIMIT:
            t = self.m.table[q][cells[i]]
            if t is None:
                break
            cells[i], mv, q = t
            i += mv
            n += 1
        else:
            if n < self.LIMIT and q == q0:
                if d == 1 and i >= 2 * k and tuple(cells[k:]) == c:
                    r = (tuple(cells[:k]), n)
                elif d == -1 and i < 0 and tuple(cells[:k]) == c:
                    r = (tuple(cells[k:]), n)
        self.cache2[key] = r
        return r

    def step(self):
        if self.halted:
            return False
        q, d = self.state, self.dir
        front, back = (self.right, self.left) if d == 1 else (self.left, self.right)
        if len(front) > 1 and front[-1][1] >= 2:
            w = front[-1][0]
            r1 = self._trans(q, w, d)
            if not (r1[0] == q and r1[2] == d):         # the plain chain step does not apply
                c = back[-1][0]
                r = self._trans2(q, c, w, d)
                if r is not None:
                    x, s = r
                    n = front[-1][1]
                    front.pop()
                    if len(back) > 1:                   # take one c off the back, put x^n and c back
                        back[-1][1] -= 1
                        if back[-1][1] == 0:
                            back.pop()
                    self._push(back, x, n)
                    self._push(back, c, 1)
                    self.steps += n * s
                    self.pos += d * n * self.k
                    self.msteps += 1
                    self.nctx += 1
                    return True
        return super().step()


def check(machine=M, k=12, steps=10 ** 8):
    """Run both simulators to the same step counts and compare the tapes, heads and states."""
    a, b = MacroRun(machine, k), CtxMacroRun(machine, k)
    t = 100
    while t <= steps:
        b.run(t)
        while a.steps < b.steps and a.step():
            pass
        ca = {p: v for p, v in a.cells().items() if v}
        cb = {p: v for p, v in b.cells().items() if v}
        if not (a.steps == b.steps and ca == cb and a.state == b.state and a.head() == b.head()):
            raise SystemExit(f"mismatch near {t} steps")
        print(f"{b.steps} steps: same tape ({len(cb)} ones), plain {a.msteps} macro steps, with context {b.msteps}")
        t *= 10
    print("ok")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "check":
        check(*([sys.argv[2]] if len(sys.argv) > 2 else []), *[int(float(x)) for x in sys.argv[3:5]])
    else:
        sys.exit(__doc__)
