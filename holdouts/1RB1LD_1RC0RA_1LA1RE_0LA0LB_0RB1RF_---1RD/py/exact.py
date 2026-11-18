"""The rule table of the explainer ("Exact tapes, exact step counts") checked against direct simulation.

usage: python3 py/exact.py [STEPS]     (default STEPS = 10000000: the run from blank tape is followed that far)

Families (lean/Model.lean `Xc`, `Yc`, `Zc`; real counts as in the README):
    X(a, b, c) = 0^inf 1^a 0  (10)^b 1 D> 0 1^c 0^inf
    Y(a, b, c) = 0^inf 1^a 00 (10)^b 1 D> 0 1^c 0^inf
    Z(a, c)    = 0^inf 1^a 0 D> 0 1^c 0^inf
`rule` is `single` of py/orbit.py (the rules of lean/Rules.lean with their step counts), except that the halt
Z(a, 2) is counted up to and including the halting transition (5 + 1 steps).  Checked: (a) a grid of tapes of each
family, each run for exactly the claimed number of steps and compared cell by cell with the claimed target (or:
halts at exactly that step); (b) the run from blank tape: every tape the rules predict in the first STEPS steps, at
its predicted step, is the machine's configuration then."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from orbit import single, HALT  # noqa: E402

MACHINE = "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD"

# ---- direct simulation on exact tapes (shared shape of the py/exact.py scripts) ----
# A configuration is (left, state, right): the tape reads left + right, the head reads right[0] (a blank cell if
# right is empty), everything outside is 0.  Words are strings of '0'/'1'.

def table(name):
    T = {}
    for i, part in enumerate(name.split('_')):
        for r in (0, 1):
            t = part[3 * r:3 * r + 3]
            T[(i, r)] = None if t[2] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return T


def norm(cfg):
    """A canonical form: (word without blank ends, head index, state); the head cell is kept even if blank."""
    left, st, right = cfg
    if not right:
        right = '0'
    w, h = left + right, len(left)
    a = 0
    while a < h and w[a] == '0':
        a += 1
    b = len(w)
    while b > h + 1 and w[b - 1] == '0':
        b -= 1
    return (w[a:b], h - a, st if isinstance(st, int) else ord(st) - 65)


class Run:
    """A running machine on a list tape that grows on both sides."""

    def __init__(self, T, cfg):
        w, h, st = norm(cfg)
        self.T, self.pad = T, 64
        self.tape = [0] * self.pad + [int(c) for c in w] + [0] * self.pad
        self.pos, self.st = self.pad + h, st

    def run(self, n):
        """n steps; returns None, or the step number (1-based, the halting transition counted) at which it halted."""
        T, tape, pos, st = self.T, self.tape, self.pos, self.st
        for k in range(n):
            if pos < 0 or pos >= len(tape):
                g = len(tape)
                if pos < 0:
                    tape[:0] = [0] * g; pos += g
                else:
                    tape.extend([0] * g)
            t = T[(st, tape[pos])]
            if t is None:
                self.tape, self.pos, self.st = tape, pos, st
                return k + 1
            tape[pos] = t[0]; pos += t[1]; st = t[2]
        self.tape, self.pos, self.st = tape, pos, st
        return None

    def cfg(self):
        if self.pos < 0:
            self.tape[:0] = [0] * -self.pos; self.pos = 0
        if self.pos >= len(self.tape):
            self.tape.extend([0] * (self.pos - len(self.tape) + 1))
        w = ''.join(map(str, self.tape))
        return norm((w[:self.pos], self.st, w[self.pos:]))


def check_rule(T, cfg, n, target):
    """`cfg --n--> target` exactly (target None: the n-th step is the halting transition)."""
    r = Run(T, cfg)
    h = r.run(n)
    if target is None:
        return h == n
    return h is None and r.cfg() == norm(target)


# ---- the families and the rules ----

def tape(f):
    if f[0] == 'X':
        _, a, b, c = f
        return ('1' * a + '0' + '10' * b + '1', 'D', '0' + '1' * c)
    if f[0] == 'Y':
        _, a, b, c = f
        return ('1' * a + '00' + '10' * b + '1', 'D', '0' + '1' * c)
    _, a, c = f
    return ('1' * a + '0', 'D', '0' + '1' * c)


def rule(f):
    """(next tape or None = halt, steps)."""
    g, s = single(f)
    return (None, s + 1) if g == HALT else (g, s)


def main():
    T = table(MACHINE)
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 7
    grid = [('X', a, b, c) for a in range(0, 31) for b in range(0, 21) for c in range(1, 21) if a or b or c > 1]
    grid += [('Y', a, b, c) for a in range(3, 31) for b in range(0, 21) for c in range(1, 21)]
    grid += [('Z', a, c) for a in range(3, 41) for c in range(1, 31)]
    n = bad = halts = 0
    for f in grid:
        g, s = rule(f)
        n += 1
        halts += g is None
        if not check_rule(T, tape(f), s, None if g is None else tape(g)):
            bad += 1
            print("differs:", f, "->", g, s)
    print(f"grid: {n} tapes ({halts} halting), {bad} failures")
    # the run from blank tape: X(2, 0, 3) at step 29 (`blank_to_X`), then the rules
    run = Run(T, ('', 'A', ''))
    f, at, visits = ('X', 2, 0, 3), 29, 1
    if run.run(29) is not None or run.cfg() != norm(tape(f)):
        bad += 1; print("start differs")
    while True:
        g, s = rule(f)
        if g is None or at + s > steps:
            break
        if run.run(s) is not None or run.cfg() != norm(tape(g)):
            bad += 1
            print("run differs at step", at + s, g)
            break
        at += s; f = g; visits += 1
    print(f"run from blank tape: {visits} predicted tapes up to step {at:,} (of {steps:,}), "
          f"{'all equal' if not bad else 'FAILED'}; last {f}")
    return bad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
