"""The rule table of the explainer ("Exact tapes, exact step counts") checked against direct simulation.

usage: python3 py/exact.py [STEPS]     (default STEPS = 10000000: the run from blank tape is followed that far)

One family (lean/Reset.lean, `Ph`):  S_t(x, c) = 0^inf A> 1^x (01)^2 1^6 (01)^c 1^t 0 1 1 0^inf, t = 3 or 6.
`rule` is `next` of lean/Reset.lean (`next_map` of py/model.py) with the number of machine steps of each case; the
halt counts the halting transition too.  Checked: (a) a grid of tapes S_t(x, c), each run for exactly the claimed
number of steps and compared cell by cell with the claimed target (or: halts at exactly that step); (b) the run
from blank tape: every tape the rules predict in the first STEPS steps, at its predicted step, is the machine's
configuration then."""
import sys

MACHINE = "1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA"

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


# ---- the family and the rules ----

def tape(f):
    x, c, t = f
    return ('', 'A', '1' * x + '0101' + '111111' + '01' * c + '1' * t + '011')


# the constant K of the step count (3x^2 + 23x + K)/2 of a reset, by (c, t, x mod 4)
K01 = {(0, 3): (208, 332, 338, 356), (0, 6): (374, 392, 244, 368), (1, 3): (354, 372, 224, 348)}
# the reset after c = 1, t = 6: (39x^2 + 662x + K)/8 for x even, (39x^2 + 644x + K)/8 for x odd, K by x mod 4
K16 = (3304, 3141, 3416, 3029)


def rule(f):
    """(next tape or None = halt, steps): the cases of `next` (x >= 1)."""
    x, c, t = f
    if c >= 2:
        return (3 * x // 2 + 7, c - 2, t), (3 * x * x + 41 * x + (202 if x % 2 == 0 else 174)) // 2
    if c == 1 and t == 6:
        y = 3 * (x // 2) + 7 + x % 2
        return (3 * y // 2 + 4, 1, 3), (39 * x * x + (662 if x % 2 == 0 else 644) * x + K16[x % 4]) // 8
    s = (3 * x * x + 23 * x + K01[(c, t)][x % 4]) // 2
    if c == 0:
        b, t1, d = 3 * (x // 2) + 7 + t, 3, 5
    else:
        b, t1, d = 3 * (x // 2) + 7, 6, 3
    if x % 2 == 0:
        return (None if b % 2 == 0 else (4, (b - d) // 2, t1)), s
    return ((6, (b - d - 3) // 2, t1) if b % 2 == 0 else (5, (b - d) // 2, t1)), s


def main():
    T = table(MACHINE)
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 7
    n = bad = halts = 0
    grid = [(x, c, t) for x in range(1, 81) for c in range(0, 9) for t in (3, 6)]
    grid += [(x, c, t) for x in range(81, 301) for c in range(0, 4) for t in (3, 6)]
    for f in grid:
        g, s = rule(f)
        n += 1
        halts += g is None
        if not check_rule(T, tape(f), s, None if g is None else tape(g)):
            bad += 1
            print("differs:", f, "->", g, s)
    print(f"grid: {n} tapes ({halts} halting), {bad} failures")
    # the run from blank tape: S_3(4, 4) at step 388 (`start`), then the rules
    run = Run(T, ('', 'A', ''))
    f, at, visits = (4, 4, 3), 388, 1
    if run.run(388) is not None or run.cfg() != norm(tape(f)):
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
          f"{'all equal' if not bad else 'FAILED'}; last S_{f[2]}({f[0]}, {f[1]})")
    return bad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
