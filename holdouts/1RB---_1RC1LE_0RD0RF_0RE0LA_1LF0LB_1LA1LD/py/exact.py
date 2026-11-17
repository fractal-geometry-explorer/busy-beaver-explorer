"""The rule table of the explainer ("Exact tapes, exact step counts") checked against direct simulation.

usage: python3 py/exact.py [STEPS]     (default STEPS = 10000000: the run from blank tape is followed that far)

One family (lean/MapThm.lean, `Kc`):  K(x, m, s) = 0^inf 1^4 0 (10)^x 1^m C>s 0^inf  (the head, in state C, reads s).
`rule` is `mstep` with the number of machine steps of each case; the halt counts the halting transition too.
Checked: (a) a grid of samples K(x, m, s), each run for exactly the claimed number of steps and compared cell by cell
with the claimed target (or: halts at exactly that step); (b) the run from blank tape: every sample the rules
predict in the first STEPS steps, at its predicted step, is the machine's configuration then."""
import sys

MACHINE = "1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD"

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
    x, m, s = f
    return ('11110' + '10' * x + '1' * m, 'C', str(s))


def rule(f):
    """(next sample or None = halt, steps): the six cases of `mstep` (lean/MapThm.lean)."""
    x, m, s = f
    if m % 2 == 0:
        if x >= 1:
            return (x - 1, m + 4, 1 - s), 3 * m + 12 - 2 * s                      # B
        return ((m + 6) // 2, 1 + 2 * s, 0), 6 * m + 55 + 4 * s                  # R
    if x == 0:
        return None, m + 11 - 2 * s                                               # H
    h = (m + 5) // 2
    if x >= h:
        return (x - h, 2 * m + 7 - s, s), (3 * m * m + 24 * m + 61) // 2 - 7 * s   # C
    if x == h - 1 and s == 0:
        return (2 * x + 3, 1, 0), 6 * x * x + 30 * x + 75                         # A'
    return (2 * x + 1, m + 4 - 2 * x, 1 - s), 6 * x * x + 12 * x + 3 * m + 43 - 2 * s   # A


def main():
    T = table(MACHINE)
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 7
    n = bad = halts = 0
    for x in range(0, 41):
        for m in range(0, 46):
            for s in (0, 1):
                f = (x, m, s)
                g, k = rule(f)
                n += 1
                halts += g is None
                if not check_rule(T, tape(f), k, None if g is None else tape(g)):
                    bad += 1
                    print("differs:", f, "->", g, k)
    print(f"grid: {n} samples ({halts} halting), {bad} failures")
    # the run from blank tape: K(7, 1, 0) at step 216 (`start`), then the rules
    run = Run(T, ('', 'A', ''))
    f, at, visits = (7, 1, 0), 216, 1
    if run.run(216) is not None or run.cfg() != norm(tape(f)):
        bad += 1; print("start differs")
    while True:
        g, k = rule(f)
        if g is None or at + k > steps:
            break
        if run.run(k) is not None or run.cfg() != norm(tape(g)):
            bad += 1
            print("run differs at step", at + k, g)
            break
        at += k; f = g; visits += 1
    print(f"run from blank tape: {visits} predicted samples up to step {at:,} (of {steps:,}), "
          f"{'all equal' if not bad else 'FAILED'}; last K{f}")
    return bad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
