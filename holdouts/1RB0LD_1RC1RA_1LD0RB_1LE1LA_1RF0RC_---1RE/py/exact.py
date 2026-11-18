"""The rule table of the explainer ("Exact tapes, exact step counts") checked against direct simulation.

usage: python3 py/exact.py [STEPS]     (default STEPS = 10000000: the run from blank tape is followed that far)

One family (lean/Macro.lean, `enc`):  P(a, K, j) = 0^inf 1^a 0 0 (10)^K 1^(2j+1) C> 0^inf.
`rule` gives the rules of lean/Rules.lean with their step counts (a sweep, the two ends of a phase, the reset, the
halt; the halt counts the halting transition too); `phase` is `mstep` of lean/Macro.lean (a whole phase) with the
sum of those counts.  Checked: (a) a grid of tapes P(a, K, j), each run for exactly the claimed number of steps and
compared cell by cell with the claimed target (or: halts at exactly that step), for `rule` and for `phase`; (b) the
run from blank tape: every tape `rule` predicts in the first STEPS steps, at its predicted step, is the machine's
configuration then."""
import sys

MACHINE = "1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE"

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
    a, K, j = f
    return ('1' * a + '00' + '10' * K + '1' * (2 * j + 1), 'C', '')


def rule(f):
    """(next tape or None = halt, steps): one rule of lean/Rules.lean."""
    a, K, j = f
    if K >= 2:
        return (a, K - 2, j + 3), 8 * j + 14                  # inner
    if a >= 1:
        if K == 0:
            return (a - 1, j + 1, 0), 8 * j + 13              # end_even
        return (a - 1, j + 3, 1), 12 * j + 33                 # end_odd
    if K == 0:
        return None, 8 * j + 14                               # to_halt, then the halting transition
    return (2 * j + 7, 0, 1), 12 * j + 38                     # reset_a (12j + 31), reset_b (7)


def phase(f):
    """`mstep`: i = K // 2 sweeps and the end, with J = j + 3i."""
    a, K, j = f
    i = K // 2
    J = j + 3 * i
    s = 8 * i * j + 12 * i * i + 2 * i
    g, e = rule((a, K % 2, J))
    return g, s + e


def main():
    T = table(MACHINE)
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 7
    n = bad = halts = 0
    for a in range(0, 31):
        for K in range(0, 41):
            for j in range(0, 31):
                f = (a, K, j)
                for fn in (rule, phase) if K >= 2 else (rule,):
                    g, s = fn(f)
                    n += 1
                    halts += g is None
                    if not check_rule(T, tape(f), s, None if g is None else tape(g)):
                        bad += 1
                        print("differs:", fn.__name__, f, "->", g, s)
    print(f"grid: {n} checks of tapes and step counts ({halts} halting), {bad} failures")
    # the run from blank tape: P(3, 0, 1) at step 18 (`start`), then the rules
    run = Run(T, ('', 'A', ''))
    f, at, visits = (3, 0, 1), 18, 1
    if run.run(18) is not None or run.cfg() != norm(tape(f)):
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
          f"{'all equal' if not bad else 'FAILED'}; last P{f}")
    return bad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
