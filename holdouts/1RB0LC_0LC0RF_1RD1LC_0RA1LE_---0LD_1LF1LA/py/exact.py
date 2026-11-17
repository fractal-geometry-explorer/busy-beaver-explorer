"""The rule table of the explainer ("Exact tapes, exact step counts") checked against direct simulation.

usage: python3 py/exact.py [STEPS]     (default STEPS = 10000000: the run from blank tape is followed that far)

One family (lean/Map.lean, `X`):  X(a, b, c) = 0^inf D> 0 0 1^a 0 1^b (01)^c 0^inf.
`rule` is `next` of lean/Map.lean with the number of machine steps of each case (the counts of the rules of
lean/Rules.lean); the halt counts the halting transition too.  Checked: (a) a grid of tapes X(a, b, c), each run for
exactly the claimed number of steps and compared cell by cell with the claimed target (or: halts at exactly that
step); (b) the run from blank tape: every tape the rules predict in the first STEPS steps, at its predicted step, is
the machine's configuration then."""
import sys

MACHINE = "1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA"

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
    a, b, c = f
    return ('', 'D', '00' + '1' * a + '0' + '1' * b + '01' * c)


def rule(f):
    """(next tape or None = halt, steps), or None where `next` is `stuck`."""
    a, b, c = f
    if a >= 4:
        return (a - 2, b + 3, c), 4 * (a - 4) + 21                         # r_big
    if a == 3:
        return (1, b + 3, c), 17                                           # r_three
    if a == 1:
        if b >= 3:
            return ((b + 1, 4, c - 1) if c >= 1 else (b + 1, 3, 0)), 4 * (b - 3) + 34   # r_one, r_one0
        if b == 1 and c >= 1:
            return (2, 4, c - 1), 26                                       # r_one_b1
        return None
    if a == 2:
        if c >= 3:
            return (b + 6, 4, c - 3), 4 * b + 50                           # r_two3
        if c == 2:
            return (b + 6, 3, 0), 4 * b + 50                               # r_two2
        if c == 1:
            return (b + 5, 3, 0), 4 * b + 46                               # r_two1
        if b % 2 == 0:
            return (1, 1, b // 2 + 1), 4 * b + 31                          # r_two0e (b = 2k: 8k + 31)
        return None, 4 * b + 32                                            # r_two0o (b = 2k+1: 8k + 35, + 1)
    return None


def main():
    T = table(MACHINE)
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 7
    n = bad = halts = 0
    for a in range(0, 41):
        for b in range(0, 41):
            for c in range(0, 13):
                f = (a, b, c)
                r = rule(f)
                if r is None:
                    continue
                g, k = r
                n += 1
                halts += g is None
                if not check_rule(T, tape(f), k, None if g is None else tape(g)):
                    bad += 1
                    print("differs:", f, "->", g, k)
    print(f"grid: {n} tapes ({halts} halting), {bad} failures")
    # the run from blank tape: X(1, 1, 4) at step 138 (`init_X`), then the rules
    run = Run(T, ('', 'A', ''))
    f, at, visits = (1, 1, 4), 138, 1
    if run.run(138) is not None or run.cfg() != norm(tape(f)):
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
    print(f"run from blank tape: {visits} predicted tapes up to step {at:,} (of {steps:,}), "
          f"{'all equal' if not bad else 'FAILED'}; last X{f}")
    return bad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
