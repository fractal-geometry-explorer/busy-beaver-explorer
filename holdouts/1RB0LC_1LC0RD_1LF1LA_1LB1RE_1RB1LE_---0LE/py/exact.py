"""The rule table of the explainer ("Exact tapes, exact step counts") checked against direct simulation.

usage: python3 py/exact.py [STEPS]     (default STEPS = 10000000: the run from blank tape is followed that far)

One family (lean/Map.lean, `X`):  X(a, b, c, k) = 0^inf E> 0 1^a 0 1 0 1^b (01)^c (11101)^k 1 0^inf.
`rule` is `next` of lean/Map.lean (with `land`) and the number of machine steps of each case (the counts of the rules
of lean/Rules.lean); the halt counts the halting transition too.  Checked: (a) a grid of tapes X(a, b, c, k), each
run for exactly the claimed number of steps and compared cell by cell with the claimed target (or: halts at exactly
that step); (b) the run from blank tape: every tape the rules predict in the first STEPS steps, at its predicted
step, is the machine's configuration then."""
import sys

MACHINE = "1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE"

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
    a, b, c, k = f
    return ('', 'E', '0' + '1' * a + '010' + '1' * b + '01' * c + '11101' * k + '1')


def land(B, c, k):
    """X(B, 7, c, k); with c = 0 the first 11101 of the suffix is read as a pair: X(B, 7, 0, k+1) = X(B, 10, 1, k)."""
    if c >= 1:
        return (B, 7, c, k)
    return (B, 10, 1, k - 1) if k >= 1 else None


def rule(f):
    """(next tape or None = halt, steps), or None where `next` is `stuck`."""
    a, b, c, k = f
    if c == 0:
        return None
    if a >= 4:
        return (a - 2, b + 3, c, k), 6 * (a - 4) + 23                     # r_big
    if a == 3:
        return (1, b + 3, c, k), 17                                       # r_three
    if a == 2:
        return (0, b + 3, c, k), 11                                       # r_two
    if c >= 2:
        if a == 1 and b == 1:
            return (2, 4, c - 1, k), 28                                   # r_one_1
        if b < 3:
            return None
        g = land(b if a == 1 else b - 1, c - 2, k)
        if g is None:
            return None
        return g, (12 * b + 14 if a == 1 else 12 * b + 6)                 # r_one, r_one_3..11 / r_zero, r_zero_3..11
    if a == 1:
        if b % 2 == 1:
            return ((2, 1, b // 2, k + 1), 6 * b + 22 * k + 30) if b >= 3 else None    # e_one_odd
        return (None, 6 * b + 22 * k + 36) if b >= 2 else None                         # e_halt, e_halt0
    if b % 2 == 0:
        return ((5, 4, b // 2 - 3, k + 1), 6 * b + 22 * k + 72) if b >= 10 else None   # e_zero_even, e_zero_even0
    return ((1, 1, b // 2, k + 1), 6 * b + 22 * k + 22) if b >= 5 else None             # e_zero_odd


def main():
    T = table(MACHINE)
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 7
    n = bad = halts = 0
    for a in range(0, 25):
        for b in range(0, 37):
            for c in range(0, 7):
                for k in range(0, 4):
                    f = (a, b, c, k)
                    r = rule(f)
                    if r is None:
                        continue
                    g, s = r
                    n += 1
                    halts += g is None
                    if not check_rule(T, tape(f), s, None if g is None else tape(g)):
                        bad += 1
                        print("differs:", f, "->", g, s)
    print(f"grid: {n} tapes ({halts} halting), {bad} failures")
    # the run from blank tape: X(15, 7, 7, 1) at step 1188 (`init_X`), then the rules
    run = Run(T, ('', 'A', ''))
    f, at, visits = (15, 7, 7, 1), 1188, 1
    if run.run(1188) is not None or run.cfg() != norm(tape(f)):
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
          f"{'all equal' if not bad else 'FAILED'}; last X{f}")
    return bad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
