"""The rule table of the explainer ("Exact tapes, exact step counts") checked against direct simulation.

usage: python3 py/exact.py [STEPS]     (default STEPS = 10000000: the run from blank tape is followed that far)

Families (lean/Reset.lean; read left to right, 0^inf on both sides, the head reads the cell after S>):
    Z(t)      = 1^t A>                          (Zc)
    W(x, y)   = (10)^x 1^y A>                   (Wc; W(0, y) = Z(y))
    R(a, c)   = C> 0 1 (01)^a 1^c               (Rc)
    I(m, i, c) = 1 (01)^m A> 0 1 (0101)^i 1^c   (Ic)
`rule` gives the next family configuration and the number of steps (the leaf rules of lean/Leaves.lean, restated
in lean/Reset.lean with their step counts); the halt counts the halting transition too.  Checked: (a) a grid of
configurations of every family, each run for exactly the claimed number of steps and compared cell by cell with
the claimed target (or: halts at exactly that step); (b) the run from blank tape: every configuration the rules
predict in the first STEPS steps, at its predicted step, is the machine's configuration then."""
import sys

MACHINE = "1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA"

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
    k = f[0]
    if k == 'Z':
        return ('1' * f[1], 'A', '')
    if k == 'W':
        return ('10' * f[1] + '1' * f[2], 'A', '')
    if k == 'R':
        return ('', 'C', '01' + '01' * f[1] + '1' * f[2])
    if k == 'I':
        return ('1' + '01' * f[1], 'A', '01' + '0101' * f[2] + '1' * f[3])


SMALL = {0: (('Z', 19), 344), 1: (('Z', 19), 338), 2: (('Z', 6), 28), 3: (None, 125), 4: (('Z', 7), 32),
         5: (('Z', 20), 291)}


def fam(f):
    return ('Z', f[2]) if f[0] == 'W' and f[1] == 0 else f


def rule(f):
    """(next family configuration or None = halt, steps); None if no row of the table applies."""
    k = f[0]
    if k == 'Z':
        t = f[1]
        if t in SMALL:
            return SMALL[t]
        if t % 2 == 0:
            k2 = (t - 6) // 2
            return ('W', k2 + 1, 7), 4 * k2 + 36                   # even reset
        k2 = (t - 7) // 2
        return ('R', 0, 2 * k2 + 13), 12 * k2 + 69                 # odd reset
    if k == 'W':
        x, y = f[1], f[2]
        if y % 2 == 0 or x == 0:
            return None
        yy = (y - 1) // 2
        if x >= 2:
            return ('W', x - 2, 2 * yy + 7), 8 * yy + 18           # sweep
        return ('Z', 2 * yy + 6), 8 * yy + 18                      # last sweep
    if k == 'R':
        a, c = f[1], f[2]
        if a == 0:
            return (('R', 2, c - 2), 12) if c >= 2 else None       # first round
        a -= 1
        if c == 0:
            return ('R', 0, 2 * a + 5), 6 * a + 15                  # restart
        if c == 1:
            return None, 2 * a + 6                                  # halt
        return ('I', a, 0, c), 2 * a + 8                            # round begins
    m, i, c = f[1], f[2], f[3]
    if m >= 1:
        if c >= 2:
            return ('I', m - 1, i + 1, c - 2), 8 * i + 6            # pair moves across
        if c == 1:
            return ('W', m - 1, 4 * i + 5), 12 * i + 10             # round runs out of 1s
        return None
    if c >= 4:
        return ('R', 2 * i + 4, c - 4), 16 * i + 20                 # round ends
    if c == 3:
        return ('R', 2 * i + 3, 0), 16 * i + 20                     # round ends, no 1s left
    if c == 1:
        return ('Z', 4 * i + 4), 12 * i + 10                        # round ends in a block
    return None


def main():
    T = table(MACHINE)
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 7
    grid = [('Z', t) for t in range(0, 200)]
    grid += [('W', x, y) for x in range(1, 31) for y in range(1, 62, 2)]
    grid += [('R', a, c) for a in range(0, 31) for c in range(0, 41)]
    grid += [('I', m, i, c) for m in range(0, 21) for i in range(0, 21) for c in range(1, 42, 2)]
    n = bad = halts = 0
    for f in grid:
        r = rule(f)
        if r is None:
            continue
        g, k = r
        n += 1
        halts += g is None
        if not check_rule(T, tape(f), k, None if g is None else tape(g)):
            bad += 1
            print("differs:", f, "->", g, k)
    print(f"grid: {n} configurations ({halts} halting), {bad} failures")
    # the run from blank tape
    run, f, at, visits = Run(T, tape(('Z', 0))), ('Z', 0), 0, 0
    while True:
        g, k = rule(f)
        if g is None or at + k > steps:
            break
        if run.run(k) is not None or run.cfg() != norm(tape(g)):
            bad += 1
            print("run differs at step", at + k, g)
            break
        at += k; f = fam(g); visits += 1
    print(f"run from blank tape: {visits} predicted configurations up to step {at:,} (of {steps:,}), "
          f"{'all equal' if not bad else 'FAILED'}; last {f}")
    return bad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
