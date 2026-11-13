"""Validation and mutation tests for the transfer work on 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---.

1. runs.py against the real run: from every trip start of the first STEPS steps, `runs.start` + run to the next trip
   start must give the next real trip start and the same number of steps.
2. The shuttle theorem (lean/Transfer.lean `shuttles`, `scst_eq`) against a plain cell-by-cell simulator, for random
   lists of saturated runs, z and m; and five mutated statements, each of which must FAIL.
3. The halting tapes quoted in the README, on the plain simulator (exact halting step).

usage (from the repo root): python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/validate.py [STEPS]
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rsim import Sim, T  # noqa: E402
import runs as R  # noqa: E402
from monitor import canon  # noqa: E402


def plain(left, st, right, maxsteps):
    """Cell-by-cell run.  left/right: lists of cells (left in tape order, right starting at the head).
    Returns (steps, left, st, right) at the halt or after maxsteps steps (right-stripped of blank)."""
    tape = dict(enumerate(left + right, start=-len(left)))
    pos = 0
    for n in range(maxsteps):
        tr = T[(st, tape.get(pos, 0))]
        if tr is None:
            return n, None, st, None
        w, d, st = tr
        tape[pos] = w
        pos += d
    lo, hi = min(tape), max(tape)
    return maxsteps, [tape.get(i, 0) for i in range(lo, pos)], st, [tape.get(i, 0) for i in range(pos, hi + 1)]


def strip(cs, left):
    cs = list(cs)
    if left:
        while cs and cs[0] == 0:
            cs.pop(0)
    else:
        while cs and cs[-1] == 0:
            cs.pop()
    return cs


def shuttle_case(as_, z, m, lam, mut=None):
    """True if `lam (10)^m 0 A> runs(as) 1 (0101)^z` reaches `lam 0 A> runs(as) 1 (0101)^(z+m)` in scst steps."""
    S = sum(4 * a + 5 for a in as_)
    steps = m * (2 * S + 8 * z + 8) + 4 * m * (m - 1)
    zz, mm, take = z + m, m, [1, 0]
    if mut == "z":
        zz += 1
    if mut == "steps":
        steps += 2
    if mut == "m":
        mm -= 1
    if mut == "run":
        as_ = list(as_)
        as_[0] += 1          # the end tape claims a longer first run
    left = lam + take * m + [0]
    right = []
    src = as_ if mut != "run" else [as_[0] - 1] + list(as_[1:])
    for a in src:
        right += [1] + [0, 1, 0, 1] * (a + 1)
    right += [1] + [0, 1, 0, 1] * z
    if mut == "unsat":
        right[0:0] = [1, 0]  # first run 2 cells longer: not saturated
    n, l2, st, r2 = plain(left, 0, right, steps)
    if l2 is None:
        return False
    eleft = lam + take * (m - mm) + [0]
    eright = []
    for a in as_:
        eright += [1] + [0, 1, 0, 1] * (a + 1)
    eright += [1] + [0, 1, 0, 1] * zz
    if mut == "unsat":
        eright[0:0] = [1, 0]
    return st == 0 and strip(l2, True) == strip(eleft, True) and strip(r2, False) == strip(eright, False)


def main():
    steps = float(sys.argv[1]) if len(sys.argv) > 1 else 1e9
    # 1
    s, prev, pstep, n, bad = Sim(), None, 0, 0, 0
    while s.steps < steps:
        s.step()
        if s.at_left():
            cur = canon(s.runs())
            if prev is not None:
                st, r, k = R.next_trip(prev)
                n += 1
                if st != "trip" or r != cur or k != s.steps - pstep:
                    bad += 1
            prev, pstep = cur, s.steps
    print(f"1. runs.py vs the real run: {n} consecutive trip starts, {bad} mismatches")
    # 2
    random.seed(7)
    ok = 0
    cases = []
    for _ in range(200):
        as_ = [random.randint(0, 5) for _ in range(random.randint(1, 5))]
        cases.append((as_, random.randint(0, 6), random.randint(1, 9), [1, 1, 0, 1, 1] if random.random() < .5 else []))
    for c in cases:
        ok += shuttle_case(*c)
    print(f"2. shuttle theorem on the plain simulator: {ok} of {len(cases)} random cases agree")
    for mut in ("z", "steps", "m", "run", "unsat"):
        f = sum(1 for c in cases[:40] if not shuttle_case(*c, mut=mut))
        print(f"   mutation {mut}: {f} of 40 cases fail (must be 40)")
    # 3
    for r, want in (([6, 6, 4, 6, 5, 5, 5, 5, 6, 7], 5943), ([6, 6, 2, 7, 6, 5, 6, 3, 5, 5], 3587)):
        n, l2, st, r2 = plain([], 0, R.cells(r), 10**7)
        print(f"3. plain simulator from {r}: {'HALT at step ' + str(n + 1) if l2 is None else 'no halt'} (rsim: {want})")


if __name__ == "__main__":
    main()
