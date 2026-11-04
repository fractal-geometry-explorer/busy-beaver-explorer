"""Passes of 1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA: the rule of lean/Pass.lean, checked on the run from blank.

A *gap* is a maximal run of 0s between two 1s.  A pass starts when the head turns right: F or B, having just moved
left, reads a 0 (the first cell of a gap) and moves right, and C then stands on the gap's second cell.  C crosses gaps of length 1 and 2; the first gap of any other
length ends the pass: 3 halts, 4 or more turns left at E, 0 (two 1s side by side) turns left at B or F.  This is
proved in Lean (`pass_outcome`, kernel); here it is a rule to apply to tapes.

usage:
  python3 py/passes.py check STEPS        run from blank tape; at every pass start predict the ending from the cells
                                          ahead, run the machine to the end of the pass and compare; check the
                                          parity invariant; print the tally of ending gaps
  python3 py/passes.py starts STEPS [K]   the first K pass starts as "STEPS tape" with the ending gap

The parity invariant (observed, not proved): at every pass start, every run of 0s or of 1s of length 3 or more that
has the other symbol on both sides and does not touch the head has even length.  A pass can halt only by meeting a
gap of exactly 3, so as long as the invariant holds the machine does not halt.  c/passes.c checks the same things
for billions of steps.
"""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools", "py"))

from bbtools.machine import Machine, Run  # noqa: E402

M = "1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA"
MACHINE = Machine.parse(M)
A, B, C, D, E, F = range(6)
BLANK = "blank"


def ending(cells):
    """How a pass ends, from the cells starting at the gap's first cell (C enters at index 1).

    Returns (gaps crossed, ending gap) where the ending gap is 3, a length of 4 or more, BLANK when the gap runs to the
    end of `cells` (the blank part of the tape), or 0 for two 1s side by side; then the last crossed gap (1 or 2) is
    the one just before them, and it decides who turns: B after a 1 (`gap1_then_0`), A after a 2 (`gap2_then_0`)."""
    crossed = []
    x = 1
    while True:
        g = 1
        while x < len(cells) and cells[x] == 0:
            g += 1
            x += 1
        if x >= len(cells):
            return crossed, BLANK
        if g not in (1, 2):
            return crossed, g
        x += 1
        crossed.append(g)
        if x < len(cells) and cells[x] == 1:
            return crossed, 0
        x += 1


def first_left(crossed, g):
    """The state that makes the pass's first left move, or None for a halt (lean/Pass.lean)."""
    if g == 3:
        return None
    if g == 0:
        return B if crossed[-1] == 1 else F
    return E


def odd_runs(run):
    """Runs of length >= 3 and odd length, with the other symbol on both sides, not touching the head."""
    t = run.tape
    lo, hi = t.lo, t.hi
    cells = [t.get(i) for i in range(lo, hi + 1)]
    out = []
    i = 0
    while i < len(cells) and cells[i] == 0:
        i += 1
    while i < len(cells):
        j = i
        while j < len(cells) and cells[j] == cells[i]:
            j += 1
        if j >= len(cells):
            break
        st, en = lo + i, lo + j - 1
        n = j - i
        if n >= 3 and n % 2 == 1 and not (st - 1 <= run.head <= en + 1):
            out.append((cells[i], n, st))
        i = j
    return out


def pass_starts(steps):
    """Yield the run at each pass start (F or B on a 0 after a left move, before it moves right)."""
    r = Run(MACHINE)
    last = 0
    while r.steps < steps:
        if r.state in (B, F) and r.tape.get(r.head) == 0 and last == -1:
            yield r
        t = MACHINE.table[r.state][r.tape.get(r.head)]
        if t is None or not r.step():
            return
        last = t[1]


def ahead(run):
    """The cells from the head to the right end of the visited tape."""
    return [run.tape.get(i) for i in range(run.head, run.tape.hi + 1)]


def check(steps):
    """Run from blank; at each pass start compare the predicted ending with the machine.  Returns (starts, tally of
    ending gaps, mismatches, odd runs found)."""
    r = Run(MACHINE)
    starts, mism, odd = 0, 0, 0
    tally = Counter()
    last = 0
    while r.steps < steps:
        if r.state in (B, F) and r.tape.get(r.head) == 0 and last == -1:
            starts += 1
            crossed, g = ending(ahead(r))
            tally[g] += 1
            odd += len(odd_runs(r))
            want = first_left(crossed, g)
            # run the pass to its first left move, or a halt
            while True:
                t = MACHINE.table[r.state][r.tape.get(r.head)]
                if t is None or t[1] != 1:
                    break
                r.step()
                last = 1
            got = None if t is None else r.state
            if got != want:
                mism += 1
            if got is None:
                break
            continue
        t = MACHINE.table[r.state][r.tape.get(r.head)]
        if t is None or not r.step():
            break
        last = t[1]
    return starts, tally, mism, odd


def main(argv):
    cmd, steps = argv[0], int(argv[1])
    if cmd == "check":
        starts, tally, mism, odd = check(steps)
        print(f"pass starts {starts}, predictions wrong {mism}, odd runs {odd}")
        for g in sorted(tally, key=lambda x: (isinstance(x, str), x)):
            print(f"  ending gap {g}: {tally[g]}")
    elif cmd == "starts":
        k = int(argv[2]) if len(argv) > 2 else 50
        for n, r in enumerate(pass_starts(steps)):
            if n >= k:
                break
            crossed, g = ending(ahead(r))
            print(r.steps, r.config_str(), " ends at gap", g)


if __name__ == "__main__":
    main(sys.argv[1:])
