"""The phases of 1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD from blank tape, with the macro simulator.

A phase starts when the head, in state B, stands just left of the lone 1 at the left end of the tape:
`0^inf B> 0 1 0^X T`.  Prints the step, the gap X and the tail T (run-length coded) at each phase start, and the
correction d = X' - 3X/2 between consecutive phases.

usage: python3 phases.py [STEPS]      (default 1e11; 3.9e13 takes a few minutes)
"""
import os
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.macro import MacroRun  # noqa: E402

M = "1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD"


def rle(r):
    """The tape right of the head as run-length tokens (the head is at the left end)."""
    toks = []
    for w, c in r.runs()[1]:
        cells = w[0] * (len(w) * c) if len(set(w)) == 1 else w * c
        for ch in cells if len(set(w)) > 1 else [cells]:
            b, n = ch[0], len(ch)
            if toks and toks[-1][0] == b:
                toks[-1][1] += n
            else:
                toks.append([b, n])
    return " ".join(f"{b}^{n}" if n > 1 else b for b, n in toks)


def main(argv):
    steps = int(float(argv[0])) if argv else int(1e11)
    r = MacroRun(M, 2)
    was_left, prev = False, None
    while r.steps < steps:
        if not r.step():
            print("halts after", r.steps, "steps")
            return
        at_left = len(r.left) == 1 and r.dir == -1
        if at_left and not was_left and r.state == 1:
            s = rle(r)
            m = re.match(r"1 0\^(\d+) (.*)", s)
            if m:
                X = int(m.group(1))
                d = "" if prev is None else f"  d = {X - 1.5 * prev:+g}"
                print(f"{r.steps} X={X} (mod 4: {X % 4}) T: {m.group(2)}{d}", flush=True)
                prev = X
        was_left = at_left


if __name__ == "__main__":
    main(sys.argv[1:])
