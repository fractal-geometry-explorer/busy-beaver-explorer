"""The right end of the tape as a base-3 counter, checked against the run.

At each return of the head to the right end (state C reading the `0` of `... 0 10 0^inf`), the tape is read as
blocks of pairs `10` and single separator cells (`blocks`).  Read from the right, it is a list of *levels*
`s_l (10)^g s_r (10)^W`; the digit of a level is 2 for seps `1 1`, 1 for `0 1`, 0 for `0 0`.  One excursion to the
left and back subtracts one from the base-3 number the digits spell (the last level lowest), `predict` below:

    digit 2 -> 1:  s_l becomes 0, g + 1, W - 1   (W + 1 for the last level)
    digit 1 -> 0:  s_r becomes 0                  (W + 2 for the last level)
    digit 0 -> 2:  borrow from the level to the left; seps 1 1, g + 1, W - 1  (W + 1 for the last level)

with the parities the theorems need (digit 2: g, W odd; digits 1, 0: g, W even) and minimum sizes.  This is what
`lean/Counter.lean` proves, for every block length and any number of borrows (`counter_last2`, `counter_last1`,
`counter_borrow2`, `counter_borrow1`).  `check` runs the machine (the macro simulator `bbtools.macro`, k = 4) and
compares every excursion with `predict`: the excursions it predicts all come out as predicted, and the rest are the
ones whose borrow reaches the irregular blocks at the left end of the tape (`left`), or meets a level too short or
of the wrong parity for the theorems (`short`), which happens only among the leftmost levels.

usage: python3 counter.py check STEPS          tally of excursions to STEPS (1e10: about a minute)
       python3 counter.py levels STEPS         the level list at the first right-end return after STEPS
       python3 counter.py events STEPS         the excursions `predict` does not cover, before and after
"""
import collections
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools", "py"))
from bbtools.macro import MacroRun  # noqa: E402

M = "1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---"
C = 2   # state C


def items(run):
    """The tape of a k=4 MacroRun, left to right, as cells (0/1) and ('P', n) for (10)^n."""
    out = []
    lw, rw = run.runs()
    for w, c in lw + rw:
        if c >= 3 and w == "1010":
            out.append(("P", 2 * c))
        elif c >= 3 and w == "0101":
            out += [0, ("P", 2 * c - 1), 1]
        else:
            for _ in range(c):
                out += [int(ch) for ch in w]
    return out


def blocks(its):
    """Greedy reading as (10)+ | single cell: a list of ints (block lengths in pairs) and '0'/'1' (single cells),
    without leading or trailing zeros."""
    toks, run, lone = [], 0, False

    def flush():
        nonlocal run
        if run:
            toks.append(run)
            run = 0

    for it in its:
        if isinstance(it, tuple):
            if lone:
                flush()
                toks.append("1")
                lone = False
            run += it[1]
        elif lone:
            if it == 0:
                run += 1
                lone = False
            else:
                flush()
                toks.append("1")
        elif it == 1:
            lone = True
        else:
            flush()
            toks.append("0")
    if lone:
        flush()
        toks.append("1")
    flush()
    while toks and toks[0] == "0":
        toks.pop(0)
    while toks and toks[-1] == "0":
        toks.pop()
    return toks


def tape_str(toks):
    return "".join("10" * t if isinstance(t, int) else t for t in toks).lstrip("0")


DIGIT = {("1", "1"): 2, ("0", "1"): 1, ("0", "0"): 0}


def predict(t):
    """One excursion as Counter.lean proves it: (new token list, None), or (None, reason) when no theorem
    applies: 'left' (the borrow runs into the irregular left end) or 'short' (a level too short or of the wrong
    parity)."""
    t = list(t)
    if len(t) < 5 or t[-2] != "0" or t[-1] != 1:
        return None, "tail"
    i, last = len(t) - 5, True          # t[i] is the g of the level being looked at
    while True:
        if i < 1 or not isinstance(t[i], int) or not isinstance(t[i + 2], int):
            return None, "left"
        d = DIGIT.get((t[i - 1], t[i + 1]))
        if d is None:
            return None, "left"
        g, w = t[i], t[i + 2]
        if d == 2:
            if not (g % 2 == 1 and w % 2 == 1 and w >= (1 if last else 3)):
                return None, "short"
            t[i - 1] = "0"
            t[i] += 1
            t[i + 2] += 1 if last else -1
            return t, None
        if d == 1:
            if not (g % 2 == 0 and g >= 2 and w % 2 == 0 and w >= 2):
                return None, "short"
            t[i + 1] = "0"
            if last:
                t[i + 2] += 2
            return t, None
        if not (g % 2 == 0 and g >= 2 and w % 2 == 0 and w >= (2 if last else 4)):
            return None, "short"
        t[i - 1] = t[i + 1] = "1"
        t[i] += 1
        t[i + 2] += 1 if last else -1
        last = False
        i -= 4


def returns(steps):
    """(step count, token list) at each return of the head to the right end, up to `steps`."""
    r = MacroRun(M, 4)
    prev = None
    while r.steps < steps:
        if not r.step():
            raise RuntimeError(f"halted after {r.steps} steps")
        if r.state == C and r.dir == 1 and len(r.right) == 2 and r.right[1] == [(0, 1, 0, 0), 1]:
            t = blocks(items(r))
            if t != prev:
                yield r.steps, t
                prev = t


def check(steps, events=None):
    """Tally of excursions up to `steps`: 'proved' (predicted and confirmed), 'left', 'short', and 'wrong'
    (predicted and not confirmed, which would contradict Counter.lean)."""
    tally = collections.Counter()
    prev = None
    for s, t in returns(steps):
        if prev is not None:
            p, why = predict(prev)
            if p is None:
                tally[why] += 1
                if events is not None:
                    events.append((s, why, prev, t))
            else:
                tally["proved" if tape_str(p) == tape_str(t) else "wrong"] += 1
        prev = t
    return tally


def main(argv):
    if len(argv) != 2:
        sys.exit(__doc__)
    cmd, steps = argv[0], int(float(argv[1]))
    if cmd == "check":
        tally = check(steps)
        n = sum(tally.values())
        print(f"{n} excursions to {steps:.3g} steps: " + ", ".join(f"{k} {v}" for k, v in sorted(tally.items())))
    elif cmd == "levels":
        for s, t in returns(float("inf")):
            if s >= steps:
                print(s, " ".join(map(str, t)))
                return
    elif cmd == "events":
        ev = []
        check(steps, ev)
        for s, why, a, b in ev:
            print(f"{s} {why}\n   {' '.join(map(str, a))}\n   {' '.join(map(str, b))}")
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
