"""The pass map of 1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD, checked against the machine and iterated.

At every *pass start* (state B at the left end of the tape) the tape is

    B> 0 0 (10)^a 1^b T 0^inf        T = "10" (t = True) or nothing (t = False)

and the next pass start is pass_map(a, b, t).  A pass is a loop of *phases*: state A eats the a-blocks one at a
time (each costs two 1s of the right block 1^s and adds four 1s to a growing block on its left); if the right block
runs out first the head *rebounds* off the right end, the left block becomes the new right block and the phase
starts again.  The halting transition (E reading 0) is reached exactly when a pass ends with b = 0 and t = True:
from  B> 0 0 (10)^n 0^inf  states C and E zip right over the 10s and E reads the blank (see the README).

usage (from the repository root):
  python3 holdouts/1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD/py/passmap.py check STEPS
        run the machine (tools/c/tmrun, compiled to /tmp if needed) and compare every pass start with the map
  python3 holdouts/1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD/py/passmap.py iterate PASSES
        iterate the map from the first pass start (0, 4, True) and report halts, near misses and parity epochs
  python3 holdouts/1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD/py/passmap.py lean PASSES
        iterate lean_next, a copy of the phase map `next` that lean/Phases.lean proves, from PS 0 2, and compare
        it with pass_map at every pass start (PS a c is the pass start (a, c - t, t) of pass_map)
"""
import os
import re
import subprocess
import sys
from collections import Counter

M = "1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD"
REPO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))


def pass_map(a, b, t):
    """The next pass start after (a, b, t), or ('halt', a', t) when the pass ends with b' = 0 and t: the machine
    then halts a few steps into the next pass.  Derived from the runs and checked by `check`; the proved form is
    `next` of lean/Phases.lean (copied as `lean_next` below), and `lean` checks that the two agree."""
    r, s, l = a - 1, b, 4          # a-blocks still to eat (minus one), right block, left block
    while True:
        if r < -2:
            raise ValueError(("unseen case", a, b, t, r, s, l))
        if 2 * r <= s - 3:         # enough 1s on the right: eat the rest and end the pass
            l += 4 * r
            s -= 2 * r
            a2, b2 = l // 2 + 2, s - 4
            if b2 == -1:           # the last 10 joins the left: (0, 2a', True)
                return (0, 2 * a2, True)
            if b2 == 0:
                if t:
                    return ("halt", a2, t)
                return (0, 2 * a2, True)
            return (a2, b2, t)
        if s % 2 == 1:             # odd right block runs out: rebound
            m = (s - 1) // 2
            r -= m
            l += 4 * m
            s, r, l = l + 1, r - 2, 4
        elif t:                    # even right block, trailing 10: rebound eats the 10
            m = (s - 2) // 2
            r -= m
            l += 4 * m
            s, r, l, t = l + 8, r - 3, 4, False
        else:                      # even right block, no trailing 10: rebound writes one
            m = (s - 2) // 2
            r -= m
            l += 4 * m
            s, r, l, t = l + 1, r - 2, 4, True


def lean_next(p):
    """The phase map `next` of lean/Phases.lean, case by case.  ('ps', a, c) is PS a c = 0^inf B> 0 0 (10)^a 1^c,
    ('q', R, m, c) is Q R m c = 0^inf (10)^R (11)^m A> 1^c; None where Lean's `next` is none."""
    if p[0] == "ps":
        _, a, c = p
        if c <= 1:
            return None
        if a == 0:
            return ("ps", 0, 5) if c == 2 else ("ps", 2, c - 2)
        return ("q", a - 1, 2, c)
    _, R, m, c = p
    if m < 2 or c == 0:
        return None
    if R >= 1 and c >= 3:
        j = min(R, (c - 1) // 2)
        return ("q", R - j, m + 2 * j, c - 2 * j)
    if R == 0:
        if c >= 5:
            return ("ps", m + 2, c - 4)
        return ("ps", 0, {1: 2 * m + 4, 2: 2 * m + 2, 3: 2 * m + 7, 4: 2 * m + 5}[c])
    if R == 1:
        return ("ps", 2, 2 * m + 2 if c == 1 else 2 * m)
    return ("q", R - 2, 2, 2 * m + 4 if c == 1 else 2 * m + 2)


def lean(n):
    p, phases = ("ps", 0, 2), 0
    p = lean_next(p)                     # PS 0 2 -> PS 0 5, the pass start (0, 4, True) of pass_map
    a, b, t = 0, 4, True
    for i in range(n):
        g = pass_map(a, b, t)
        q = lean_next(p)
        phases += 1
        while q is not None and q[0] == "q":
            q = lean_next(q)
            phases += 1
        if g[0] == "halt":
            print("pass_map halts after pass", i, "; lean_next gives", q)
            return
        if q != ("ps", g[0], g[1] + g[2]):
            print("DIFFERENT at pass", i, (a, b, t), "pass_map", g, "lean_next", q)
            return
        a, b, t = g
        p = q
    print(f"{n} passes: lean_next and pass_map agree at every pass start ({phases} phases); no PS a c with c <= 1")


def parse(tape):
    """(a, b, t) from a tmrun tape 'B>0 0 1 0 ...' at a pass start, or None."""
    cells = []
    for tok in tape.split():
        m = re.match(r"^(?:[A-F]>)?([01])(?:\^(\d+))?$", tok)
        cells += [m.group(1)] * int(m.group(2) or 1)
    raw = "".join(cells)
    m = re.fullmatch(r"00((?:10)*)(1*)(0*)", raw)
    if not m:
        return None
    a, ones = len(m.group(1)) // 2, len(m.group(2))
    # tmrun prints the visited cells: a trailing "10" shows as one more 1 and a visited 0
    t = len(m.group(3)) > 0
    return (a, ones - 1, True) if t else (a, ones, False)


def tmrun():
    exe = "/tmp/tmrun_passmap"
    if not os.path.exists(exe):
        subprocess.check_call(["gcc", "-O2", "-o", exe, os.path.join(REPO, "tools", "c", "tmrun.c")])
    return exe


def check(steps):
    out = subprocess.run([tmrun(), M, str(steps), "at", "B", "L", "100000000"], capture_output=True, text=True).stdout
    starts = []
    for line in out.splitlines():
        f = line.split(maxsplit=1)
        if f[0] in ("running", "halted"):
            continue
        starts.append((int(f[0]), parse(f[1])))
    ok = bad = 0
    for (s0, p), (s1, q) in zip(starts, starts[1:]):
        if p is None or q is None:
            print("unparsed at", s0, s1)
            bad += 1
            continue
        if pass_map(*p) == q:
            ok += 1
        else:
            bad += 1
            print("mismatch", s0, p, "->", q, "map:", pass_map(*p))
    print(f"{len(starts)} pass starts in {steps} steps; {ok} passes as the map says, {bad} not")


def iterate(n):
    a, b, t = 0, 4, True
    near, epochs, flips, even = Counter(), [], 0, 0
    par = b % 2
    for i in range(n):
        g = pass_map(a, b, t)
        if g[0] == "halt":
            print("HALT after pass", i, (a, b, t))
            return
        if g[1] <= 5:
            near[g[1]] += 1
        if g[1] % 2 != par:
            flips += 1
            par = g[1] % 2
        even += g[1] % 2 == 0
        a, b, t = g
    print(f"{n} passes, no halt; last pass start a={a} b={b} t={t}, width 2a+b+2t+2 = {2 * a + b + 2 * t + 2}")
    print(f"passes ending with b even: {even}; parity changes of b: {flips}; ends with b <= 5: {dict(sorted(near.items()))}")


if __name__ == "__main__":
    if len(sys.argv) != 3 or sys.argv[1] not in ("check", "iterate", "lean"):
        sys.exit(__doc__)
    {"check": check, "iterate": iterate, "lean": lean}[sys.argv[1]](int(sys.argv[2]))
