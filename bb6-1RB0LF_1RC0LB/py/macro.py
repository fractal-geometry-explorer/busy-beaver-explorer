"""The macro machine of 1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA (lean/Macro.lean), checked against the machine.

At every pass start the tape is

    0^inf 1^(2s1+2) 0 1^(2s2+2) 0 ... 0 1^(2sp+2) [head] 0^(2h+1) 1 (0 1)^m1 0^(2g1) 1 (0 1)^m2 0^(2g2) 1 ... (0 1)^mt 0^inf

a stack of solid blocks (top sp next to the head), a head gap of 2h + 2 cells, and a word of segments (0 1)^m and gaps
0^(2g) 1 (g = 0 is two 1s side by side).  The configurations are the same as in Lean:

    ("F", S, ws, mt)       F on the gap 0 0 1 (h = 0)
    ("B", S, h, ws, mt)    B on a gap of 2h + 2 cells
    ("Binf", S)            B with blank tape from the head on

S is the stack, top first; ws is the list of pairs (m, g); mt is the last segment.  `mstep` is `BB6e.mstep`, proved
sound in Lean (`mstep_sound`).  The notes write gaps as n = g - 1 (`nform`).

usage:
  python3 py/macro.py check STEPS      run from blank tape; at every pass start compare the tape with the macro
                                       configuration, then step the macro configuration
  python3 py/macro.py show T [FROM]    the macro configurations FROM..T-1 in the notes' notation
  python3 py/macro.py stats T          from M0, T macro steps: how often each rule fires, and the odd values
"""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools", "py"))

from bbtools.machine import Machine, Run  # noqa: E402

M = "1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA"
MACHINE = Machine.parse(M)
A, B, C, D, E, F = range(6)

M0 = ("B", [], 1, [], 1)  # the pass start after 12 steps: B> 0^4 1 0 1


def fscan(S, u, ws, mt):
    """BB6e.fscan: the pass from F; S the stack so far (top first), u the last segment crossed."""
    S = list(S)
    i = 0
    while True:
        if i == len(ws):
            return ("B", S, u + 2, [], mt)
        m, g = ws[i]
        if g == 1:
            S.insert(0, u)
            u = m
            i += 1
            continue
        if g >= 2:
            return ("B", S, u + 2, [(m, g - 2)] + ws[i + 1:], mt)
        # g == 0: two 1s side by side
        if m == 0:
            return None
        rest = ws[i + 1:]
        if not rest:
            return ("Binf", [u] + S) if mt == 0 else ("B", [u] + S, m, [], mt - 1)
        m2, g2 = rest[0]
        if m2 == 0:
            return None
        return ("B", [u] + S, m, [(m2 - 1, g2)] + rest[1:], mt)


def mstep(c):
    """BB6e.mstep: the next pass start, or None where Lean's rules do not apply (never seen from blank)."""
    if c[0] == "F":
        _, S, ws, mt = c
        return fscan(S, 0, ws, mt)
    if c[0] == "B":
        _, S, h, ws, mt = c
        if h == 0:
            return None
        if not S:
            return ("F", [], [(1, h - 1)] + ws, mt)
        return ("F", S[1:], [(S[0] + 2, h - 1)] + ws, mt)
    _, S = c
    if not S:
        return ("F", [], [], 1)
    return ("F", S[1:], [], S[0] + 2)


def encode(c):
    """The tape of a macro configuration: (cells, head index, state), cells from the leftmost 1 (or the head) to the
    last 1 (or the head)."""
    S = c[1]
    left = []
    for i, s in enumerate(reversed(S)):  # bottom first
        if i:
            left.append(0)
        left += [1] * (2 * s + 2)
    if c[0] == "Binf":
        return left + [0], len(left), B
    if c[0] == "F":
        _, _, ws, mt = c
        h, st = 0, F
    else:
        _, _, h, ws, mt = c
        st = B
    right = [0] * (2 * h + 2) + [1]
    for m, g in ws:
        right += [0, 1] * m + [0] * (2 * g) + [1]
    right += [0, 1] * mt
    return left + right, len(left), st


def tape_at(run):
    """The machine's tape as (cells, head index, state), trimmed to the 1s and the head."""
    t = run.tape
    ones = [i for i in range(t.lo, t.hi + 1) if t.get(i)]
    lo = min(ones + [run.head])
    hi = max(ones + [run.head])
    return [t.get(i) for i in range(lo, hi + 1)], run.head - lo, run.state


def check(steps):
    """Run from blank; at every pass start compare the tape with the macro configuration.  Returns (pass starts,
    mismatches, stuck)."""
    r = Run(MACHINE)
    last, c, starts, bad, stuck = 0, None, 0, 0, 0
    while r.steps < steps:
        if r.state in (B, F) and r.tape.get(r.head) == 0 and last == -1:
            starts += 1
            if c is None:
                c = M0
            if encode(c) != tape_at(r):
                bad += 1
            c = mstep(c)
            if c is None:
                stuck += 1
                break
        t = MACHINE.table[r.state][r.tape.get(r.head)]
        if t is None or not r.step():
            break
        last = t[1]
    return starts, bad, stuck


def nform(c):
    """The notes' notation: state, stack (bottom first) | head gap h | m1 <n1> m2 <n2> ... mt, with n = g - 1."""
    S = c[1]
    if c[0] == "Binf":
        return f"B {' '.join(map(str, reversed(S)))} | inf |"
    if c[0] == "F":
        h, ws, mt = 0, c[2], c[3]
    else:
        h, ws, mt = c[2], c[3], c[4]
    w = " ".join(f"{m} <{g - 1}>" for m, g in ws)
    return f"{c[0]} {' '.join(map(str, reversed(S)))} | {h} | {w} {mt}".replace("  ", " ")


def stats(T):
    """T macro steps from M0: which rule fired, and how many values of the configuration are odd."""
    c, rules, odd = M0, Counter(), Counter()
    for _ in range(T):
        if c[0] == "F":
            nxt = mstep(c)
            if nxt is None:
                rules["stuck"] += 1
                break
            ws = c[2]
            i = 0
            while i < len(ws) and ws[i][1] == 1:
                i += 1
            rules["F, gap of 4 or more cells" if i == len(ws) or ws[i][1] >= 2 else "F, two 1s side by side"] += 1
        else:
            nxt = mstep(c)
            rules["B" if c[0] == "B" else "B, blank ahead"] += 1
        vals = list(c[1]) + ([c[2]] if c[0] == "B" else [])
        if c[0] != "Binf":
            ws, mt = (c[2], c[3]) if c[0] == "F" else (c[3], c[4])
            vals += [x for m, g in ws for x in (m, g - 1)] + [mt]
        odd[sum(v % 2 for v in vals)] += 1
        c = nxt
    return rules, odd


def main(argv):
    cmd = argv[0]
    if cmd == "check":
        starts, bad, stuck = check(int(argv[1]))
        print(f"pass starts {starts}, mismatches {bad}, stuck {stuck}")
    elif cmd == "show":
        T = int(argv[1])
        a = int(argv[2]) if len(argv) > 2 else 0
        c = M0
        for t in range(T):
            if t >= a:
                print(t, nform(c))
            c = mstep(c)
    elif cmd == "stats":
        rules, odd = stats(int(argv[1]))
        for k, v in sorted(rules.items()):
            print(f"  {k}: {v}")
        print("  odd values per configuration:", dict(sorted(odd.items())))


if __name__ == "__main__":
    main(sys.argv[1:])
