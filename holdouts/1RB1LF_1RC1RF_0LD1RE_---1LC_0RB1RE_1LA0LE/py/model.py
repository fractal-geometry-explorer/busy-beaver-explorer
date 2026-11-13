"""The doubling bouncer of 1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE.

At every right-end visit in state B the tape is

    T(P, a, b) = 0^inf [1^2 0 (10)^c] 1^a 0 (10)^b B>0 0^inf      (P = the bracket, present or not)

The main rule: if a >= 2b + 3, the next visit is T(P, a - 2b - 2, 2b + 2) (the (10) block doubles, plus 2, eating
2b + 2 ones).  Otherwise the step is exceptional (the pool overflows; the tape is rewritten and the bracket can
appear, grow or vanish).  The only halting configurations of this form: no bracket and a = 1.  Since the main rule
keeps the parity of a, a halt needs a run of steps with a odd.

    python3 py/model.py check       # main rule and halting cases against simulation (grid), and along the run
"""
import re
import sys

M = "1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE"
PAT = re.compile(r"(?:(11)0((?:10)*))?(1*)0((?:10)*)")


def table():
    T = {}
    for i, g in enumerate(M.split("_")):
        for s in (0, 1):
            t = g[3 * s:3 * s + 3]
            T[(i, s)] = None if t[0] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


def parse_t(tape, lo, pos):
    a = lo
    while a < pos and tape.get(a, 0) == 0:
        a += 1
    m = PAT.fullmatch("".join(str(tape.get(x, 0)) for x in range(a, pos)))
    if not m:
        return None
    return (len(m.group(2)) // 2 if m.group(1) else None, len(m.group(3)), len(m.group(4)) // 2)


def sim(c, a, b, limit=10 ** 6):
    T = table()
    w = word(c, a, b)
    tape = {i: int(ch) for i, ch in enumerate(w)}
    pos, st, lo, hi = len(w), 1, 0, len(w)
    for _ in range(limit):
        t = T[(st, tape.get(pos, 0))]
        if t is None:
            return "halt"
        tape[pos] = t[0]; pos += t[1]; st = t[2]
        lo = min(lo, pos)
        if pos > hi:
            hi = pos
            if st == 1:
                r = parse_t(tape, lo, pos)
                if r:
                    return r
    return "?"


def word(c, a, b):
    return ("11" + "0" + "10" * c if c is not None else "") + "1" * a + "0" + "10" * b


def same(r, c, a, b):
    return isinstance(r, tuple) and word(*r) == word(c, a, b)


def check():
    bad = n = 0
    for c in (None, 0, 1, 2, 5, 9):
        for a in range(1, 40):
            for b in range(0, 20):
                r = sim(c, a, b); n += 1
                if a >= 2 * b + 3 and not same(r, c, a - 2 * b - 2, 2 * b + 2):
                    bad += 1; print("main rule fails", c, a, b, r)
                if (r == "halt") != (c is None and a == 1):
                    bad += 1; print("halting case differs", c, a, b, r)
    print(f"grid: {n} configurations, {bad} failures")
    T = table()
    tape, pos, st, lo, hi, prev = {}, 0, 0, 0, 0, None
    main = 0
    for k in range(3 * 10 ** 6):
        t = T[(st, tape.get(pos, 0))]
        tape[pos] = t[0]; pos += t[1]; st = t[2]
        lo = min(lo, pos)
        if pos > hi:
            hi = pos
            if st == 1:
                r = parse_t(tape, lo, pos)
                if r is None:
                    continue
                if prev and prev[1] >= 2 * prev[2] + 3:
                    main += 1
                    if not same(r, prev[0], prev[1] - 2 * prev[2] - 2, 2 * prev[2] + 2):
                        bad += 1; print("run: main rule fails at", k + 1, prev, r)
                prev = r
    print(f"run: {main} main-rule steps in 3e6 steps, {bad} failures")
    return bad


if __name__ == "__main__":
    sys.exit(check())
