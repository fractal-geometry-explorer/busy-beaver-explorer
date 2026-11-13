"""The inner counter of 1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD (`g` of lean/Counter.lean), and a check against
the edge events of the accelerated simulator.

A cycle, between two edge events of the run:
  R F  `1 (01)^N 0 0 F>`          the inner counter starts, X(N, 1, 0)
  L A  `A> 0 x (01)^m (11)^s`     its end, (x, m, s) = g(N, 1, 0)                         (proved: lean/Counter.lean)
then, read off the run (trusted, checked here on every event):
  x = 0, m even:  R F with N' = m + 2s + 3                     (the counter starts again)
  x = 0, m odd:   R E `1 (01)^(m+2) 0^(2s+2) 01 E>`            (the E-phase: a counter on the zeros, not decoded)
  x = 1, s ones even (2s):  R A `1 (01)^(m+2s) 0 A>`, then C(2(m+2s)+4)   (the next cycle)
and after an E-phase `A> 0 1 (01)^m 1^k` or `E> (01)^m 1^k` (k ones):  k even -> C(2(m+k)+4); k odd -> R F with
N' = m + k - 1.

usage: python3 counter.py EVENTS     EVENTS: output of `wrsim M 01 ...` (mode 0) or of tools edges with the same events
"""
import re
import sys


def g(p, q, r):
    """End of the inner counter from X(p, q, r), q >= 1: (x, m, s), as in lean/Counter.lean."""
    while True:
        if p == 0 and r == 0:
            return (1, 1, q + 1)
        if p == 0:
            return (0, q + 2, r - 1)
        if p == 1 and r > 0:
            return (1, q + 3, r - 1)
        if r == 0:
            p, q, r = p - 1, 1, q + 1
            continue
        t = min(r, p // 2)  # p >= 2, r >= 1: t >= 1 rounds at once
        p, q, r = p - 2 * t, q + 3 * t, r - t


def parse(line):
    f = line.split()
    toks = []
    for t in f[3:]:
        if t in "<>":
            continue
        w, _, c = t.partition("^")
        toks.append((w, int(c) if c else 1))
    return int(f[0]), f[1], f[2], toks


def main(argv):
    ev = [parse(l) for l in open(argv[0]) if l[:1].isdigit()]
    checked = bad = 0
    for a, b in zip(ev, ev[1:]):
        if a[1] == "R" and a[2] == "F":
            toks = a[3]
            assert toks[0] == ("1", 1) and toks[1][0] == "01" and toks[2] == ("0", 2), toks
            N = toks[1][1]
            x, m, s = g(N, 1, 0)
            want = ([("0", 1)] if x == 0 else [("1", 1)]) + ([("01", m)] if m else []) + ([("1", 2 * s)] if s else [])
            # the event prints the tape after the head cell: `0 x (01)^m 1^2s` with the leading blank not shown
            got = b[3]
            ok = b[1] == "L" and b[2] == "A" and got == want
            checked += 1
            bad += not ok
            if not ok:
                print("mismatch", a[0], N, (x, m, s), got)
    print(f"inner counter g against the run: {checked} starts, {bad} mismatches")
    checked = bad = 0
    for a, b in zip(ev, ev[1:]):
        if a[1] != "L" or a[2] == "B":
            continue
        t = list(a[3])
        lead = None
        if t and t[0] in (("0", 1), ("1", 1)):
            lead = t.pop(0)[0]
        m = t.pop(0)[1] if t and t[0][0] == "01" else 0
        k = t.pop(0)[1] if t and t[0][0] == "1" else 0
        assert not t, a
        if lead == "0" and k % 2 == 0 and m % 2 == 0:
            want = ("R", "F", [("1", 1), ("01", m + k + 3), ("0", 2)])
        elif lead == "0" and k % 2 == 0:
            want = ("R", "E", [("1", 1), ("01", m + 2), ("0", k + 2), ("01", 1)])
        elif lead != "0" and k % 2 == 0:
            want = ("R", "A", [("1", 1), ("01", m + k), ("0", 1)])
        elif lead != "0":
            want = ("R", "F", [("1", 1), ("01", m + k - 1), ("0", 2)])
        else:
            want = None
        ok = want is not None and (b[1], b[2], b[3]) == want
        checked += 1
        bad += not ok
        if not ok:
            print("transition mismatch", a, b)
    print(f"transitions from the left end: {checked} events, {bad} mismatches")


if __name__ == "__main__":
    main(sys.argv[1:])
