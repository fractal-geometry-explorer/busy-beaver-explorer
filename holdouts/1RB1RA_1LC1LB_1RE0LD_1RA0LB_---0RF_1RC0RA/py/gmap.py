"""The map G of lean/Map.lean for 1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA, with the machine's step counts,
and a check of both against a direct run of the machine.

A node is ('e', fs, b, rest) = `lfin fs  E> 1^b 00 rbl rest`  or  ('s', fs, m, rest) = `lfin fs  B> 0 1^m 00 rbl rest`
(fs: blocks left of the head, nearest first, separated by one 0; rest: blocks further right, separated by 00).

usage: python3 gmap.py run N        print the first N nodes of the orbit of blank tape, with step counts
       python3 gmap.py check N      compare the first N nodes with a direct simulation, cell by cell
"""
import sys

M = "1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA"
START = ("s", (), 3, ())      # B> 0 1 1 1, reached from blank tape in 8 steps
START_STEPS = 8


def inc(j, l):
    return (l[0] + j,) + tuple(l[1:]) if l else (j,)


def G(x):
    """(next node, machine steps), or None when the machine halts from x."""
    mode, fs, b, rest = x
    c = rest[0] if rest else 0
    rt = tuple(rest[1:])
    if mode == "e":
        if b == 0:
            return None
        j = (b - 1) // 2
        b0 = b - 2 * j                      # 1 or 2: what is left after j rounds
        rounds = 2 * b0 * j + 2 * j * (j + 1) + 3 * j
        if b % 2 == 1:
            return ("e", (2,) + inc(j, fs), c + j, rt), rounds + 3
        return ("s", inc(j, fs), c + j + 3, rt), rounds + 10
    if not fs:
        return ("e", (1,), b + 1, rest), 2
    f, t = fs[0], tuple(fs[1:])
    if f == 0:
        return ("e", inc(1, t), b + 1, rest), 2
    if f == 1:
        h = t[0] if t else 0
        return ("s", tuple(t[1:]), h + b + 3, rest), h + 7
    return ("s", t, f - 2, (b + 1,) + tuple(rest)), f + 1


def cells(x):
    mode, fs, b, rest = x
    left = []
    for f in fs:
        left += [1] * f + [0]
    right = ([0] if mode == "s" else []) + [1] * b
    for c in rest:
        right += [0, 0] + [1] * c
    while left and left[-1] == 0:
        left.pop()
    while right and right[-1] == 0:
        right.pop()
    return left, right, "B" if mode == "s" else "E"


def check(n):
    tr = {}
    for i, row in enumerate(M.split("_")):
        for s in range(2):
            w = row[3 * s:3 * s + 3]
            tr[(chr(65 + i), s)] = None if w[0] == "-" else (int(w[0]), 1 if w[1] == "R" else -1, w[2])
    tape, pos, st, step = {}, 0, "A", 0
    x, at = START, START_STEPS
    for i in range(n):
        while step < at:
            w, d, st2 = tr[(st, tape.get(pos, 0))]
            tape[pos] = w
            pos += d
            st = st2
            step += 1
        ks = [k for k, v in tape.items() if v] + [pos]
        left = [tape.get(k, 0) for k in range(pos - 1, min(ks) - 1, -1)]
        right = [tape.get(k, 0) for k in range(pos, max(ks) + 1)]
        while left and left[-1] == 0:
            left.pop()
        while right and right[-1] == 0:
            right.pop()
        assert (left, right, st) == cells(x), (i, step, x)
        r = G(x)
        assert r is not None
        x, at = r[0], at + r[1]
    print(f"{n} nodes of the orbit agree with the machine, cell by cell, up to step {step}")


def main():
    cmd, n = sys.argv[1], int(sys.argv[2])
    if cmd == "check":
        return check(n)
    x, at = START, START_STEPS
    for i in range(n):
        print(at, x)
        r = G(x)
        if r is None:
            print("halts")
            return
        x, at = r[0], at + r[1]


if __name__ == "__main__":
    main()
