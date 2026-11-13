"""The maps G and GA of lean/Map.lean for 1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB, with the machine's step counts,
and a check of both against a direct run of the machine.

A node is (gs, bs) = `... 0 1^g2 0 1^g1  B> 0  1^b0 000 1^b1 000 ...`: gs the blocks left of the head (nearest
first, separated by one 0), bs the blocks right of it (separated by 000; b0 may be 0).

usage: python3 vmap.py run N          the first N nodes of the orbit of blank tape under G, with step counts
       python3 vmap.py fast N         the same under GA (the transfer loop done at once)
       python3 vmap.py check N        compare the first N nodes under G with a direct simulation, cell by cell,
                                      and check that the orbit under GA is a subsequence of it (same step counts)
"""
import sys

M = "1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB"
SIB = True                 # the rule for a block of one 1 differs between the two sibling machines
START = ((1,), ())            # 1 B> 0, the configuration after the first step from blank tape
START_STEPS = 1


def inc(j, l):
    return (l[0] + j,) + tuple(l[1:]) if l else (j,)


def G(x, fast=False):
    """(next node, machine steps), or None when the machine halts from x."""
    gs, bs = x
    if not gs or gs[0] == 0:
        return None
    k, t = gs[0], tuple(gs[1:])
    b = bs[0] if bs else 0
    bt = tuple(bs[1:])
    g = t[0] if t else 0
    if k == 1:
        if SIB:
            return ((g + b + 4,) + inc(1, t[1:]), bt), 2 * g + b + 13
        return ((g + b + 3,) + inc(2, t[1:]), bt), 4 * g + b + 13
    if k == 2:
        return ((b + 2, g + 2) + inc(1, t[1:]), bt), 2 * g + b + 11
    if k == 3:
        return (t, (0,) + inc(1, bs)), 4
    if fast and b == 0:
        f = 2 + k % 2
        j = (k - f) // 2
        return ((f,) + inc(j, t), (0,) + inc(j, bt)), 2 * k * j - 2 * j * (j - 1) + 15 * j
    return ((b + 3, k - 2) + inc(1, t), bt), 2 * k + b + 11


def cells(x):
    gs, bs = x
    left, right = [], [0]
    for f in gs:
        left += [1] * f + [0]
    for c in bs:
        right += [1] * c + [0, 0, 0]
    while left and left[-1] == 0:
        left.pop()
    while right and right[-1] == 0:
        right.pop()
    return left, right


def check(n):
    tr = {}
    for i, row in enumerate(M.split("_")):
        for s in range(2):
            w = row[3 * s:3 * s + 3]
            tr[(chr(65 + i), s)] = None if w[0] == "-" else (int(w[0]), 1 if w[1] == "R" else -1, w[2])
    tape, pos, st, step = {}, 0, "A", 0
    x, at = START, START_STEPS
    seen = {}
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
        assert st == "B" and (left, right) == cells(x), (i, step, x)
        seen[at] = cells(x)
        r = G(x)
        assert r is not None
        x, at = r[0], at + r[1]
    last = max(seen)
    print(f"{n} nodes of the orbit under G agree with the machine, cell by cell, up to step {step}")
    x, at, m = START, START_STEPS, 0
    while at <= last:
        assert seen.get(at) == cells(x), (at, x)
        r = G(x, fast=True)
        x, at, m = r[0], at + r[1], m + 1
    print(f"the orbit under GA is a subsequence of it: {m} nodes, same step counts")


def main():
    cmd, n = sys.argv[1], int(sys.argv[2])
    if cmd == "check":
        return check(n)
    x, at = START, START_STEPS
    for i in range(n):
        print(at, x)
        r = G(x, fast=(cmd == "fast"))
        if r is None:
            print("halts")
            return
        x, at = r[0], at + r[1]


if __name__ == "__main__":
    main()
