"""The step map of 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC as lean/Reduction.lean defines it (`stepMap`).

A step starts at  W A> 0 b^N 1  (b = 110).  It has three parts:
  1. the head crosses the block and builds the junction  L 1 b^x 111 F> b^(y+1) 1  with x = N - const;
  2. the transfer loop: x // 2 sweeps, each moving two copies of b out of the left block and three into the right;
  3. the end of the step works on the wall and leaves  W' A> 0 b^N' 1.
Parts 1 and 3 are computed by a zone simulator: the middle of the long block of b's is "the block", which the head
only crosses whole by one of three shift rules, so the computation never looks at the number of copies in it (the
copies kept outside it, B1, B2, B below, are buffers the head may work in cell by cell).  lean/Zone.lean proves
that whatever this simulator answers is what the machine does.  Answers: (W', N'), 'halt', or 'stuck' (N too
small for the buffers, a meeting with the block that no rule covers, or fuel; never seen along the orbit).

Walls are kept as the list of cells from the head leftwards (so the wall `1^4 b 1` is 1 0 1 1 1 1 1 1 here).

usage:
  python3 zonemap.py check STEPS     compare with stepmap.py (plain simulation in C) along the orbit from (1, 468)
  python3 zonemap.py graph MAXLEN    breadth-first search of the walls of at most MAXLEN cells reachable from `1`
                                     with either parity of N; reports the steps that halt or get stuck
  python3 zonemap.py orbit STEPS     iterate from the step start at step 10,206 of the run from blank tape
"""
import sys

M = "1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC"
A, B_, C, D, E, F = range(6)


def parse(text):
    tab = []
    for g in text.split("_"):
        row = []
        for y in (0, 1):
            s = g[3 * y:3 * y + 3]
            row.append(None if s[2] not in "ABCDEF" else (int(s[0]), 1 if s[1] == "R" else -1, "ABCDEF".index(s[2])))
        tab.append(row)
    return tab


TAB = parse(M)
# (state, u, w, v): rightwards  L u q> w^k R -> L v^k u q> R  (u, v nearest the head first);
#                   leftwards   L w^k q> u R -> L q> u v^k R  (w nearest the head first)
RULES_R = [(C, [0], [1, 1, 0], [0, 1, 1]), (A, [0, 1, 1, 0], [1, 1, 0], [1, 1, 1])]
RULES_L = [(F, [1], [1, 1, 1], [1, 1, 0])]
START = ((1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1), 48)     # step 10,206 of the run: 11101101111101 A> 0 b^48 1


def find(rules, q, m, ctx):
    for r in rules:
        if r[0] == q and r[2] == m and ctx[:len(r[1])] == r[1]:
            return r
    return None


def arun(c, stop, fuel):
    """The simulator `arun` of lean/Zone.lean.  Inside, `a` and `b` are kept reversed (nearest cell last)."""
    z, a, b, m, o, q = c
    a, b = a[::-1], b[::-1]
    for _ in range(fuel):
        if z == "L":
            if not b:
                r = find(RULES_R, q, m, a[:-6:-1])
                if r is None:
                    return ("stuck",)
                k = len(r[1])
                z, a, b, m, o = "R", a[len(a) - k:], o[::-1], r[3], a[len(a) - k - 1::-1] if len(a) > k else []
            else:
                tr = TAB[q][b[-1]]
                if tr is None:
                    return ("halt",)
                w, d, q = tr
                if d > 0:
                    b.pop()
                    a.append(w)
                else:
                    b[-1] = w
                    b.append(a.pop() if a else 0)
        else:
            r = find(RULES_L, q, m, b[:-6:-1]) if not a else None
            if r is not None:
                k = len(r[1])
                z, a, b, m, o = "L", o[::-1], b[len(b) - k:], r[3], b[len(b) - k - 1::-1] if len(b) > k else []
            else:
                tr = TAB[q][b[-1] if b else 0]
                if tr is None:
                    return ("halt",)
                w, d, q = tr
                if d > 0:
                    if b:
                        b.pop()
                    a.append(w)
                elif not a:
                    return ("stuck",)
                else:
                    if b:
                        b[-1] = w
                    else:
                        b.append(w)
                    b.append(a.pop())
        if q == stop.state and z == stop.zone and m == stop.word and stop.pre(a, b):
            s = stop(z, a[::-1], b[::-1], m, o, q)
            if s is not None:
                return ("ok", s)
    return ("stuck",)


def cnt(w, l):
    n = 0
    while l[3 * n:3 * n + 3] == w:
        n += 1
    return n, l[3 * n:]


def trim(l):
    l = list(l)
    while l and l[-1] == 0:
        l.pop()
    return l


def decode_j(z, a, b, m, o, q):
    if not (z == "R" and q == F and m == [0, 1, 1] and a[:3] == [1, 1, 1]):
        return None
    i, r = cnt([0, 1, 1], a[3:])
    j, ro = cnt([0, 1, 1], o)
    y, rb = cnt([1, 1, 0], b)
    if r or ro[:1] != [1] or y < 1 or trim(rb) != [1]:
        return None
    return (i + j, y - 1, ro[1:])


def decode_s(z, a, b, m, o, q):
    if not (z == "L" and q == A and m == [1, 1, 0] and b[:1] == [0]):
        return None
    i, r = cnt([1, 1, 0], b[1:])
    j, ro = cnt([1, 1, 0], o)
    if r or trim(ro) != [1]:
        return None
    return (i + j, tuple(trim(a)))


decode_j.state, decode_j.zone, decode_j.word = F, "R", [0, 1, 1]
decode_j.pre = lambda a, b: a[-3:] == [1, 1, 1] and b[-3:] == [0, 1, 1]      # reversed lists: nearest cell last
decode_s.state, decode_s.zone, decode_s.word = A, "L", [1, 1, 0]
decode_s.pre = lambda a, b: b[-1:] == [0]


def fuel(n):
    return 200 * (n + 20) ** 2


MEMO1, MEMO2 = {}, {}


def step_map(W, N):
    b1, b2 = len(W) + 2, len(W) + 14
    if N < b1 + b2:
        return ("stuck",)
    if W not in MEMO1:
        MEMO1[W] = arun(("L", list(W), [0] + [1, 1, 0] * b1, [1, 1, 0], [1, 1, 0] * b2 + [1], A), decode_j,
                        fuel(len(W)))
    r = MEMO1[W]
    if r[0] != "ok":
        return r
    x, y, L = r[1]
    X = N - (b1 + b2) + x
    Y = y + 3 * (X // 2)
    bb = len(L) + 14
    if Y + 1 < 2 * bb:
        return ("stuck",)
    key = (X % 2, tuple(L))
    if key not in MEMO2:
        MEMO2[key] = arun(("L", [1, 1, 1] + [0, 1, 1] * (X % 2) + [1] + L, [1, 1, 0] * bb, [1, 1, 0],
                           [1, 1, 0] * bb + [1], F), decode_s, fuel(len(L)))
    r = MEMO2[key]
    if r[0] != "ok":
        return r
    return (r[1][1], Y + 1 - 2 * bb + r[1][0])


def show(W):
    return "".join(map(str, reversed(W)))


def orbit(steps):
    W, N = START
    seen = set()
    for i in range(1, steps + 1):
        r = step_map(W, N)
        if len(r) == 1:
            print(f"{r[0].upper()} in step {i}: wall {show(W)}, N mod 2 = {N % 2}")
            return
        W, N = r
        seen.add(W)
        if i <= 12:
            print(f"orbit {i}: wall {show(W)}, N = {N}")
        if i % 20000 == 0:
            print(f"step {i}: N has {N.bit_length()} bits, {len(seen)} walls so far", flush=True)
    print(f"{steps} steps: no halt, never stuck; N has {N.bit_length()} bits; {len(seen)} distinct walls, "
          f"the longest of {max(map(len, seen))} cells")


def check(steps):
    import os
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import stepmap
    stepmap.build()
    W, N = (1,), 468
    for i in range(steps):
        Wf, a, c = stepmap.trans(tuple(reversed(W)), N & 1)
        want = (tuple(reversed(Wf)), int(a * N + c))
        got = step_map(W, N)
        if got != want:
            print("MISMATCH at step", i, show(W), N % 2, got[:1])
            return
        W, N = got
    print(f"zone map and plain simulation agree for {steps} steps from (1, 468); N has {N.bit_length()} bits")


def graph(maxlen):
    dist, queue, out, cases = {(1,): 0}, [(1,)], {"halt": [], "stuck": []}, 0
    while queue:
        W = queue.pop(0)
        for par in (0, 1):
            r = step_map(W, 10 ** 7 + par)
            cases += 1
            if len(r) == 1:
                out[r[0]].append((show(W), par))
            elif r[0] not in dist and len(r[0]) <= maxlen:
                dist[r[0]] = dist[W] + 1
                queue.append(r[0])
    print(f"{len(dist)} walls of at most {maxlen} cells, {cases} steps: halting {out['halt'] or 'none'}, "
          f"stuck {out['stuck'] or 'none'}")


if __name__ == "__main__":
    {"orbit": orbit, "check": check, "graph": graph}[sys.argv[1]](int(sys.argv[2]))
