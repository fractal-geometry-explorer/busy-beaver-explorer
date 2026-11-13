"""The step map of 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC, by simulating one step per (wall, parity), and its orbit.

A step starts at  W A> 0 b^N 1  (b = 110, blank on both sides, W the "wall", a word ending in 1).  The head moves
the block b^N across a junction two copies at a time, three copies coming out (N' about 3N/2), and the parity of N
decides how the step ends and what the wall becomes.  For each (W, N mod 2) the next step is (W', (3N + c)/2) with
(W', c) depending only on (W, N mod 2): checked here on three values of N per case (c/stepc.c runs one step).

usage:
  python3 stepmap.py orbit STEPS     iterate the map from the step start  1 A> 0 b^468 1  (step 1,133,743 of the run)
  python3 stepmap.py graph WALLS     breadth-first search of the walls reachable with either parity

"""
import os
import subprocess
import sys
import tempfile
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "c", "stepc.c")
BIN = os.path.join(tempfile.gettempdir(), "h3292_stepc")
B = (1, 1, 0)


def build():
    if not os.path.exists(BIN) or os.path.getmtime(BIN) < os.path.getmtime(SRC):
        subprocess.run(["gcc", "-O2", "-o", BIN, SRC], check=True)


def run_step(W, N):
    out = subprocess.run([BIN, "".join(map(str, W)), str(N)], capture_output=True, text=True).stdout.split()
    if out[0] == "HALT":
        return ("halt", int(out[1]))
    return (tuple(int(c) for c in out[0]), int(out[1]), int(out[2]))


MEMO = {}


def trans(W, par):
    """(W', a, c) with N' = a N + c for every large enough N of parity par, or ('halt', N, steps)."""
    key = (W, par)
    if key not in MEMO:
        pts = []
        for t in range(3):
            n = 2 * (len(W) + 10 + t) + par
            r = run_step(W, n)
            if r[0] == "halt":
                MEMO[key] = ("halt", n, r[1])
                return MEMO[key]
            pts.append((n, r[0], r[1]))
        assert len(set(p[1] for p in pts)) == 1, (W, par, pts)
        a = Fraction(pts[1][2] - pts[0][2], pts[1][0] - pts[0][0])
        c = pts[0][2] - a * pts[0][0]
        assert a * pts[2][0] + c == pts[2][2]
        MEMO[key] = (pts[0][1], a, c)
    return MEMO[key]


def show(W):
    s = "".join(map(str, W))
    out, i = [], 0
    while i < len(s):
        if s.startswith("110", i):
            j = i
            while s.startswith("110", j):
                j += 3
            k = (j - i) // 3
            out.append("b" if k == 1 else f"b^{k}")
            i = j
        else:
            j = i
            while j < len(s) and s[j] == s[i] and not s.startswith("110", j):
                j += 1
            out.append(s[i] if j - i == 1 else f"{s[i]}^{j - i}")
            i = j
    return " ".join(out)


def orbit(steps, verbose=True):
    W, N = (1,), 468
    seen, maxlen = {}, 0
    for i in range(1, steps + 1):
        r = trans(W, N & 1)
        if r[0] == "halt":
            print("HALT in step", i, show(W))
            return
        W, a, c = r
        N = int(a * N + c)
        seen[W] = seen.get(W, 0) + 1
        if verbose and len(W) > maxlen:
            maxlen = len(W)
            print(f"step {i}: N has {N.bit_length()} bits, new longest wall {show(W)}", flush=True)
    print(f"{steps} steps, no halt; N has {N.bit_length()} bits; {len(seen)} distinct walls; the commonest:")
    for w, k in sorted(seen.items(), key=lambda x: -x[1])[:25]:
        print(f"  {k:8d}  {show(w)}")
    return W, N


def graph(limit):
    start = (1,)
    dist, queue, halts = {start: 0}, [start], []
    while queue and len(dist) < limit:
        W = queue.pop(0)
        for par in (0, 1):
            r = trans(W, par)
            if r[0] == "halt":
                halts.append((show(W), par))
                continue
            if r[0] not in dist:
                dist[r[0]] = dist[W] + 1
                queue.append(r[0])
    print(f"{len(dist)} walls, halting (wall, parity): {halts or 'none'}")


if __name__ == "__main__":
    build()
    cmd, arg = sys.argv[1], int(sys.argv[2])
    {"orbit": orbit, "graph": graph}[cmd](arg)
