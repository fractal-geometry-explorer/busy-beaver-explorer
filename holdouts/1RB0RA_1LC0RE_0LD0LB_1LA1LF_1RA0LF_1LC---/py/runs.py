"""Run-list configurations of 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---: build a trip start from a list of run
lengths, read the list back, run to the next trip start, and trace the turns of the head inside an irregular event.

A *trip start* is state A on the leftmost visited cell (a 0) with blank tape to its left.  The tape from that cell to
the last 1 is cut into maximal runs of alternating cells; the first run starts with 0.  `canon(runs)` is that list
(rsim.Sim.runs() also counts visited 0 cells past the last 1; canon drops them).

usage (from the repo root):
  python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/runs.py trace "187 97 2 31 25 7 7" [MAXMOVES]
prints the configuration at every turn of the head until the next trip start (or HALT).
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rsim import Sim, A, B, C, D, E, F  # noqa: E402


def cells(runs):
    out, b = [], 0
    for i, n in enumerate(runs):
        if i:
            b = out[-1]          # doubled cell
        for j in range(n):
            out.append(b ^ (j & 1))
    return out


def runs_of(cs):
    while cs and cs[-1] == 0:
        cs = cs[:-1]
    out = []
    for i, c in enumerate(cs):
        if i and cs[i - 1] != c:
            out[-1] += 1
        else:
            out.append(1)
    return out


def canon(runs):
    return runs_of(cells(runs))


def start(runs):
    """Sim at a trip start with the given run list (lengths left to right, first run starting with 0)."""
    cs = cells(runs)
    while cs and cs[-1] == 0:
        cs.pop()
    s = Sim()
    assert cs and cs[0] == 0
    s.h = cs[0]
    # R is stored right to left, as [start bit, length] of maximal runs
    rr, i = [], 1
    while i < len(cs):
        j = i
        while j + 1 < len(cs) and cs[j + 1] != cs[j]:
            j += 1
        rr.append([cs[i], j - i + 1])
        i = j + 1
    s.R = rr[::-1]
    return s


def sim_runs(s):
    """The canonical run list of a Sim at a trip start (expands the cells: meant for small tapes)."""
    return runs_of(cells(s.runs()))


def next_trip(runs, maxmoves=10**7):
    """(status, runs, steps): status 'trip' (next trip start reached), 'halt', or 'budget'."""
    s = start(runs)
    for _ in range(maxmoves):
        if not s.step():
            return "halt", sim_runs_any(s), s.steps + 1
        if s.at_left():
            return "trip", sim_runs(s), s.steps
    return "budget", None, s.steps


def sim_runs_any(s):
    cs = []
    for b, n in s.L:
        cs += [b ^ (j & 1) for j in range(n)]
    cs.append(s.h)
    for b, n in reversed(s.R):
        cs += [b ^ (j & 1) for j in range(n)]
    return runs_of(cs)


def show(s):
    """Run lengths left of the head, [state bit], run lengths right of the head (maximal runs on each side)."""
    def side(rs):
        cs = []
        for b, n in rs:
            cs += [b ^ (j & 1) for j in range(n)]
        return cs
    l = side(s.L)
    r = side(list(reversed(s.R)))
    while r and r[-1] == 0:
        r.pop()
    def rl(cs):
        out = []
        for i, c in enumerate(cs):
            if i and cs[i - 1] != c:
                out[-1][1] += 1
            else:
                out.append([c, 1])
        return " ".join(f"{n}" for b, n in out), (out[0][0] if out else "-"), (out[-1][0] if out else "-")
    ls, lb, le = rl(l)
    rs_, rb, re_ = rl(r)
    return f"{ls} .{le} [{'ABCDEF'[s.st]}{s.h}] {rb}. {rs_}"


def trace(runs, maxmoves=10**6, out=sys.stdout):
    s = start(runs)
    last = 0
    print(0, show(s), file=out)
    for _ in range(maxmoves):
        p = s.pos
        if not s.step():
            print("HALT after", s.steps + 1, show(s), file=out)
            return
        d = 1 if s.pos > p else -1
        if d != last and last:
            print(s.steps, show(s), file=out)
        last = d
        if s.at_left():
            print("TRIP", s.steps, sim_runs(s), file=out)
            return
    print("budget", file=out)


if __name__ == "__main__":
    if sys.argv[1] == "trace":
        trace([int(x) for x in sys.argv[2].split()], int(sys.argv[3]) if len(sys.argv) > 3 else 10**6)
