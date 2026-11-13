"""Closed tape language from windows of RUNS, for 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---.

Each side of the head is abstracted by its nearest K maximal runs of alternating cells (the right side includes the
head's cell).  A run is kept as its exact length if it is shorter than T, else only as its length mod 4.  A window
is (bit of the nearest cell, classes of the nearest runs, end), end = '#' (blank beyond) or '*' (anything beyond).
The streams are read up to their last 1, so the blank stream is the window with no runs.  Putting a cell in front of
a stream changes its window in a way that depends only on the window (`push`); taking the nearest cell off gives
every known window that pushes back to it (as in n-gram CPS).  `search` closes the set of (state, left window,
right window) under the machine's steps from the blank tape, and stops at the first one that can halt.

usage (from the repo root):
  python3 holdouts/<M>/py/closure/runcps.py K T [KR] [MAXCONFIGS]
"""
import sys
import time
from collections import defaultdict, deque

M = "1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---"


def parse(m):
    t = {}
    for s, part in enumerate(m.split("_")):
        for r in range(2):
            x = part[3 * r:3 * r + 3]
            t[(s, r)] = None if x[2] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65)
    return t


BLANK = (0, (), "#")


class Side:
    def __init__(self, k, t, mod=4):
        self.k, self.t, self.mod = k, t, mod
        self.known = set()
        self.back = defaultdict(set)     # window -> {(x, w')} with push(x, w') == window, w' known
        self.add(BLANK)

    def inc(self, c):
        t = self.t
        if c < t - 1:
            return c + 1
        if c == t - 1:
            return t + t % self.mod
        return t + (c - t + 1) % self.mod

    def push(self, x, w):
        b, rs, end = w
        if not rs:
            return ((1, (1,), "#") if x else BLANK)
        if x != b:
            return (x, (self.inc(rs[0]),) + rs[1:], end)
        rs = (1,) + rs
        if len(rs) > self.k:
            return (x, rs[:self.k], "*")
        return (x, rs, end)

    def add(self, w):
        """Add a window; returns the windows whose set of pops grew."""
        if w in self.known:
            return []
        self.known.add(w)
        ch = []
        for x in (0, 1):
            v = self.push(x, w)
            self.back[v].add((x, w))
            ch.append(v)
        return ch

    def pops(self, w):
        return self.back.get(w, ())


def search(k, t, kr=None, maxconf=3_000_000, tm=M, verbose=True, mod=4):
    T = parse(tm)
    L, R = Side(k, t, mod), Side(kr or k, t, mod)
    S = {}
    usesL, usesR = defaultdict(set), defaultdict(set)
    q = deque()
    t0 = time.time()

    def addconf(c, parent):
        if c in S:
            return
        S[c] = parent
        usesL[c[1]].add(c)
        usesR[c[2]].add(c)
        q.append(c)
        for v in L.add(c[1]):
            for d in usesL.get(v, ()):
                q.append(d)
        for v in R.add(c[2]):
            for d in usesR.get(v, ()):
                q.append(d)

    addconf((0, BLANK, BLANK), None)
    halt = None
    while q:
        c = q.popleft()
        st, wl, wr = c
        for x, wr1 in list(R.pops(wr)):
            tr = T[(st, x)]
            if tr is None:
                halt = (c, x, wr1)
                break
            w, d, s2 = tr
            if d == 1:
                addconf((s2, L.push(w, wl), wr1), c)
            else:
                r2 = R.push(w, wr1)
                for v in R.add(r2):          # the stream behind the head's new cell is a stream of the run too
                    for d2 in usesR.get(v, ()):
                        q.append(d2)
                for y, wl1 in list(L.pops(wl)):
                    addconf((s2, wl1, R.push(y, r2)), c)
        if halt:
            break
        if len(S) > maxconf:
            return "LIMIT", S, L, R, None
    if verbose:
        print(f"K={k} KR={kr or k} T={t}: {'HALT reachable' if halt else 'CLOSED'}; {len(S)} configs, "
              f"{len(L.known)} left windows, {len(R.known)} right windows, {time.time() - t0:.1f} s", flush=True)
    return ("HALT" if halt else "CLOSED"), S, L, R, halt


def path(S, c):
    out = []
    while c is not None:
        out.append(c)
        c = S[c]
    return out[::-1]


def fmt(c):
    st, wl, wr = c
    def w(x, rev):
        b, rs, end = x
        rs = [str(r) for r in rs]
        if rev:
            return f"{end} {' '.join(reversed(rs))} .{b}"
        return f"{b}. {' '.join(rs)} {end}"
    return f"{w(wl, True)} [{'ABCDEF'[st]}] {w(wr, False)}"


if __name__ == "__main__":
    k, t = int(sys.argv[1]), int(sys.argv[2])
    kr = int(sys.argv[3]) if len(sys.argv) > 3 else None
    mc = int(sys.argv[4]) if len(sys.argv) > 4 else 3_000_000
    res, S, L, R, halt = search(k, t, kr, mc)
    if res == "LIMIT":
        print("LIMIT", len(S))
    if halt:
        p = path(S, halt[0])
        print("abstract path to the halting configuration:", len(p), "configurations; last 40:")
        for c in p[-40:]:
            print("  ", fmt(c))
