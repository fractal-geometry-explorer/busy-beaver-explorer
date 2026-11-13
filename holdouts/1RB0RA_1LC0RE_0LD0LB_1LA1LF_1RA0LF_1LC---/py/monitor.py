"""Monitor the real run of 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC--- trip by trip (exact run-length simulator rsim).

At every trip start (A on the leftmost cell) the list of maximal runs is abstracted run by run: a run shorter than T
keeps its length, a longer one only its length mod 4 (`n` or `>=r`).  Collected:
  * the set of windows of W consecutive run classes (with `^` before the first run and `$` after the last), and the
    step at which each window is first seen: a candidate regular invariant G(T, W);
  * every transfer.  A shuttle ends with D reading a 0 at the right end of the run being moved; transfers nest (a
    shuttle of an outer transfer can turn into a whole inner transfer), so the shuttles of a trip are grouped by
    level = the number of runs left of the head at that turn.  For every level with at least 3 shuttles:
    m = its number of shuttles, sat = how many of its last shuttles were saturated (consecutive, each extending
    the tape by exactly 2 cells, as in lean/Transfer.lean `shuttle`).  The candidate quantitative condition is
    Q: sat >= 1 at every level (the moved run outlasts the saturation of the tail);
  * the residues mod 4 of digit 0 (r0, r1) and of the pairs (x_k, y_k), k >= 1, as counts;
  * the times D reads a 1, by the length k of the alternating stretch ending there (a halt is k = 1).

usage (from the repo root):
  python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/monitor.py STEPS OUT.json [T] [W] [GRAMMAR.json]
With GRAMMAR.json (an earlier OUT.json) every trip start is also checked against that window set and violations are
counted.  OUT.json is rewritten every 10^13 steps (a checkpoint of the statistics, not of the simulation).
"""
import collections
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rsim import Sim, D  # noqa: E402


def canon(r):
    """The run list up to the last 1 (rsim's list also counts visited 0 cells at the right end)."""
    r = list(r)
    while r:
        # last cell of the last run: the first run starts with 0; run i+1 starts with the last bit of run i
        b = 0
        for x in r[:-1]:
            b ^= (x - 1) & 1
        if (b ^ ((r[-1] - 1) & 1)) == 1:
            break
        r[-1] -= 1
        if r[-1] == 0:
            r.pop()
    return r


def classes(r, T):
    return tuple(str(x) if x < T else ">=%d" % (x % 4) for x in r)


def windows(cl, W):
    seq = ("^",) + cl + ("$",)
    if len(seq) <= W:
        return [seq]
    return [seq[i:i + W] for i in range(len(seq) - W + 1)]


def main():
    n = float(sys.argv[1])
    out = sys.argv[2]
    T = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    W = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    grammar = None
    if len(sys.argv) > 5:
        grammar = set(tuple(w) for w in json.load(open(sys.argv[5]))["windows"])
    s = Sim()
    seen = {}
    dk = collections.Counter()
    dig0 = collections.Counter()
    digk = collections.Counter()
    transfers = []
    viol = 0
    trips = 0
    d0 = []            # hi at every D-reads-0 event of this trip
    cur = None
    minmargin = None
    maxratio = 0.0
    nextck = 1e13
    t0 = time.time()

    def dump():
        json.dump({"steps": s.steps, "trips": trips, "T": T, "W": W,
                   "windows": sorted(seen), "first_seen": {" ".join(k): v for k, v in seen.items()},
                   "last_new_window_step": max(seen.values()) if seen else 0,
                   "D_reads_1_by_k": {str(k): v for k, v in sorted(dk.items())},
                   "digit0_residues": {"%d,%d" % k: v for k, v in sorted(dig0.items())},
                   "digitk_residues": {"%d,%d" % k: v for k, v in sorted(digk.items())},
                   "transfer_levels": len(transfers), "min_sat": minmargin, "max_unsat_fraction": maxratio,
                   "rows": "trip, step, level, shuttles, saturated at the end",
                   "grammar_violations": viol if grammar is not None else None,
                   "transfer_rows": transfers[:400] + transfers[-200:],
                   "seconds": round(time.time() - t0)}, open(out, "w"))

    while s.steps < n:
        if s.st == D:
            if s.h == 1:
                if s.L:
                    b, m = s.L[-1]
                    k = 1 if (b ^ ((m - 1) & 1)) == 1 else 1 + m
                else:
                    k = 1
                dk[min(k, 12)] += 1
            else:
                d0.append((s.hi, len(s.L)))
        if not s.step():
            print("HALT after", s.steps + 1, "steps")
            dump()
            return
        if s.at_left():
            trips += 1
            if len(d0) >= 4 and cur is not None:
                lev = collections.defaultdict(list)
                for i, (hi, k) in enumerate(d0[:-1]):        # the last one is the turn at the left end of the tape
                    lev[k].append((i, hi))
                for k, ev in lev.items():
                    if len(ev) < 3:
                        continue
                    sat = 0
                    for a in range(len(ev) - 1, 0, -1):
                        if ev[a][0] - ev[a - 1][0] == 1 and ev[a][1] - ev[a - 1][1] == 2:
                            sat += 1
                        else:
                            break
                    row = [trips, s.steps, k, len(ev), sat]
                    transfers.append(row)
                    if minmargin is None or sat < minmargin:
                        minmargin = sat
                    maxratio = max(maxratio, (len(ev) - sat) / len(ev))
            d0 = []
            cur = canon(s.runs())
            cl = classes(cur, T)
            if len(cur) >= 2:
                dig0[(cur[0] % 4, cur[1] % 4)] += 1
            for i in range(2, len(cur) - 1, 2):
                digk[(cur[i] % 4, cur[i + 1] % 4)] += 1
            for w in windows(cl, W):
                if w not in seen:
                    seen[w] = s.steps
                if grammar is not None and w not in grammar:
                    viol += 1
            if s.steps >= nextck:
                dump()
                nextck += 1e13
    dump()
    print(f"{s.steps} steps, {trips} trips, {len(seen)} windows (last new at step {max(seen.values())}), "
          f"{len(transfers)} transfer levels, min sat {minmargin}, max unsaturated fraction {maxratio:.3f}, D reads 1 by k: "
          f"{dict(sorted(dk.items()))}, violations {viol if grammar is not None else 'n/a'}, {time.time() - t0:.0f} s")


if __name__ == "__main__":
    main()
