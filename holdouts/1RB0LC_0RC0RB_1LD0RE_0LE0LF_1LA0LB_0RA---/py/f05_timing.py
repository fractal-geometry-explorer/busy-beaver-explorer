"""Time the two rare events a halt of the F05 family needs, on a long run of fast.py.

At a left-end event the tape is  A> 0 (10)^6 1 (10)^t0 1 (10)^t1 1 ... (frame A), and the round to the next event
lowers block t_j by 18*5^j (fast.py: the SWEEP visit), so two numbers of each pair of neighbours stay fixed between
merges (`visit_conserves` in lean/Family.lean): the residue t_j mod 18 and the drift d_j = t_(j+1) - 5 t_j.  When
block j runs out, the next block has about the size of d_j.

The halt scans (`scan`, below, and data/f05_danger.json) found that, for the lists of the runs, a merge leads to a
halt within 12 left-end events exactly when the pair has
    (t_j mod 18, d_j)  in  H = {(6, -4), (10, -6), (14, -8), (0, -10), (0, -2), (0, 0)}
(tested for t_j < 40, d_j from -5 t_j to about +300, at several positions of several lists).  So a halt needs a
drift in [-10, 0]: block j+1 running out within one block-j step of block j, which is the "two rare events close
together".  This script runs the machine and, at every left-end event, looks at every drift that was not there at
the event before (merges and births make new ones; between merges they are conserved): how small they get, and
whether any lands in H.

usage: python3 f05_timing.py MACHINE STEPS [OUT.json]
"""
import json
import math
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import fast  # noqa: E402
import frames  # noqa: E402
import hybrid  # noqa: E402
import rle  # noqa: E402

H = {(6, -4), (10, -6), (14, -8), (0, -10), (0, -2), (0, 0), (16, -4), (4, -2)}
KEEP = 25
NEAR = 10 ** 4


def sci(x):
    """an integer as d.ddde+N (exact digits, no float overflow)"""
    s = str(abs(x))
    if len(s) <= 15:
        return str(x)
    return ("-" if x < 0 else "") + s[0] + "." + s[1:4] + "e+" + str(len(s) - 1)


class Timing:
    def __init__(self):
        self.prev = None          # drift multiset (as a dict d -> count) at the previous event
        self.events = 0
        self.new = 0
        self.small = []           # the KEEP smallest new |d| after event 30: (|d|, event, step, j, k, d, t_j mod 18)
        self.hits = []            # new pairs in H
        self.bins = {}            # number of new drifts with |d| < 10^e, after event 30
        self.rel = []             # smallest |d| / (18*5^(j+1)) after event 30
        self.last = None
        self.firsts = []          # (event, step, k, t0) when the first block changes by more than 18 (a merge at the top)
        self.near = []            # every new pair with |d| < NEAR (after event 30)

    def event(self, step, l):
        self.events += 1
        T = l[1:]
        cur = {}
        for j in range(len(T) - 1):
            d = T[j + 1] - 5 * T[j]
            cur[d] = cur.get(d, 0) + 1
            seen = self.prev.get(d, 0) if self.prev is not None else 0
            if seen:
                self.prev[d] = seen - 1
                continue
            self.new += 1
            key = (T[j] % 18, d)
            if key in H:
                self.hits.append({"event": self.events, "step": sci(step), "j": j, "k": len(T), "d": d,
                                  "t_mod_18": T[j] % 18})
            if self.events > 30:
                a = abs(d)
                e = len(str(a)) if a else 0
                self.bins[e] = self.bins.get(e, 0) + 1
                self.small.append((a, self.events, step, j, len(T), d, T[j] % 18))
                if a < NEAR:
                    self.near.append({"event": self.events, "step": sci(step), "j": j, "k": len(T), "d": d,
                                      "t_mod_18": T[j] % 18})
                self.small.sort()
                del self.small[KEEP:]
                r = a / (18 * 5 ** (j + 1))          # exact big-int true division
                self.rel.append((r, self.events, j, len(T), d))
                self.rel.sort()
                del self.rel[KEEP:]
        if self.last is not None and T and self.last[1] and abs(T[0] - self.last[1][0]) != 18:
            self.firsts.append({"event": self.events, "step": sci(step), "k": len(T),
                                "t0_before": sci(self.last[1][0]), "t0_after": sci(T[0])})
        self.prev = cur
        self.last = (step, T[:2], len(T))


def steps_arg(s):
    """'1e1000' as an exact integer (a float would be inf past 1e308)"""
    from decimal import Decimal
    return int(Decimal(s))


def run(machine, N, log=None):
    fr, fa, st = frames.info(machine)
    cls = fast.Fast2 if fast.f05_run.needs_raw(fa) else fast.Fast
    h = cls(fa)
    tm = Timing()
    sim = hybrid.FastRLE(fa)
    sim.q = ord(st) - 65
    h.sim = sim
    h.top = []
    t0 = time.time()

    def ev(s, l):
        if all(all(c == 0 for c in w) for w, n in s.left):
            tm.event(s.steps, l)
            if log and tm.events % 500 == 0:
                print(f"  event {tm.events} step 1e{len(str(s.steps)) - 1} k {len(l)} {time.time() - t0:.0f}s",
                      file=log, flush=True)
    try:
        r = h._run(sim, 0, stop_left=False, N=N, on_event=ev)
    except rle.Halt:
        r = "halt"
    return h, tm, r, time.time() - t0


def summary(machine, N, h, tm, r, secs):
    fmt = sci
    return {
        "machine": machine, "target_steps": sci(N), "steps_digits": len(str(h.sim.steps)),
        "halted": r == "halt", "seconds": round(secs), "left_end_events": tm.events,
        "blocks_at_end": tm.last[2] if tm.last else 0,
        "f_events": len(h.fev), "f_reads_one": sum(1 for f in h.fev if f[1] == 1),
        "new_drifts": tm.new,
        "danger_set": sorted([list(x) for x in H]),
        "danger_hits": tm.hits,
        "smallest_new_drifts_after_event_30": [
            {"abs": sci(a), "event": e, "step": fmt(s), "j": j, "k": k, "d": sci(d), "t_mod_18": m}
            for (a, e, s, j, k, d, m) in tm.small],
        "smallest_relative_after_event_30": [
            {"ratio": float("%.3g" % rr), "event": e, "j": j, "k": k, "d": sci(d)} for (rr, e, j, k, d) in tm.rel],
        "near_pairs": tm.near,
        "new_drifts_by_digits_after_event_30": {str(k): v for k, v in sorted(tm.bins.items())},
        "top_merges": tm.firsts[:60],
        "stats": h.stats,
    }


if __name__ == "__main__":
    m, N = sys.argv[1], steps_arg(sys.argv[2])
    h, tm, r, secs = run(m, N, log=sys.stderr)
    s = summary(m, N, h, tm, r, secs)
    out = sys.argv[3] if len(sys.argv) > 3 else None
    if out:
        with open(out, "w") as f:
            json.dump(s, f, indent=1)
            f.write("\n")
    print(m, "steps 1e%d" % (s["steps_digits"] - 1), "HALT" if s["halted"] else "no halt", "events", tm.events,
          "F", s["f_events"], "F reads 1:", s["f_reads_one"], "new drifts", tm.new, "hits", len(tm.hits),
          "min |d|", sci(tm.small[0][0]) if tm.small else None, f"{secs:.0f}s")
