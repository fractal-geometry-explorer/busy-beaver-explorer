"""Sort machines by the shape of their run from blank tape, from the JSON lines of tools/c/triage.c.

usage: python3 -m bbtools.triage DIR_OF_JSON > table.json       one record per machine, with a class and features

The features are heuristics, read off one bounded run; they say what a machine looks like, not what it does:

  alpha_l, alpha_r   growth exponents of the cells visited on each side: d log(extent) / d log(steps), fitted over
                     the last six doublings of the step count (0.5: the head sweeps back and forth over a tape that
                     grows like a square root, as a bouncer does; near 0: each new cell costs a constant factor more
                     time, as for a counter or a Collatz-like map; 1: linear drift)
  ratio_l, ratio_r   median ratio of the times of successive new-cell records on a side, over the last records
                     (well above 1 for exponential growth)
  density            1s per visited cell at the end
  stuck_l, stuck_r   the side has not grown in the last half of the run

The class is the pair of side shapes, each one of exp (alpha < 0.12 or ratio > 1.3), sqrt (0.35 to 0.65),
power (other exponents below 0.85), linear (0.85 and up) and fixed (no growth late in the run).
"""
import json
import math
import os
import sys


def alpha(cp, idx, last=6):
    pts = [(math.log(c[0]), math.log(c[idx] + 1)) for c in cp if c[0] >= 1024]
    pts = pts[-last:]
    if len(pts) < 3:
        return None
    n = len(pts)
    mx = sum(p[0] for p in pts) / n
    my = sum(p[1] for p in pts) / n
    sxx = sum((p[0] - mx) ** 2 for p in pts)
    sxy = sum((p[0] - mx) * (p[1] - my) for p in pts)
    return sxy / sxx if sxx else None


def ratio(times):
    """Median ratio of successive record times; records in bursts (consecutive steps) count once."""
    t = []
    for x in times:
        if t and x - t[-1] <= 2 * max(1, len(t)):   # a burst: the head walks into new cells
            t[-1] = x
        else:
            t.append(x)
    r = sorted(b / a for a, b in zip(t, t[1:]) if a > 0)
    return r[len(r) // 2] if r else None


def side_shape(a, rt, stuck):
    if stuck:
        return "fixed"
    if a is None:
        return "?"
    if a < 0.12 or (rt is not None and rt > 1.3 and a < 0.35):
        return "exp"
    if 0.35 <= a <= 0.65:
        return "sqrt"
    if a < 0.85:
        return "power"
    return "linear"


def features(d):
    cp = d["cp"]
    last = cp[-1]
    half = [c for c in cp if c[0] <= d["steps"] // 2]
    h = half[-1] if half else cp[0]
    stuck_l = d["left_n"] > 0 and d["left"][-1] <= d["steps"] // 2 if d["left_n"] else True
    stuck_r = d["right_n"] > 0 and d["right"][-1] <= d["steps"] // 2 if d["right_n"] else True
    al, ar = alpha(cp, 1), alpha(cp, 2)
    rl, rr = ratio(d["left"]), ratio(d["right"])
    f = {
        "machine": d["machine"],
        "steps": d["steps"],
        "halted": d["halted"],
        "left": last[1], "right": last[2], "width": d["width"], "ones": d["ones"],
        "density": round(d["ones"] / max(1, d["width"]), 3),
        "alpha_l": None if al is None else round(al, 3),
        "alpha_r": None if ar is None else round(ar, 3),
        "ratio_l": None if rl is None else round(rl, 3),
        "ratio_r": None if rr is None else round(rr, 3),
        "stuck_l": stuck_l, "stuck_r": stuck_r,
        "half_width": h[1] + h[2] + 1,
        "final": d["final"],
        "snap_left": d["snap_left"], "snap_right": d["snap_right"],
    }
    sl = side_shape(al, rl, stuck_l)
    sr = side_shape(ar, rr, stuck_r)
    f["shape_l"], f["shape_r"] = sl, sr
    f["class"] = "halted" if d["halted"] else "/".join(sorted([sl, sr]))
    return f


def load(path):
    out = []
    for name in sorted(os.listdir(path)):
        if not name.endswith(".json"):
            continue
        with open(os.path.join(path, name)) as fh:
            line = fh.read().strip()
        if line:
            out.append(features(json.loads(line)))
    return out


if __name__ == "__main__":
    rows = load(sys.argv[1])
    json.dump(rows, sys.stdout, indent=0)
    sys.stdout.write("\n")
