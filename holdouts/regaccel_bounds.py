#!/usr/bin/env python3
"""Write the no-halt bounds of the region-memo accelerator (tools/py/bbtools/regaccel.py) into the holdouts' ledgers.

`holdouts/regaccel.json` holds one record per machine: block size K, orientation ("fwd", or "mir" when the run is
of the mirrored table, so that the counter sits at the left end), wall-clock seconds, the number of decimal digits
of the last step count reached and its leading digits, and the snapshot check (how many configurations of the
accelerated run, up to `snap_steps` steps, were compared cell for cell with a direct run, and how many differed).

    python3 holdouts/regaccel_bounds.py            # add or replace the claim in every status.json listed
    python3 holdouts/build_pages.py M ...          # then rebuild those pages

Only machines whose bound beats every earlier trusted bound of theirs are written.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TAG = "(region-memo accelerator)"


def old_best(claims):
    best = 0
    for c in claims:
        t = c.get("title", "")
        if TAG in t or "no halt" not in t.lower():
            continue
        for e in re.findall(r"10<sup>(\d+)</sup>", t):
            best = max(best, int(e))
    return best


def sci(n):
    n = int(n)
    e = len(str(n)) - 1
    m = n / 10 ** e
    return ("%g&times;10<sup>%d</sup>" % (m, e)) if m != 1 else "10<sup>%d</sup>" % e


def claim(m, r):
    e = r["digits"] - 1
    lead = r["lead"]
    mant = "%s.%s" % (lead[0], lead[1:3])
    orient = ("the mirrored table (so that the counter is at the left end), " if r["orient"] == "mir" else "")
    return {
        "level": "trusted",
        "title": "No halt in the first %s&times;10<sup>%d</sup> steps %s" % (mant, e, TAG),
        "text": ("The region-memo accelerator <code>tools/py/bbtools/regaccel.py</code> ran %swith blocks of %d cells, from "
                 "blank tape for %d seconds and reached step %s&times;10<sup>%d</sup> without a halt. It keeps the tape "
                 "run-length coded and, for each stretch of tape from the left end, a macro (the run until the head first "
                 "leaves that stretch) computed by a symbolic run of the machine with the long runs as variables; a macro "
                 "is used only when the linear inequalities its symbolic run assumed hold, otherwise the stretch is run "
                 "again by the same recursion. So the run is exact, step count included. Check: %d configurations of "
                 "this run (every time the head faced blank tape on the right, up to %s steps) agree cell for cell with "
                 "a direct run (<code>tools/py/regcheck.py</code>). This is a bounded run and says nothing about later "
                 "steps.") % (orient, r["K"], r["seconds"], mant, e, r["snapshots"], sci(r["snap_steps"])),
        "where": "<code>python3 tools/py/bbtools/regaccel.py %s %d %d%s</code>; <code>holdouts/regaccel.json</code>" % (
            m, r["K"], r["seconds"], " mirror" if r["orient"] == "mir" else ""),
    }


def main():
    data = json.load(open(os.path.join(HERE, "regaccel.json")))
    done = []
    for m, r in sorted(data.items()):
        if r.get("result") != "running" or r.get("snap_bad", 1) != 0 or r.get("skip"):
            continue
        p = os.path.join(HERE, m, "status.json")
        s = json.load(open(p))
        claims = [c for c in s["claims"] if TAG not in c.get("title", "")]
        if r["digits"] - 1 <= old_best(claims):
            continue
        idx = max([i for i, c in enumerate(claims) if c.get("level") == "trusted" and c.get("title") != "Related holdouts"] or [len(claims) - 1]) + 1
        claims.insert(idx, claim(m, r))
        s["claims"] = claims
        with open(p, "w") as f:
            json.dump(s, f, indent=1, ensure_ascii=False)
            f.write("\n")
        done.append(m)
    print(" ".join(done))


if __name__ == "__main__":
    sys.exit(main())
