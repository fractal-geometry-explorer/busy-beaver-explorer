"""One whole round trip of 1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA from a real configuration, with the length of
the body as a variable (symbolic run, `tools/py/bbtools/symtm.py`; trusted computation, not a Lean proof).

usage: gcc -O3 -o /tmp/zonemodel c/zonemodel.c && DUMP=3000 /tmp/zonemodel 0 3000 100000000 > /tmp/r.txt
       python3 py/trip_check.py /tmp/r.txt

The dump is the tape at a right record (the head on the new cell, state B).  The program keeps the zone as it is,
writes the body of period-10 words as  lead (w)^(n+k) tail  with n a variable, and runs symbolically to the next
right record.  It prints the step count (a linear expression in n), the crossing rules the run used and the zone
next to the body at the end.  The run never looks at a particular n: one trip acts on the zone in the same way for
every body length that is at least the one used (k - 5 words fewer than the real one, as written).
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.machine import Machine  # noqa: E402
from bbtools.symtm import Blank, Config, Rep, run  # noqa: E402

M = "1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA"
TAIL = "011011011"


def main():
    _, st, s = open(sys.argv[1]).read().split()
    assert st == "B"
    j = len(s) - 1
    while j - 10 >= 0 and s[j] == s[j - 10]:
        j -= 1
    zone, body = s[:j + 1], s[j + 1:]
    assert body.endswith(TAIL), "the body does not end as expected"
    b = body[:len(body) - len(TAIL)]
    lead = len(b) % 10
    w, k = b[lead:lead + 10], (len(b) - lead) // 10
    print(f"zone {len(zone)} cells, body {len(body)} cells = {lead} + {k} words {w} + {TAIL}")
    parts = ["0^inf"] + list(zone) + list(b[:lead]) + [f"({w})^n+{k - 5}"] + list(TAIL) + ["B>", "0^inf"]
    c = Config.parse(" ".join(parts))
    trace = []
    f = run(Machine.parse(M), c, lambda c: c.steps.k > 0 and len(c.right) == 1 and isinstance(c.right[0], Blank),
            max_moves=5_000_000, trace=trace)
    print("steps to the next right record:", f.steps)
    for ev in trace:
        if ev[0] == "cross":
            print("  crossing:", ev[3])
    reps = [t for t in f.left if isinstance(t, Rep)]
    print("body at the next right record:", reps)


if __name__ == "__main__":
    main()
