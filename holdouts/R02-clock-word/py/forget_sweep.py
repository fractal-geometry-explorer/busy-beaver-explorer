"""satctl_forget.py on the clock machines of R02, started at a visit of the left end late in the run (the word
right of the block forgotten, i.e. u): sizes n x n for n in SIZES.

The start is the configuration of the machine (its mirror for a right-end clock) at the first visit of the left end
after STEP steps: `X>0 0^v 1^L 0` then u.  The steps before it are a finite run (checked by simulation).

usage: python3 forget_sweep.py STEP SIZES MACHINE...      e.g. 1000 3,4,5,6
"""
import os
import subprocess
import sys
import clockx  # noqa: F401
from clockx import clock

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
step, sizes = int(sys.argv[1]), [int(x) for x in sys.argv[2].split(",")]
for m in sys.argv[3:]:
    h = clock.Hybrid(m)
    for t, L, W in h.visits(10 ** 9):
        if t != "HALT" and t >= step:
            break
    mm = clock.mirror(m) if m in clock.MIRROR else m
    pre = "0" + "0" * h.v + "1" * L + "0"
    for n in sizes:
        r = subprocess.run([sys.executable, os.path.join(ROOT, "tools/py/satctl_forget.py"), mm, str(n), str(n),
                            clock.PARAMS[m][0], pre], capture_output=True, text=True, timeout=3600)
        print(m, "t=%d L=%d" % (t, L), r.stdout.splitlines()[0] if r.stdout else r.stderr[-300:], flush=True)
        if "SAT" in r.stdout and "UNSAT" not in r.stdout:
            print(r.stdout)
            break
