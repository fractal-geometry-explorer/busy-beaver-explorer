"""Print the tape of 1RB1LF_1LC0RD_0LD0LC_1RE0LA_0RA0RC_0RE--- at each round end, with the exact accelerated
simulator of accel.py (blocks of 4 cells).

A round ends when the head reaches the right end of the tape; the tape is then written with a = 10 only, as
    a^x1 1 a^x2 1 ... a^xk 1 a^L <end>
and this prints `step state x1 1 x2 1 ... xk 1 L ... | end`: the lengths of the runs of 10s and the single cells
between them (the last cells depend on the state the head is in: the round end is seen at slightly different
moments).  Between two round ends the block j places left of the
fixed last block loses 18*5^(j-1) a's, as long as it can pay.

usage: python3 rounds.py STEPS SECONDS
"""
import os
import re
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from accel import Accel  # noqa: E402

M = "1RB1LF_1LC0RD_0LD0LC_1RE0LA_0RA0RC_0RE---"


def main(argv):
    N, tl = float(argv[0]), float(argv[1])
    A = Accel(M, 4, bounce="A")
    r, t0, last = A.r, time.time(), -1
    while r.steps < N and time.time() - t0 < tl:
        if not A.step():
            print("HALT", r.steps)
            return
        if r.dir == -1 and len(r.right) <= 2 and r.steps > last + 100:
            last = r.steps
            lw, rw = r.runs()
            s = "".join(w * c for w, c in lw).lstrip("0")
            rs = "".join(w * c for w, c in rw).rstrip("0")
            toks = re.findall(r"(?:10)+|.", s)
            out = [str(len(x) // 2) if len(x) > 1 else x for x in toks]
            print(r.steps, "ABCDEF"[r.state], " ".join(out),
                  "|", rs, flush=True)
    print(f"# stopped at {r.steps:.3e} steps")


if __name__ == "__main__":
    main(sys.argv[1:])
