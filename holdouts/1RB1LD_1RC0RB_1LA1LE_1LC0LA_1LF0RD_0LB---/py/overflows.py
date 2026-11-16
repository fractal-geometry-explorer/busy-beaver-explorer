"""The overflows of 1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LB---: the times A is at the left end of the tape with the tape
`A>0 1^n 0 ...`, their gaps D and the corrections D(next) - 4 D, and the tape after the left block.

usage (from the repository root):
  python3 holdouts/1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LB---/py/overflows.py STEPS
"""
import os
import subprocess
import sys

REPO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))
M, STATE, HEAD, FACTOR = "1RB1LD_1RC0RB_1LA1LE_1LC0LA_1LF0RD_0LB---", "A", "A>0 1^", 4


def main(steps):
    exe = "/tmp/tmrun_overflows"
    if not os.path.exists(exe):
        subprocess.check_call(["gcc", "-O2", "-o", exe, os.path.join(REPO, "tools", "c", "tmrun.c")])
    out = subprocess.run([exe, M, str(steps), "at", STATE, "L", "1000000"], capture_output=True, text=True).stdout
    ev = []
    for line in out.splitlines():
        f = line.split(maxsplit=1)
        if f[0].isdigit() and len(f) > 1 and f[1].startswith(HEAD):
            ev.append((int(f[0]), f[1]))
    prev = None
    for i, (t, tape) in enumerate(ev):
        d = t - ev[i - 1][0] if i else None
        corr = d - FACTOR * prev if (d is not None and prev is not None) else None
        print(t, "" if corr is None else f"{corr:+d}", tape[:160])
        prev = d


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    main(int(sys.argv[1]))
