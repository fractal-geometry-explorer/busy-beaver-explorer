"""The overflow events of 1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD (or of its twin) as digit strings.

At each time the head is at the left end of the tape in state D (state A for the twin
1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA) the tape is `S>0 0` followed by blocks of 1s of odd length separated by
single 0s.  This prints, for each such time, the step and the list of digits d (block 1^(2d+1)).  The first digit
is n of the left block 1^(2n+1); it goes up by one per overflow within an epoch and falls back to 0 at an epoch
restart.

usage (from the repository root):
  python3 holdouts/1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/py/digits.py STEPS [twin]
"""
import os
import re
import subprocess
import sys

REPO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))
M, S = "1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD", "D"
if len(sys.argv) > 2 and sys.argv[2] == "twin":
    M, S = "1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA", "A"


def tmrun():
    exe = "/tmp/tmrun_digits"
    if not os.path.exists(exe):
        subprocess.check_call(["gcc", "-O2", "-o", exe, os.path.join(REPO, "tools", "c", "tmrun.c")])
    return exe


def main(steps):
    out = subprocess.run([tmrun(), M, str(steps), "at", S, "L", "100000"], capture_output=True, text=True).stdout
    for line in out.splitlines():
        f = line.split(maxsplit=1)
        if not f[0].isdigit():
            print(line)
            continue
        cells = []
        for tok in f[1].split():
            m = re.match(r"^(?:[A-F]>)?([01])(?:\^(\d+))?$", tok)
            cells += [m.group(1)] * int(m.group(2) or 1)
        raw = "".join(cells)
        if not raw.startswith("00"):
            print(f[0], "unexpected tape", raw[:40])
            continue
        blocks = raw[2:].split("0")
        print(f[0], " ".join(str((len(b) - 1) // 2) if len(b) % 2 else f"?{len(b)}" for b in blocks))


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    main(int(sys.argv[1]))
