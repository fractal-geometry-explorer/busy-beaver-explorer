"""The rounds of 1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA---: run the proved-cycle accelerator of the shared tools
(blocks of 5 cells) and group its jumps into rounds (a new round starts when a jump is longer than the one before).
Each jump is one block of b = 10000 turned, one b per cycle, into a = 11010.

usage: python3 rounds.py [STEPS]     (default 1e11, about a minute)
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.cycles import Accelerator  # noqa: E402
from bbtools.macro import MacroRun  # noqa: E402

M = "1RB0RA_0RC0LB_1LD1RF_1LE1RA_1RD1RB_1LA---"


def rounds(steps):
    acc = Accelerator(MacroRun(M, 5))
    acc.run(steps)
    out, cur, prev = [], [], None
    for before, n, after, name in acc.jumps:
        if prev is not None and n > prev:
            out.append(cur)
            cur = []
        cur.append((before, n))
        prev = n
    out.append(cur)
    return out, acc.run_


def main():
    steps = float(sys.argv[1]) if len(sys.argv) > 1 else 1e11
    rs, run = rounds(steps)
    for r in rs:
        print(f"{r[0][0]:.3e}  total {sum(n for _, n in r):7d}  blocks {[n for _, n in r]}")
    print(("halted after" if run.halted else "no halt in"), run.steps, "steps")


if __name__ == "__main__":
    main()
