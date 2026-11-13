"""Epochs of 1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF (the machine T of the 3-cell-block family).

The head reaches the left end of the tape only in state F, over a run 1^n that covers the whole left part; then the
run is reset (`D` erases it, leaving 1^3 0^(n-1) 1^2) and the left binary counter starts again.  This script reads
the output of `tmrun T STEPS at F L K` (the configurations at those moments) and prints, for each epoch, the length
n of the run, the steps it took, and the steps per count, (steps) / 2^k for n = 3k + 1.

usage: ./tmrun 1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF 100000000000 at F L 100000 > fl.txt
       python3 holdouts/1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF/py/epochs.py fl.txt
"""
import sys


def main(path):
    rows = []
    for line in open(path):
        p = line.split()
        if len(p) < 3 or not p[0].isdigit() or p[1] != "F>0":
            continue
        run = p[2]
        n = int(run.split("^")[1]) if "^" in run else 1
        rows.append((int(p[0]), n, " ".join(p[3:])))
    print(f"{'step':>13} {'n':>4} {'epoch steps':>13} {'per count':>12}  rest of the tape")
    prev = None
    for t, n, rest in rows:
        if prev is None:
            print(f"{t:13d} {n:4d}")
        else:
            d = t - prev[0]
            per = f"{d / 2 ** ((prev[1] - 1) // 3):12.3f}" if prev[1] % 3 == 1 else " " * 12
            print(f"{t:13d} {n:4d} {d:13d} {per}  {rest[:150]}")
        prev = (t, n)


if __name__ == "__main__":
    main(sys.argv[1])
