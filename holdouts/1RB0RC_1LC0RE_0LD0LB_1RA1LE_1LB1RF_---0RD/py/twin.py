"""Compare the token runs of 1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD and of its twin
1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA frame by frame.

phi(L | R) = L | R with the last two tokens `1 0` of R replaced by `0`.  From the first frame after step START of this
machine, the twin is advanced until its frame is phi of this machine's frame; then both are advanced one frame at a
time and every pair of frames is compared (phi, and a constant difference of step counts).

usage (from the repository root):
  python3 holdouts/1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD/py/twin.py FRAMES [START]   (START default 22706700)
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tokens import table, MACHINES, raw_next, step, show  # noqa: E402

T3, T4 = table(MACHINES[False][0]), table(MACHINES[True][0])


def adv(T, S, L, R):
    nx = step(L, R)
    if nx is None:
        rn = raw_next(T, S, L, R)
        if rn[0] == "HALT":
            raise SystemExit("halt")
        nx = ("reset", rn[0], rn[1], rn[2])
    L, R = nx[1], nx[2]
    while L and L[0] == "0":
        L.pop(0)
    return nx[0], L, R, nx[3]


def phi(L, R):
    return (L, R[:-2] + ["0"]) if R[-2:] == ["1", "0"] else None


def main(n, start):
    L3, R3, s3 = [], ["0", "0"], 5
    L4, R4, s4 = [], [], 0
    while s3 < start:
        _, L3, R3, d = adv(T3, "D", L3, R3)
        s3 += d
    while s4 < start - 1000:
        _, L4, R4, d = adv(T4, "A", L4, R4)
        s4 += d
    for _ in range(400):
        if phi(L3, R3) == (L4, R4):
            break
        _, L4, R4, d = adv(T4, "A", L4, R4)
        s4 += d
    else:
        sys.exit("no matching twin frame found")
    off, resets = s3 - s4, 0
    print(f"matched: this machine at step {s3}, the twin at step {s4}: {show(L3, R3)}")
    for it in range(n):
        n3, L3, R3, d3 = adv(T3, "D", L3, R3)
        n4, L4, R4, d4 = adv(T4, "A", L4, R4)
        s3, s4 = s3 + d3, s4 + d4
        if n3 == "reset":
            resets += 1
            print(f"reset at frame {it}: step difference {off} -> {s3 - s4}")
            off = s3 - s4
        if phi(L3, R3) != (L4, R4) or s3 - s4 != off:
            sys.exit(f"break at frame {it}: {n3} {n4} {s3} {s4} {show(L3, R3)} / {show(L4, R4)}")
    print(f"{n} frames compared: the twin's frame is always phi of this machine's; step difference {off}")


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    main(int(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 22706700)
