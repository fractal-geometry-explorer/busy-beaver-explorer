"""The tape of 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF as a list of blocks of 1s, at every turn of the head.

usage: python3 blocks.py STEPS [FROM_STEP [MAX_LINES]]      e.g. python3 blocks.py 100000 4016 70

One line per turn: the step, L or R (the direction the head was moving) with the head's distance from the left end,
the lengths of the blocks of 1s left of the head, the head (state and the bit it reads), the blocks right of it.
A `z` stands for one extra 0 between two blocks (blocks are normally separated by a single 0).
"""
import re
import sys

M = "1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF"


def table(m):
    t = {}
    for s, row in enumerate(m.split("_")):
        for b in range(2):
            x = row[3 * b:3 * b + 3]
            t[(s, b)] = None if x[0] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, "ABCDEF".index(x[2]))
    return t


def runs(row):
    out = []
    for g in re.finditer(r"1+|0+", row):
        w = g.group()
        if w[0] == "1":
            out.append(str(len(w)))
        elif len(w) > 1:
            out.append("z" * (len(w) - 1))
    return " ".join(out)


def main():
    steps = int(sys.argv[1])
    start = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    limit = int(sys.argv[3]) if len(sys.argv) > 3 else 100
    t = table(M)
    tape, pos, s, lo, hi, last, shown = {}, 0, 0, 0, 0, 1, 0
    for i in range(steps):
        b = tape.get(pos, 0)
        tr = t[(s, b)]
        if tr is None:
            print("HALT", i)
            return
        if tr[1] != last:
            if i >= start:
                left = "".join(str(tape.get(j, 0)) for j in range(lo, pos))
                right = "".join(str(tape.get(j, 0)) for j in range(pos + 1, hi + 1))
                print(f"{i:9d} {'L' if last == -1 else 'R'}@{pos - lo:<5d} {runs(left)} [{'ABCDEF'[s]}{b}] {runs(right)}")
                shown += 1
                if shown >= limit:
                    return
            last = tr[1]
        tape[pos] = tr[0]
        pos += tr[1]
        s = tr[2]
        lo, hi = min(lo, pos), max(hi, pos)


if __name__ == "__main__":
    main()
