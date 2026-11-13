"""The tape in block notation at the start of each rightward sweep from the left end.

usage (from the repo root):  python3 holdouts/MACHINE/py/particles.py STEPS [EVERY] [WIDTH]

Cut the tape into blocks 1^k 0 and write each block as its k; a run of n background blocks 1110 is written `(n)`
(`.` for one).  `^` is the head: in the rightward state, on the second cell of the leftmost block (the left gadget,
4 when idle).  Prints every EVERY-th sweep start (default 1) in the first STEPS steps, cut to WIDTH characters.
Particles: 1 and 5 are walls, 2 a runner, 0 = runner + 1-wall, 4 = runner + 5-wall (see py/cycles.py).
The twin 1RB1RF_0RC0LE_1RD0RF_1LB---_1LB1LE_1RA0LC is handled too (its rightward state is A).
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
M = os.path.basename(os.path.dirname(HERE))


def parse(m):
    t = {}
    for s, part in enumerate(m.split("_")):
        for r in range(2):
            x = part[3 * r:3 * r + 3]
            t[(s, r)] = None if x[2] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65)
    return t


def blocks(cells):
    out, run, k = [], 0, 0
    for c in cells:
        if c:
            k += 1
            continue
        if k == 3:
            run += 1
        else:
            if run:
                out.append("." if run == 1 else "(%d)" % run)
                run = 0
            out.append(str(k) if k < 10 else "[%d]" % k)
        k = 0
    if run:
        out.append("." if run == 1 else "(%d)" % run)
    return "".join(out)


def main(argv):
    steps = int(argv[0])
    every = int(argv[1]) if len(argv) > 1 else 1
    width = int(argv[2]) if len(argv) > 2 else 150
    T = parse(M)
    right = "ABCDEF".index("A" if M.startswith("1RB1RF") else "F")
    N = 1 << 20
    t = bytearray(N)
    p = N // 2
    lo = hi = p
    st, ev = 0, 0
    for k in range(steps):
        x = t[p]
        if st == right and p - lo <= 8 and t[p - 1] == 1 and not any(t[lo - 1:p - 1]):
            if ev % every == 0:
                hi1 = max(i for i in range(p, hi + 2) if t[i]) if any(t[p:hi + 2]) else p
                print(("%10d  ^%s" % (k, blocks(t[p - 1:hi1 + 2])))[:width + 12])
            ev += 1
        tr = T[(st, x)]
        if tr is None:
            print("HALT", k)
            return
        t[p] = tr[0]
        p += tr[1]
        st = tr[2]
        lo, hi = min(lo, p), max(hi, p)


if __name__ == "__main__":
    main(sys.argv[1:])
