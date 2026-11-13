"""The phases of 1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD from blank tape.

usage: python3 holdouts/1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/py/phases.py [STEPS]   (default 12,000,000)

Every time the head is at the left end of the visited tape in state F it reads the tape. The main regime is
`F>0^6 (1000)^a 1 0 1 1 1 (0001)^b TAIL` (`P a b` in lean/Phase.lean when TAIL is the first of its three shapes);
this prints a line each time a phase starts (a = 3) and, with -v, every sample of the main regime.
"""
import re
import sys

M = "1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD"
MAIN = re.compile(r"^000000((?:1000)*)10111((?:0001)*)(.*)$")
TAILS = {"0100010100001": 1, "0101101000010": 2, "0111011": 3}


def rle(cells):
    """`0 1 (1000)^859 0 1` style: runs of the words 1000 and 0001 of length 3 or more collapsed."""
    out = re.sub(r"((?:1000){3,}|(?:0001){3,})", lambda g: f" ({g.group(1)[:4]})^{len(g.group(1)) // 4} ", cells)
    return " ".join(out.split())


def table(m):
    t = []
    for g in m.split("_"):
        row = []
        for b in (0, 1):
            x = g[3 * b:3 * b + 3]
            row.append(None if x[2] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, "ABCDEF".index(x[2])))
        t.append(row)
    return t


def run(steps, verbose=False):
    t = table(M)
    size = 1 << 16
    tape = bytearray(size)
    h = lo = hi = size // 2
    s = 0
    for k in range(1, steps + 1):
        tr = t[s][tape[h]]
        if tr is None:
            print("HALT", k)
            return
        w, d, s = tr
        tape[h] = w
        h += d
        if h < lo:
            lo = h
        elif h > hi:
            hi = h
        if h == lo and s == 5:
            cells = tape[lo:hi + 1].decode("latin1").translate({0: "0", 1: "1"}).rstrip("0")
            mm = MAIN.match(cells)
            if mm:
                a, b = len(mm.group(1)) // 4, len(mm.group(2)) // 4
                tail = TAILS.get(mm.group(3), rle(mm.group(3)))
                if a == 3 or verbose:
                    print(f"step {k:>12,}  a={a:<6} b={b:<6} tail={tail}")
        if h < 8 or h > size - 8:
            raise SystemExit("tape too small")


if __name__ == "__main__":
    args = [x for x in sys.argv[1:] if x != "-v"]
    run(int(float(args[0])) if args else 12_000_000, "-v" in sys.argv)
