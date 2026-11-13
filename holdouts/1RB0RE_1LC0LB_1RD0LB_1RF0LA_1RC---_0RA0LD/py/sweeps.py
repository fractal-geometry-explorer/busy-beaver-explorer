"""Print the tape each time the head first reaches an end of the visited tape on a new visit (a "sweep end").

usage (from the repository root):
  python3 holdouts/MACHINE/py/sweeps.py STEPS SIDE [FROM] [MAXLINES] [MODE]

SIDE is L or R (the end).  MODE `raw` (default) prints the cells; `1` or `0` prints the lengths of the runs of that
symbol between single cells of the other one, run-length coded (`5*3` is three runs of length 5).  Plain Python, about
a million steps a second: fine up to 10^8 steps.
"""
import os
import sys

MACHINE = os.path.basename(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def parse(m):
    t = {}
    for s, part in enumerate(m.split("_")):
        for r in range(2):
            x = part[3 * r:3 * r + 3]
            t[(s, r)] = None if x[2] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65)
    return t


def comp(lens):
    out, i = [], 0
    while i < len(lens):
        j = i
        while j < len(lens) and lens[j] == lens[i]:
            j += 1
        out.append(str(lens[i]) if j - i == 1 else f"{lens[i]}*{j - i}")
        i = j
    return " ".join(out)


def main(argv):
    steps, side = int(argv[0]), argv[1]
    start = int(argv[2]) if len(argv) > 2 else 0
    maxlines = int(argv[3]) if len(argv) > 3 else 50
    mode = argv[4] if len(argv) > 4 else "raw"
    t = parse(MACHINE)
    tape = bytearray(1 << 22)
    p = lo = hi = len(tape) // 2
    st, k, last, n = 0, 0, None, 0
    while k < steps and n < maxlines:
        tr = t[(st, tape[p])]
        if tr is None:
            print("HALT", k + 1)
            return
        tape[p], p, st = tr[0], p + tr[1], tr[2]
        k += 1
        if p < lo or p > hi:
            s = "L" if p < lo else "R"
            lo, hi = min(lo, p), max(hi, p)
            if s != last:
                last = s
                if s == side and k >= start:
                    x = "".join("01"[c] for c in tape[lo:hi + 1])
                    if mode == "raw":
                        body = x
                    else:
                        other = "1" if mode == "0" else "0"
                        body = comp([len(y) for y in x.split(other)])
                    print(k, len(x), "ABCDEF"[st], body)
                    n += 1


if __name__ == "__main__":
    main(sys.argv[1:])
