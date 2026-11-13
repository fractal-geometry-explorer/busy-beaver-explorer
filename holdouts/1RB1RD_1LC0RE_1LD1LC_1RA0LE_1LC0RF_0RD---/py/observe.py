"""Print this machine's tape at sample points, with repeated words compressed: (001)^5 is 001 five times.

usage: python3 holdouts/MACHINE/py/observe.py [STEPS] [SIDE] [K]
  the tape at the last K moments (default 6) the head extended the visited part on SIDE (L, R or B for both) within
  STEPS steps (default 10^7), each line 'step tape'. A direct simulation; slow beyond ~10^8 steps (use tools/c).
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.machine import Machine  # noqa: E402

M = "1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---"
REP = re.compile(r"([01]{1,12}?)\1{2,}|([01]{4,12}?)\2")


def compress(s):
    def sub(mt):
        w = mt.group(1) or mt.group(2)
        k = len(mt.group(0)) // len(w)
        return " " + (w if len(w) == 1 else "(" + w + ")") + "^" + str(k) + " "
    return " ".join(REP.sub(sub, s).split())


def main(argv):
    n = int(float(argv[0])) if argv else 10 ** 7
    side = argv[1] if len(argv) > 1 else "B"
    k = int(argv[2]) if len(argv) > 2 else 6
    m = Machine.parse(M)
    tape, pos, st, lo, hi, snaps = {}, 0, 0, 0, 0, []
    for t in range(1, n + 1):
        tr = m.table[st][tape.get(pos, 0)]
        if tr is None:
            print("halted at step", t)
            return
        w, d, st = tr
        tape[pos] = w
        pos += d
        if (pos < lo and side in "LB") or (pos > hi and side in "RB"):
            snaps.append((t, dict(tape), pos, st))
            snaps = snaps[-k:]
        lo, hi = min(lo, pos), max(hi, pos)
    for t, tp, p, s in snaps:
        a, b = min(min(tp), p), max(max(tp), p)
        left = "".join(str(tp.get(i, 0)) for i in range(a, p))
        right = "".join(str(tp.get(i, 0)) for i in range(p, b + 1))
        print(t, compress(left), "ABCDEF"[s] + ">", compress(right))


if __name__ == "__main__":
    main(sys.argv[1:])
