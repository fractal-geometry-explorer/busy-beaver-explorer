"""Resets of 1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE.  Q(x, y) = 1^x (10)^y 11 with the head in B on the last cell.
From Q(x, y) with x in {0, 1} (an empty tank), run until the next Q(x', y') with x' in {0, 1} and print it.

usage: python3 zmap.py X Y0 Y1      (the resets from Q(X, y) for Y0 <= y < Y1)"""
import re
import sys

M = "1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE"
T = {}
for i, g in enumerate(M.split("_")):
    for r in (0, 1):
        t = g[3 * r:3 * r + 3]
        T[(i, r)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
RX = re.compile(r"(1*)((?:10)+)11")


def reset(x, y, maxs=10 ** 8):
    cells = [1] * x + [1, 0] * y + [1, 1]
    pad = 8 * len(cells) + 100
    tape = bytearray(pad) + bytearray(cells) + bytearray(pad)
    h, st, hi, n, last = pad + len(cells) - 1, 1, pad + len(cells) - 1, 0, 0
    while n < maxs:
        tr = T[(st, tape[h])]
        if tr is None:
            return "HALT", n + 1
        w, d, s = tr
        tape[h] = w
        h += d
        st = s
        n += 1
        hi = max(hi, h)
        if st == 1 and h == hi and n - last > 3:
            last = n
            seg = bytes(tape[:hi + 1]).lstrip(b"\x00").decode("latin1").translate({0: "0", 1: "1"})
            m = RX.fullmatch(seg)
            if m and len(m.group(1)) <= 1:
                return len(m.group(1)), len(m.group(2)) // 2
    return "TIMEOUT", maxs


if __name__ == "__main__":
    x, a, b = map(int, sys.argv[1:4])
    for y in range(a, b):
        print((x, y), "->", reset(x, y))
