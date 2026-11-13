"""Length of the tape and number of defects in its alternating background, at turns of the head at the left end.

usage: python3 py/defects.py STEPS [EVERY]     prints  step  length  #(11)  #(00)  at every EVERY-th left-end turn

A defect is a pair of equal neighbouring cells (`11` or `00`) in the background `1010...`.
"""
import sys

M = "1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE"


def table(text):
    t = []
    for g in text.split("_"):
        t.append([None if g[3 * y:3 * y + 3] == "---" else (int(g[3 * y]), 1 if g[3 * y + 1] == "R" else -1, "ABCDEF".index(g[3 * y + 2])) for y in (0, 1)])
    return t


def main(T, K):
    tab = table(M)
    N = 1 << 20
    tape = bytearray(N)
    h = lo = hi = N // 2
    s = 0
    t = k = 0
    while t < T:
        tr = tab[s][tape[h]]
        if tr is None:
            print("HALT", t)
            return
        tape[h] = tr[0]
        h += tr[1]
        s = tr[2]
        t += 1
        if h > hi:
            hi = h
        if h < lo:
            lo = h
            k += 1
            if k % K == 0:
                c = tape[lo:hi + 1]
                d11 = sum(1 for i in range(len(c) - 1) if c[i] == c[i + 1] == 1)
                d00 = sum(1 for i in range(len(c) - 1) if c[i] == c[i + 1] == 0)
                print(t, len(c), d11, d00)


if __name__ == "__main__":
    main(int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**6, int(sys.argv[2]) if len(sys.argv) > 2 else 1)
