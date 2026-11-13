"""The tape of 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF at each turn of the head at an end of the visited tape, read as words.

usage: python3 py/turns.py [STEPS] [L|R|LR] [FROM]

Each line: step, side, the tape run-length coded over the words q = 010110101101010110101101, s = 101010110110110, c = 110 (longest first; a cell no word matches is
printed as itself), the head as `S>` before the cell it reads.
"""
import sys

M = "1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF"
WORDS = [('q', '010110101101010110101101'), ('s', '101010110110110'), ('c', '110')]


def table(text):
    t = []
    for g in text.split("_"):
        row = []
        for y in (0, 1):
            s = g[3 * y:3 * y + 3]
            row.append(None if s == "---" else (int(s[0]), 1 if s[1] == "R" else -1, "ABCDEF".index(s[2])))
        t.append(row)
    return t


def tokens(cells):
    words = sorted(((n, tuple(int(c) for c in w)) for n, w in WORDS), key=lambda x: -len(x[1]))
    out, i = [], 0
    while i < len(cells):
        for n, w in words:
            if tuple(cells[i:i + len(w)]) == w:
                tok, i = n, i + len(w)
                break
        else:
            tok, i = str(cells[i]), i + 1
        if out and out[-1][0] == tok:
            out[-1][1] += 1
        else:
            out.append([tok, 1])
    return " ".join(t if c == 1 else f"{t}^{c}" for t, c in out)


def main(T, sides="LR", start=0):
    tab = table(M)
    N = 1 << 22
    tape = bytearray(N)
    h = lo = hi = N // 2
    st, t, d = 0, 0, 0
    while t < T:
        h0 = h
        tr = tab[st][tape[h]]
        t += 1
        if tr is None:
            print("HALT", t)
            return
        tape[h] = tr[0]
        h += tr[1]
        st = tr[2]
        lo, hi = min(lo, h), max(hi, h)
        nd = h - h0
        if d and nd != d and t >= start:
            side = "L" if h0 == lo else "R" if h0 == hi else None
            if side and side in sides:
                print(t, side, tokens(list(tape[lo:h])), "ABCDEF"[st] + ">", tokens(list(tape[h:hi + 1])))
        d = nd


if __name__ == "__main__":
    a = sys.argv[1:]
    main(int(float(a[0])) if a else 100000, a[1] if len(a) > 1 else "LR", int(float(a[2])) if len(a) > 2 else 0)
