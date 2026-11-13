"""The tape of 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB compressed into repeated words, each time the head reaches a new cell at an end.

usage: python3 py/shape.py STEPS [SIDES] [EVERY] [WIDTH]
    SIDES  L, R or LR (default L): which end
    EVERY  print every EVERY-th new cell at that end (default 1)
    WIDTH  cut each line after WIDTH characters (default 400)

A line is `step side length tape`; `(w)^k` is the word w repeated k times (greedy, periods up to 30, at least 3
copies), `[S]` the head in state S on the next cell.
"""
import sys

M = "1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB"


def table(text):
    t = []
    for g in text.split("_"):
        t.append([None if g[3 * y:3 * y + 3] == "---" else
                  (int(g[3 * y]), 1 if g[3 * y + 1] == "R" else -1, "ABCDEF".index(g[3 * y + 2])) for y in (0, 1)])
    return t


def rle(s, maxp=30, minrep=3):
    out, i, lit = [], 0, ""
    while i < len(s):
        best = None
        for p in range(1, maxp + 1):
            w = s[i:i + p]
            if len(w) < p or "[" in w:
                break
            r = 1
            while s[i + r * p:i + (r + 1) * p] == w:
                r += 1
            if r >= minrep and (best is None or r * p > best[0] * best[1] + p):
                best = (r, p, w)
        if best:
            if lit:
                out.append(lit)
                lit = ""
            out.append("(%s)^%d" % (best[2], best[0]))
            i += best[0] * best[1]
        else:
            lit += s[i]
            i += 1
    if lit:
        out.append(lit)
    return " ".join(out)


def main(T, sides, every, width):
    tab = table(M)
    N = 1 << 22
    tape = bytearray(N)
    h = lo = hi = N // 2
    s = t = 0
    count = {"L": 0, "R": 0}
    while t < T:
        tr = tab[s][tape[h]]
        if tr is None:
            print("HALT", t)
            return
        tape[h] = tr[0]
        h += tr[1]
        s = tr[2]
        t += 1
        side = "L" if h < lo else "R" if h > hi else None
        if side is None:
            continue
        lo, hi = min(lo, h), max(hi, h)
        if side not in sides:
            continue
        count[side] += 1
        if count[side] % every:
            continue
        cells = "".join(map(str, tape[lo:h])) + "[" + "ABCDEF"[s] + "]" + "".join(map(str, tape[h:hi + 1]))
        print(t, side, hi - lo + 1, rle(cells)[:width])


if __name__ == "__main__":
    a = sys.argv[1:]
    main(int(float(a[0])) if a else 10**6, a[1] if len(a) > 1 else "L", int(a[2]) if len(a) > 2 else 1,
         int(a[3]) if len(a) > 3 else 400)
