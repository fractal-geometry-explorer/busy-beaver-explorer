"""The blocks and separators of 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---, at each turn of the head at the right end.

usage: python3 py/blocks.py [STEPS]

At every turn at the right end the tape is checked to be (10)^n1 s1 (10)^n2 s2 ... (10)^N A>1 1 with separators
s in {0, 1}; the blocks and separators are printed.
"""
import re
import sys

M = "1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---"


def table(text):
    t = []
    for g in text.split("_"):
        row = []
        for y in (0, 1):
            s = g[3 * y:3 * y + 3]
            row.append(None if s == "---" else (int(s[0]), 1 if s[1] == "R" else -1, "ABCDEF".index(s[2])))
        t.append(row)
    return t


def main(T):
    tab = table(M)
    N = 1 << 20
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
        if d == 1 and nd == -1 and h0 == hi:
            s = "".join(map(str, tape[lo:hi + 1])).lstrip("0")
            assert st == 0 and s.endswith("11"), s   # A> 1 1 at the right end
            parts = re.findall(r"((?:10)+)([01]?)", s[:-2])
            assert "".join(p + q for p, q in parts) == s[:-2] and not parts[-1][1], s
            print(t, " ".join(f"(10)^{len(p) // 2}" + (f" {q}" if q else "") for p, q in parts), "A> 1 1")
        d = nd


if __name__ == "__main__":
    main(int(float(sys.argv[1])) if len(sys.argv) > 1 else 40000)
