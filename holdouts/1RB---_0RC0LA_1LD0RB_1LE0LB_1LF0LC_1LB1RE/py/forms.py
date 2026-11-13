"""The dense and sparse forms of 1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE, checked along the run from blank tape.

usage: python3 py/forms.py [STEPS] [show]

At every left turn (B at the left end) the tape is a list of 1-blocks separated by single 0s; the blocks strictly
inside the list are counted by their length mod 4.  At every right turn the tape is a prefix followed by the words
0101 and 0001; the prefix lengths are counted.  With `show` the lists j (block 1^(4j+3), word (0101)^j 0001) are
printed at each turn.
"""
import re
import sys
from collections import Counter

M = "1RB---_0RC0LA_1LD0RB_1LE0LB_1LF0LC_1LB1RE"


def table(text):
    t = []
    for g in text.split("_"):
        row = []
        for y in (0, 1):
            s = g[3 * y:3 * y + 3]
            row.append(None if s == "---" else (int(s[0]), 1 if s[1] == "R" else -1, "ABCDEF".index(s[2])))
        t.append(row)
    return t


def main(T=5_000_000, show=False):
    tab = table(M)
    N = 1 << 22
    tape = bytearray(N)
    h = lo = hi = N // 2
    st, t, d, last = 0, 0, 0, None
    mod4, nL, nR, pre = Counter(), 0, 0, Counter()
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
        if d and nd != d:
            s = "".join(map(str, tape[lo:hi + 1]))
            if h0 - lo <= 1 and st == 1 and last != "L":
                bl = [len(b) for b in s.strip("0").split("0")]
                nL += 1
                for b in bl[2:-1]:
                    mod4[b % 4] += 1
                if show:
                    print(t, "L", [(b - 3) // 4 if b % 4 == 3 else f"*{b}" for b in bl])
                last = "L"
            elif hi - h0 <= 1 and last != "R":
                body = s.lstrip("0")
                m = re.fullmatch(r"(.*?)((?:0101|0001)*)(0*)", body)
                nR += 1
                pre[len(m.group(1))] += 1
                if show:
                    print(t, "R", m.group(1), [len(w) // 4 for w in re.findall(r"(?:0101)*0001", m.group(2))])
                last = "R"
        d = nd
    print(f"{T} steps: {nL} left turns, interior block lengths mod 4: {dict(sorted(mod4.items()))}")
    print(f"{nR} right turns, sparse prefix lengths: {dict(sorted(pre.items()))}")


if __name__ == "__main__":
    main(int(float(sys.argv[1])) if len(sys.argv) > 1 else 5_000_000, "show" in sys.argv)
