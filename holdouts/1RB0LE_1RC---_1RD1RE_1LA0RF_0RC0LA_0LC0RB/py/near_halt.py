"""Where 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB comes closest to halting, along the run from blank tape.

usage: python3 py/near_halt.py [STEPS] [K]

For the halting state and every state with a transition into it, the K cells on each side of the head each time the
machine is in that state, most frequent first (`[x]` is the cell under the head).
"""
import sys
from collections import Counter

M = "1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB"


def table(text):
    t = []
    for g in text.split("_"):
        row = []
        for y in (0, 1):
            s = g[3 * y:3 * y + 3]
            row.append(None if s == "---" else (int(s[0]), 1 if s[1] == "R" else -1, "ABCDEF".index(s[2])))
        t.append(row)
    return t


def main(T, K):
    tab = table(M)
    hs = {s for s in range(6) for y in (0, 1) if tab[s][y] is None}
    pre = {s for s in range(6) for y in (0, 1) if tab[s][y] and tab[s][y][2] in hs}
    watch = hs | pre
    N = 1 << 22
    tape = bytearray(N)
    h = N // 2
    st, t = 0, 0
    win = Counter()
    while t < T:
        if st in watch:
            w = "".join(map(str, tape[h - K:h])) + "[" + str(tape[h]) + "]" + "".join(map(str, tape[h + 1:h + 1 + K]))
            win["ABCDEF"[st], w] += 1
        tr = tab[st][tape[h]]
        t += 1
        if tr is None:
            print("HALT", t)
            return
        tape[h] = tr[0]
        h += tr[1]
        st = tr[2]
    for s in sorted(watch):
        rows = sorted(((w, n) for (q, w), n in win.items() if q == "ABCDEF"[s]), key=lambda x: -x[1])
        print("ABCDEF"[s], sum(n for _, n in rows), "visits;", ", ".join(f"{w} {n}" for w, n in rows[:12]))


if __name__ == "__main__":
    a = sys.argv[1:]
    main(int(float(a[0])) if a else 1_000_000, int(a[1]) if len(a) > 1 else 3)
