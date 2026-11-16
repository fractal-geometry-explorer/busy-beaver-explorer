"""The two-counter round law of 1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---, checked at its left-end visits in state F.

Words: a = 1100, b = 110, c = 10 (read longest first).  At each moment the head is in F on the leftmost visited cell,
the tape right of it reads (in the run from blank tape, every such moment from step 1,756 to 10^10 that matches)

    F>0  c^s  H  X_1 bb X_2 bb ... bb X_w  b^m  c c 0  b^j

* c^s is the *left counter* with all digits 0: its digits are four cells, `1 0 1 0` = 0 and `1 0 0 0` = 1, least
  significant on the right (lean/Counter.lean proves its increment and overflow rules for any length);
* H is a short header, `ab` (most of the time), `ababcc` or `abccbcc`;
* X_1 .. X_w are the digits of the *right counter*, X = a for 1 and X = cc for 0, X_1 the least significant; v is its
  value;
* b^m and b^j are two runs of b, separated by the marker `c c 0`.

In a round (from one such visit to the next) the left counter counts through all its 2^(s/2) values, and between two
of its increments the head goes right once and decrements the right counter; each time the right counter passes
from 0 to 2^w - 1 (a borrow) one b moves from the first run to the second.  So, with D = 2^(s/2) and
t = the number of borrows of D decrements from v (t = (D - v - 1) div 2^w + 1 if D > v, else 0):

    regular round (m >= t, and m > t when H is not `ab`):
                             (s, H, X, m, j)  ->  (s + 2, H, X - D mod 2^w, m - t, j + t)

Within a phase t doubles from round to round, which is the doubling map (m, j) -> (m - j - k, 2 j + k) of the
README (k = t - j).  When m < t the round is a *phase change*: H, w, s and the runs change in a way not yet
understood (the phase changes are printed at the end).  From H = `ab` a phase change gives s - 4 and mostly a
header `ababcc` or `abccbcc`; from those headers it gives s + 2, header `ab`, one more digit (w + 1) and m + j + 1.
The first visit (step 636) is before the law starts.

usage: tmrun MACHINE 10000000000 at F L 5000 > fl.txt   (tools/c/tmrun.c, about a minute)
       python3 py/round_law.py fl.txt
"""
import re
import sys

WORDS = [("a", "1100"), ("b", "110"), ("c", "10")]
FORM = re.compile(r"(c*)(ab|ababcc|abccbcc)((?:(?:a|cc)bb)*(?:a|cc))(b*)cc0(b*)")


def tokenize(s):
    out, i = [], 0
    while i < len(s):
        for name, w in WORDS:
            if s.startswith(w, i):
                out.append(name); i += len(w); break
        else:
            out.append(s[i]); i += 1
    return "".join(out)


def cells_right_of_head(toks):
    cells, head = [], None
    for tk in toks:
        if ">" in tk:
            head = len(cells); cells.append(tk[-1]); continue
        a, _, e = tk.partition("^")
        cells += [a] * (int(e) if e else 1)
    return "".join(cells[head + 1:])


def parse(line):
    p = line.split()
    if not p or p[0] in ("running", "halted"):
        return None
    t = tokenize(cells_right_of_head(p[1:]))
    m = FORM.fullmatch(t)
    if not m:
        return int(p[0]), None, t
    X = m.group(3).split("bb")
    v = sum(1 << i for i, x in enumerate(X) if x == "a")
    return int(p[0]), (len(m.group(1)), m.group(2), v, len(X), len(m.group(4)), len(m.group(5))), t


def borrows(s, v, w):
    D = 1 << (s // 2)
    return (D - v - 1) // (1 << w) + 1 if D > v else 0


def regular(c):
    s, H, v, w, m, j = c
    t = borrows(s, v, w)
    if m < t or (H != "ab" and m == t):
        return None
    return (s + 2, H, (v - (1 << (s // 2))) % (1 << w), w, m - t, j + t)


def bits(v, w):
    return "".join("1" if (v >> i) & 1 else "0" for i in range(w))


def main(path):
    rows = [r for r in (parse(x) for x in open(path)) if r]
    ok = bad = 0
    changes = []
    for (k0, c0, _), (k1, c1, raw) in zip(rows, rows[1:]):
        if k0 < 1000:            # the visits at steps 276 and 636 come before the law starts
            continue
        if c0 is None or c1 is None:
            changes.append(f"{k1:>14,}  (not of the form)  {raw[:90]}")
            continue
        pred = regular(c0)
        if pred is None:
            s, H, v, w, m, j = c0
            s1, H1, v1, w1, m1, j1 = c1
            changes.append(f"{k1:>14,}  s={s} H={H} X={bits(v, w)} m={m} j={j} t={borrows(s, v, w)}"
                           f"  ->  s={s1} H={H1} X={bits(v1, w1)} m={m1} j={j1}")
            continue
        good = pred == c1
        ok += good; bad += not good
        s, H, v, w, m, j = c0
        print(f"{k1:>14,}  s={s:<3} w={w:<3} v={v:<8} (m, j) = ({m}, {j}) -> ({c1[4]}, {c1[5]})  t={borrows(s, v, w):<4}",
              "ok" if good else f"DIFFERS: {c1}")
    print(f"regular rounds: {ok} as the law says, {bad} not")
    print("phase changes (m < t) and visits not of the form:")
    for x in changes:
        print("  " + x)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    main(sys.argv[1])
