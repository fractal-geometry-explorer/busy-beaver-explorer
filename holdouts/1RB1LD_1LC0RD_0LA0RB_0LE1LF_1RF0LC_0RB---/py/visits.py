"""Where the head goes in 1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---: crossings of every word boundary between two steps.

The tape is cut into words "1^a 0^b" (written a:b; in practice 1:1 = `10`, 2:1 = `110`, 1:3 = `1000`, 2:3 = `11000`),
as it stands at step FROM, and the number of times the head crosses the left edge of each word to the right between
steps FROM and TO is printed, with the ratio to the word before.  Between two left-end extensions the ratios are
(to rounding) 3 across each `110` word, 1/2 across each binary pair (`10`, `1000`), and 5/2, 3/10 or 3/5 at the
junctions: the tape works as a mixed-radix counter whose digits are the words (see README.md).

usage: python3 visits.py FROM TO        e.g. 230340600 249136500 (between the extensions at 230,340,555 and
                                         249,136,554; pure Python, about a minute)
"""
import collections
import re
import sys

M = "1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---"


def table(m):
    T = {}
    for s, row in enumerate(m.split("_")):
        for b in (0, 1):
            t = row[3 * b:3 * b + 3]
            T[(s, b)] = None if t[0] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


def main(a, b):
    T = table(M)
    tape, h, q, n, lo, hi = {}, 0, 0, 0, 0, 0
    while n < a:
        w, d, q = T[(q, tape.get(h, 0))]; tape[h] = w; h += d; n += 1
        lo, hi = min(lo, h), max(hi, h)
    lo0 = lo
    cells = "".join(str(tape.get(i, 0)) for i in range(lo, hi + 1))
    cross = collections.Counter()
    while n < b:
        w, d, q = T[(q, tape.get(h, 0))]; tape[h] = w
        if d > 0:
            cross[h + 1 - lo0] += 1
        h += d; n += 1
        lo = min(lo, h)
    print(f"steps {a:,} to {b:,}; the left end moved by {lo0 - lo} cells")
    print("start  word  crossings  ratio")
    prev = None
    for m in re.finditer(r"1+0*", cells):
        word = m.group(0); ones = len(word.rstrip("0"))
        c = cross[m.start()]
        print(f"{m.start():>5}  {ones}:{len(word) - ones}  {c:>9}  {'' if not prev else f'{c / prev:.3f}'}")
        if c:
            prev = c


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    main(int(sys.argv[1]), int(sys.argv[2]))
