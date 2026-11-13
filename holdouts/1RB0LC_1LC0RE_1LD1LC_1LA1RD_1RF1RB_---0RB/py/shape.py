"""Tape shape at the last tape extensions, and the growth exponent of the width.

usage (from the repo root):
  gcc -O2 -o /tmp/tmrun tools/c/tmrun.c
  /tmp/tmrun MACHINE 1000000000 records 100000 > /tmp/rec.txt
  python3 holdouts/MACHINE/py/shape.py /tmp/rec.txt [WORDS] [N]

WORDS is a comma list like a=10,c=110 (longest word wins); N records per side are printed (default 4).
The exponent is the least-squares slope of log(width) against log(step) over the extensions after step 10^7.
"""
import math
import sys


def cells_of(body):
    c, head = [], None
    for k in body.split():
        if ">" in k:
            head = (k[0], len(c))
            k = k[2:]
            if not k:
                continue
        if "^" in k:
            a, b = k.split("^")
            c += [int(a)] * int(b)
        else:
            c += [int(ch) for ch in k]
    return c, head


def tokenize(cells, words):
    ws = sorted(words.items(), key=lambda kv: -len(kv[1]))
    s = "".join(map(str, cells))
    out, i = [], 0
    while i < len(s):
        for name, w in ws:
            if s.startswith(w, i):
                out.append(name)
                i += len(w)
                break
        else:
            out.append(s[i])
            i += 1
    res, j = [], 0
    while j < len(out):
        k = j
        while k < len(out) and out[k] == out[j]:
            k += 1
        res.append(out[j] + (f"^{k - j}" if k - j > 1 else ""))
        j = k
    return " ".join(res)


def main():
    words = dict(kv.split("=") for kv in sys.argv[2].split(",")) if len(sys.argv) > 2 and sys.argv[2] else {}
    n = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    rows = {"L": [], "R": []}
    pts = []
    for line in open(sys.argv[1]):
        p = line.split(None, 3)
        if len(p) < 4 or not p[0].isdigit() or p[1] not in "LR":
            continue
        rows[p[1]].append(p)
        pts.append((int(p[0]), int(p[2])))
    for s in "LR":
        for p in rows[s][-n:]:
            c, h = cells_of(p[3])
            print(p[0], s, "width", p[2], "head", h, ":", tokenize(c, words))
    pts = [q for q in pts if q[0] >= 10**7]
    xs = [math.log(a) for a, _ in pts]
    ys = [math.log(b) for _, b in pts]
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
    print(f"extensions: {len(rows['L'])} left, {len(rows['R'])} right; last width {pts[-1][1]} at step {pts[-1][0]};"
          f" width exponent after 10^7: {slope:.3f}")


if __name__ == "__main__":
    main()
