"""Read lines of snap.c output (t pos state lo hi bits) and print the tape in particle form:
a number n is (10)^n (the background), P = 0 1 1 0 0 (the stationary particle), `0` and `1^2 0` are the moving
particle Q in its two forms, the rest run-length coded.
    gcc -O2 -o snap py/snap.c && ./snap MACHINE 10000000000 L 1 9998000000 | tail -1 | python3 py/tokens.py"""
import re, sys


def rl(s, words=("10",)):
    out, i, n = [], 0, len(s)
    while i < n:
        best = None
        for w in words:
            k = 0
            while s.startswith(w, i + k * len(w)):
                k += 1
            if k >= 2 and (best is None or k * len(w) > best[1] * len(best[0])):
                best = (w, k)
        if best:
            out.append("(%s)^%d" % best)
            i += best[1] * len(best[0])
        else:
            j = i
            while j < n and s[j] == s[i]:
                j += 1
            out.append(s[i] if j - i == 1 else "%s^%d" % (s[i], j - i))
            i = j
    return " ".join(out)


def toks(s):
    r = rl(s).replace("0 1^2 0^2", "P")
    out = []
    for x in r.split(" "):
        m = re.fullmatch(r"\(10\)\^(\d+)", x)
        out.append(m.group(1) if m else ("1" if x == "10" else x))
    return out


if __name__ == "__main__":
    for line in sys.stdin:
        f = line.split()
        if len(f) < 6:
            print(line.strip())
            continue
        t = toks(f[5])
        print(" ".join(f[:5]), "| P count", t.count("P"), "|", " ".join(t))
