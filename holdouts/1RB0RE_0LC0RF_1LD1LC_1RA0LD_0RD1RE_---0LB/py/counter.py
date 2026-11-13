"""The binary counter inside a level of 1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB (plain simulation, no proof).

Start a level with the tail (100111)^m:   0^inf D> 0 0 1^5 100 (10111)^b 1 (011110)^m 0111 0^inf .
After the grow phase the samples (state D on a new leftmost cell) of the form

    0^inf D> 0 0 1^5 (00111)^a  (100)^c  J  (100111)^k  0^inf ,     J a string of the words 100 and 11100,

are collected.  Read (100)^c J as a binary number V (100 = digit 0, 11100 = digit 1, most significant digit first).
The script checks that in successive such samples k goes down by one and V goes up by one, with the number of digits
c + |J| fixed, from V = 0, k = m until k = 1: the machine counts to m - 1 in binary, one unit at a time (the digits
are then consumed from the right).  That is why the level map of this tail depends on the binary digits of m and why
no rule with linear counts describes this phase.

usage (from the repo root):  python3 holdouts/1RB0RE_0LC0RF_1LD1LC_1RA0LD_0RD1RE_---0LB/py/counter.py [B M ...]
"""
import re
import sys

import rules as RU

PAT = re.compile(r"^((?:100)*)((?:11100(?:100|11100)*)?)((?:100111)*)$")


def check(b, m):
    a, X = 0, "100" + "10111" * b + "1" + "011110" * m + "0111"
    seen, steps, visits = [], 0, 0
    while True:
        a2, X, n = RU.visit(a, X)
        steps += n
        visits += 1
        if a2 < a:
            raise SystemExit(f"b={b} m={m}: the level ended before the counter phase finished")
        a = a2
        g = PAT.match(X)
        if not g:
            continue
        c = len(g.group(1)) // 3
        digits = re.findall("11100|100", g.group(2))
        v = int("".join("1" if w == "11100" else "0" for w in digits) or "0", 2)
        k = len(g.group(3)) // 6
        if seen and k == seen[-1][2]:
            continue
        seen.append((c + len(digits), v, k))
        if k == 1:
            break
    assert len(seen) >= 3, seen
    width, v0, k0 = seen[0]
    for i, (w, v, k) in enumerate(seen):
        assert (w, v, k) == (width, v0 + i, k0 - i), (b, m, i, seen[i], seen[0])
    assert v0 + k0 == m and seen[-1][1] == m - 1, (v0, k0, m)
    print(f"b={b} m={m}: counter went {v0} -> {seen[-1][1]} in single steps while k went {k0} -> 1; "
          f"{width} digits throughout; {visits} visits, {steps} steps")


def main():
    args = [int(x) for x in sys.argv[1:]]
    pairs = list(zip(args[0::2], args[1::2])) or [(40, 9), (40, 16), (41, 23), (60, 37), (61, 64), (80, 100)]
    for b, m in pairs:
        check(b, m)
    print("ALL OK")


if __name__ == "__main__":
    main()
