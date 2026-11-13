"""Follow the rounds of 1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA--- symbolically, past the proved families.

A round start is  0^inf A> (10)^4 110 (10)^N 10010 T.  The tail T is written as runs of 10 and single cells,
e.g. "1 [15998] 1 [9] 0101101" for TD 15998.  One round: sweep0, k = (N-2)//2 counting sweeps (closed form), then
the conversion, run by `bbtools.symtm` from the concrete configuration (shift rules cross the long runs), until the
next round start.  With `lean`, also writes the Lean rules of each conversion and the chain (`lean/Orbit.lean`).

usage: python3 orbit.py ROUNDS [lean]
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bbtools import symtm  # noqa: E402
from bbtools.machine import Machine  # noqa: E402
from bbtools.symtm import Blank, Config, Rep  # noqa: E402
import round as R  # noqa: E402

MM = Machine.parse(R.M)


def tri(k):
    return k * (k - 1) // 2


def tail_sym(tail):
    """'1 [15998] 1 [9] 0101101' -> symtm tokens string."""
    out = []
    for t in tail.split():
        out.append(f"(10)^{t[1:-1]}" if t.startswith("[") else " ".join(t))
    return " ".join(out) + " 0^inf"


def cells(tokens):
    out = []
    for t in tokens:
        if isinstance(t, Blank):
            break
        if isinstance(t, int):
            out.append(t)
        else:
            out.extend(list(t.word) * t.n.k)
    return out


def runs(c):
    """cell list -> '[n]' runs of 10 and single cells."""
    out, i = [], 0
    while i < len(c):
        n = 0
        while i + 2 * n + 1 < len(c) and c[i + 2 * n] == 1 and c[i + 2 * n + 1] == 0:
            n += 1
        if n:
            out.append(f"[{n}]")
            i += 2 * n
        else:
            out.append(str(c[i]))
            i += 1
    # merge single digits
    res = []
    for t in out:
        if not t.startswith("[") and res and not res[-1].startswith("["):
            res[-1] += t
        else:
            res.append(t)
    while res and set(res[-1]) == {"0"}:
        res.pop()
    return " ".join(res)


def conv_start(N, tail):
    k, x = divmod(N - 2, 2)
    q, r = divmod(k + 1, 2)
    xs = "1 0" if x else ""
    return f"0^inf A> (10)^{7 + 3 * k} 1 1 0 {xs} 1 0 0 1 0 (110110)^{q} {'1 1 0 ' * r}{tail_sym(tail)}", k, x


def next_round(N, tail):
    s, k, x = conv_start(N, tail)
    c = Config.parse(s)
    symtm.run(MM, c, R.round_start, max_moves=100000, rotate=True)
    cl = cells(c.right)
    # (10)^4 110 (10)^N' 10010 T
    assert cl[:11] == [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0], cl[:20]
    i = 11
    n = 0
    while cl[i:i + 2] == [1, 0]:
        i += 2
        n += 1
    if cl[i:i + 1] != [0]:
        return None, None, s, c
    N2 = n - 1
    rest = cl[i + 1:]
    # rest starts with "10" (the last two cells of 10010)
    assert rest[:2] == [1, 0]
    T2 = runs(rest[2:])
    steps = 8 * (N - 4) + 125 + k * (167 + 8 * x) + 58 * tri(k) + c.steps.k
    return N2, T2, s, steps


if __name__ == "__main__":
    N, T, t = 19199, "1 [15998] 1 [9] 0101101", 1842640229
    for i in range(int(sys.argv[1])):
        N2, T2, s, st = next_round(N, T)
        if N2 is None:
            print("not a round start:", st)
            break
        t += st
        print(f"round N={N2} tail={T2[:80]} step={t:.4e} ({len(str(t))} digits)")
        N, T = N2, T2
