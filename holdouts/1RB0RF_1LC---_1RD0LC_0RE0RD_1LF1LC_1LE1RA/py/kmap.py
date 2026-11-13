"""The sample map of 1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA, measured, and the run of it from blank tape.

The sample configuration is K(P, m) = 0^inf P (10)^m C> 1 1 1 1 1 0^inf.  `K(P, m)` below runs the machine from it
to the next sample (or a halt).  `T(P, m)` is the map for any m: it runs three representatives of m mod q (q = 2,
4, ...), checks that the next prefix is the same and the next count affine in m, and extrapolates.  That the map is
affine in m for every m is proved in Lean only for the prefixes `empty` and `1` (lean/Macro.lean); for the others
it is an observation (heuristic).

usage: python3 kmap.py [SAMPLES]     the run from blank tape (first sample K(1, 1) at step 30), and the shortest
                                     route of parities from the empty prefix to a halt
"""
import sys
from collections import Counter, deque
from fractions import Fraction

sys.set_int_max_str_digits(0)
TABLE = "1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA"


def parse(m):
    t = []
    for g in m.split("_"):
        row = []
        for y in (0, 1):
            s = g[3 * y:3 * y + 3]
            row.append(None if s[2] not in "ABCDEF" else (int(s[0]), 1 if s[1] == "R" else -1, "ABCDEF".index(s[2])))
        t.append(row)
    return t


TT = parse(TABLE)


def K(P, m, maxsteps=10 ** 8):
    """Run from K(P, m) to the next sample: (P', m', steps), or ('HALT', steps) / ('TO', steps)."""
    cells = [int(c) for c in P] + [1, 0] * m
    tape = {i: c for i, c in enumerate(cells)}
    pos, st = len(cells), 2
    for i in range(5):
        tape[pos + i] = 1
    n = 0
    while n < maxsteps:
        tr = TT[st][tape.get(pos, 0)]
        if tr is None:
            return ("HALT", n)
        w, d, st = tr
        tape[pos] = w
        pos += d
        n += 1
        if st == 2 and all(tape.get(pos + i, 0) == 1 for i in range(5)) and tape.get(pos + 5, 0) == 0:
            ones = [k for k, v in tape.items() if v]
            if max(ones) == pos + 4:
                s = "".join(str(tape.get(i, 0)) for i in range(min(ones), pos))
                mm = 0
                while s.endswith("10"):
                    s, mm = s[:-2], mm + 1
                return (s, mm, n)
    return ("TO", n)


cache = {}


def T(P, m):
    """The next sample after K(P, m) as (P', m'), or None for a halt (extrapolated, see the module docstring)."""
    for q in (2, 4, 8, 16, 32):
        key = (P, q, m % q)
        if key in cache:
            v = cache[key]
            break
        m0 = q + m % q + 6
        outs = [K(P, m0 + q * i) for i in range(3)]
        if all(o[0] == "HALT" for o in outs):
            v = cache[key] = ("H",)
            break
        if any(o[0] in ("HALT", "TO") for o in outs) or len({o[0] for o in outs}) != 1:
            continue
        a, b, c = [o[1] for o in outs]
        if b - a != c - b:
            continue
        slope = Fraction(b - a, q)
        v = cache[key] = (outs[0][0], slope, a - slope * m0, q)
        break
    else:
        raise ValueError(("no affine fit", P, m))
    if v[0] == "H":
        return None
    mm = v[1] * m + v[2]
    assert mm.denominator == 1
    return v[0], int(mm)


def route():
    """Shortest list of (prefix, parity) from the empty prefix to a halting (prefix, parity)."""
    prev, dq = {"": None}, deque([""])
    while dq:
        P = dq.popleft()
        for r in range(2):
            res = T(P, 100 + r)
            if res is None:
                out, x = [(P, r)], P
                while prev[x]:
                    out.append(prev[x])
                    x = prev[x][0]
                return list(reversed(out))
            if res[0] not in prev:
                prev[res[0]] = (P, r)
                dq.append(res[0])


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    r = route()
    print(f"shortest route to a halt from the empty prefix: {len(r)} samples")
    print("  " + " ".join(f"{p or 'e'}/{'odd' if b else 'even'}" for p, b in r))
    P, m, lens = "1", 1, Counter()
    for i in range(n):
        if i < 12:
            print(f"sample {i}: K({P or 'empty'}, {m})")
        x = T(P, m)
        if x is None:
            print("HALT after sample", i)
            return
        P, m = x
        lens[len(P)] += 1
    print(f"{n} samples, no halt; m has {len(str(m))} digits; prefix lengths seen: {sorted(lens.items())}")
    print("maps used, by the modulus they needed:", Counter(v[3] for v in cache.values() if v[0] != "H"))


if __name__ == "__main__":
    main()
