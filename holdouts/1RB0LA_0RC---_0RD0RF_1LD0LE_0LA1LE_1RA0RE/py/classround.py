"""Rounds from every tape of a simple class, by plain simulation.

usage (from the repo root):  python3 holdouts/<M>/py/classround.py MACHINE N

A round start is E on a 0 at the left end (blank to its left) followed by a tape of the class
`0? 1^a1 (0 1^ai)*` (a1 >= 1, ai >= 2, single 0s between blocks) of at most N cells.  The round ends the next time
E is on a 0 at the leftmost visited cell.  Prints how many starts there are, and those whose round halts, does not
end within 10^6 steps, or ends on a tape outside the class.
"""
import collections
import re
import sys

PAT = re.compile(r"0?1+(011+)*")


def table(m):
    t = {}
    for i, g in enumerate(m.split("_")):
        for b in (0, 1):
            x = g[3 * b:3 * b + 3]
            t[(i, b)] = None if x[0] == "-" else (int(x[0]), 1 if x[1] == "R" else -1, ord(x[2]) - 65)
    return t


def round_s(t, st, maxsteps=10**6):
    tape = {i + 1: int(c) for i, c in enumerate(st)}
    pos, s, lo = 0, 4, 0
    for n in range(1, maxsteps):
        tr = t[(s, tape.get(pos, 0))]
        if tr is None:
            return n, "HALT"
        w, d, s = tr
        tape[pos] = w
        pos += d
        lo = min(lo, pos)
        if s == 4 and pos == lo and tape.get(pos, 0) == 0:
            hi = max([k for k, v in tape.items() if v] + [pos])
            return n, "".join(str(tape.get(i, 0)) for i in range(pos + 1, hi + 1))
    return None, "TIMEOUT"


def starts(N):
    def blocks(rem, first):
        for a in range(1 if first else 2, rem + 1):
            yield [a]
            for rest in blocks(rem - a - 1, False):
                yield [a] + rest
    for lead in ("", "0"):
        for bl in blocks(N - len(lead), True):
            yield lead + "0".join("1" * b for b in bl)


def main():
    M, N = sys.argv[1], int(sys.argv[2])
    t = table(M)
    tot, bad, ex = 0, collections.Counter(), []
    for st in starts(N):
        tot += 1
        _, out = round_s(t, st)
        if out in ("HALT", "TIMEOUT") or not PAT.fullmatch(out):
            bad[out if out in ("HALT", "TIMEOUT") else "outside the class"] += 1
            ex.append((st, out))
    print(f"{tot} round starts of at most {N} cells; not back in the class: {dict(bad)}")
    for st, out in ex[:10]:
        print(f"  {st} -> {out}")


if __name__ == "__main__":
    main()
