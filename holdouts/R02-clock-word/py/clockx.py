"""Register, in clock.py, the members of family R02 that share a table with a machine whose clock is already
described there (the same table started in another state, possibly in a mirror), so that the exact accelerated
simulator of clock.py runs them too.

The renaming is found by brute force over the 120 permutations of B..F x {plain, mirror}... (all 720 of A..F, since
the start state differs).  For a base machine b with parameters (X, Y, ...) and a renaming pi (state s of b is
state pi(s) of m), m gets (pi(X), pi(Y), ...), the same sweep, and MIRROR flipped when the renaming mirrors.

usage: python3 clockx.py            list the registrations
"""
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE", "py"))
import clock  # noqa: E402

S = "ABCDEF"


def rows(m):
    return [[g[0:3], g[3:6]] for g in m.split("_")]


def renamed(m, pi, mir):
    """The table of m with state s called pi[s] (and L/R swapped when mir), as a TNF-free string in order A..F of
    the new names."""
    out = [None] * 6
    for s, (r0, r1) in enumerate(rows(m)):
        new = []
        for r in (r0, r1):
            if r[0] == "-":
                new.append("---")
            else:
                d = r[1]
                if mir:
                    d = {"L": "R", "R": "L"}[d]
                new.append(r[0] + d + S[pi[S.index(r[2])]])
        out[pi[s]] = "".join(new)
    return "_".join(out)


def find_map(base, m):
    """(pi, mir) with renamed(base, pi, mir) == m, or None."""
    for mir in (False, True):
        for pi in itertools.permutations(range(6)):
            if renamed(base, pi, mir) == m:
                return pi, mir
    return None


def register(m, base):
    r = find_map(base, m)
    if r is None:
        raise ValueError(f"{m} is not a renaming of {base}")
    pi, mir = r
    p = clock.PARAMS[base]
    clock.PARAMS[m] = (S[pi[S.index(p[0])]], S[pi[S.index(p[1])]]) + tuple(p[2:])
    for d in (clock.SWEEP, clock.VISIT, clock.MODES):
        if base in d:
            d[m] = d[base]
    if base in clock.ONES_FIRST:
        clock.ONES_FIRST.add(m)
    if (base in clock.MIRROR) != mir:
        clock.MIRROR.add(m)
    return pi, mir


# member -> base machine of clock.py with the same table
DERIVED = {
    "1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_0RA---": "1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---",
    "1RB0RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RB---": "1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---",
    "1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---": "1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE",
    "1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---": "1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE",
    "1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD": "1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF",
    "1RB1RE_1LC1RD_1LA1LC_0RA0RB_1RF0LE_1RA---": "1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF",
}

for _m, _b in DERIVED.items():
    register(_m, _b)

if __name__ == "__main__":
    for m, b in DERIVED.items():
        print(m, "<-", b, find_map(b, m), clock.PARAMS[m], m in clock.MIRROR)
