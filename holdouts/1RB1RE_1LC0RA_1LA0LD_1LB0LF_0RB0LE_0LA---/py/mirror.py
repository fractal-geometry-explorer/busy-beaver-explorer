"""Check that this machine is the mirror image of 1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD--- with states A and D
exchanged: try every renaming of the states (and both orientations) and print the ones that match exactly.

usage (from the repo root): python3 holdouts/1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---/py/mirror.py
"""
import itertools

A = "1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---"
B = "1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---"


def table(m):
    return [[g[3 * y:3 * y + 3] for y in range(2)] for g in m.split("_")]


ta, tb = table(A), table(B)
for perm in itertools.permutations(range(6)):
    for mirror in (False, True):
        ok = True
        for s in range(6):
            for y in range(2):
                t = ta[s][y]
                if t != "---":
                    d = {"L": "R", "R": "L"}[t[1]] if mirror else t[1]
                    t = t[0] + d + "ABCDEF"[perm[ord(t[2]) - 65]]
                ok &= tb[perm[s]][y] == t
        if ok:
            print("match:", "mirror" if mirror else "same direction",
                  ", ".join("%s->%s" % ("ABCDEF"[s], "ABCDEF"[perm[s]]) for s in range(6)))
