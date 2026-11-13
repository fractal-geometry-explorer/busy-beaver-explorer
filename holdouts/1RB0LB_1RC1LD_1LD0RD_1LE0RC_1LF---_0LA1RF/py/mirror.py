"""Check that this machine's table is the mirror image of 1RB0LB_1RC0LA_1RD---_0RE1LD_1LF0RF_1LA1RB's, with its
states renamed, and print the renaming.  The two runs differ only in the start state: this machine starts in the
state that is E of the other one.

usage: python3 holdouts/1RB0LB_1RC1LD_1LD0RD_1LE0RC_1LF---_0LA1RF/py/mirror.py
"""
M = "1RB0LB_1RC1LD_1LD0RD_1LE0RC_1LF---_0LA1RF"
OTHER = "1RB0LB_1RC0LA_1RD---_0RE1LD_1LF0RF_1LA1RB"
# state of OTHER -> state of M
REN = {"A": "C", "B": "D", "C": "E", "D": "F", "E": "A", "F": "B"}


def table(m):
    rows = m.split("_")
    return {(chr(65 + i), b): rows[i][3 * b:3 * b + 3] for i in range(len(rows)) for b in (0, 1)}


def mirrored_renamed(t):
    out = {}
    for (s, b), x in t.items():
        if x == "---":
            out[(REN[s], b)] = x
        else:
            out[(REN[s], b)] = x[0] + {"L": "R", "R": "L"}[x[1]] + REN[x[2]]
    return out


if __name__ == "__main__":
    assert mirrored_renamed(table(OTHER)) == table(M), "not a mirror image"
    print(f"{M} = mirror image of {OTHER} with states renamed {REN}; it starts in {M}'s A = the other's E")
