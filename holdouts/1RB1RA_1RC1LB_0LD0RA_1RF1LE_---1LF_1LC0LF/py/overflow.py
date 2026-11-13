"""The overflow round [.., X, B, A, 2A+3] of 1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF: the rules found by experiment,
checked against direct simulation (../c/blk.c, via verify_rounds.round_) for 3 <= X <= XMAX, 1 <= B <= BMAX,
2 <= A <= AMAX, with blank tape left of X.  `predict` is also used by blocks.py.

usage: python3 overflow.py [XMAX BMAX AMAX]
"""
import sys

from verify_rounds import build, round_


def predict(X, B, A):
    """The block list that replaces [X, B, A, 2A+3], or 'halt'.  None: no rule known."""
    if B == 1:
        return "halt"
    if B == 2:
        return [X + A + 1, 2 * A + 8]
    if B % 2:
        if B <= 2 * X + 1:
            return [X + A + 2, 2 * A + B + 5]
        if B == 2 * X + 3:
            return [X + A + 3, 2 * A + B + 6]
        return [X, A + 2 * X + 7, 2 * A + B - 2 * X + 3]
    if B <= 2 * X + 2:
        return [X - 1, A + B + 1, 2 * A + 6]
    if B == 2 * X + 4:
        return [X, A + B + 2, 2 * A + 6]
    return [X, 2 * X + 4, A + B - 2 * X - 1, 2 * A + 6]


def main(xmax, bmax, amax):
    build()
    k = 0
    for X in range(3, xmax + 1):
        for B in range(1, bmax + 1):
            for A in range(2, amax + 1):
                steps, res = round_([X, B, A, 2 * A + 3])
                got = "halt" if steps == "halt" else res
                want = predict(X, B, A)
                assert got == want, (X, B, A, got, want)
                k += 1
    print(f"ok: {k} overflow rounds, 3 <= X <= {xmax}, B <= {bmax}, 2 <= A <= {amax}")


if __name__ == "__main__":
    a = [int(x) for x in sys.argv[1:4]] or [8, 24, 9]
    main(*a)
