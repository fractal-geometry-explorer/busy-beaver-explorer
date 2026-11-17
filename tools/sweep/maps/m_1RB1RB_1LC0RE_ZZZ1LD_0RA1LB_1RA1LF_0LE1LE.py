"""1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE: lean/Round.lean `next`, `orb`, `halts_iff` (round_ok, Valid)."""
from maps._common import Stuck, bl

MACHINE = "1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE"
LEAN = "holdouts/1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE/lean/Round.lean: next, orb, halts_iff"
VARS = ("i", "j", "J")
START = (3, 1, False)
HALT = "i = j or i + 1 = j"
KIND = "subtractive-3x"
BOUND = "2e7 rounds (~6.1e6 bits), tools/c/redmaps.c rb (halt-hunt/maps NOTES.md)"


def step(s):
    i, j, J = s
    if not (i >= 1 and j >= 1 and (not J or j >= 2)):
        raise Stuck("outside Valid (round_ok needs 1 <= i, 1 <= j, J -> 2 <= j)")
    if i == j or i + 1 == j:
        return None, "H"
    if j + 2 <= i:
        return (i - j - 1, 3 * j + (3 if J else 2), J), "i>"
    if i == j + 1:
        return ((3 * i, 1, False) if J else (3 * i - 3, 3, True)), "i=j+1"
    if i + 2 == j:
        return ((3 * i + 3, 3, True) if J else (3 * i + 3, 1, False)), "j=i+2"
    return (j - i - 2, 3 * i + (5 if J else 3), not J), "j>"


def margin(s):
    i, j, J = s
    return bl(2 * (i - j) + 1)
