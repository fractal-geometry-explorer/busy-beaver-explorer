"""1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA: lean/Reset.lean `next`, `orbit`, `halts_iff`."""
from maps._common import Stuck

MACHINE = "1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA"
LEAN = "holdouts/1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA/lean/Reset.lean: next, orbit, halts_iff (next_spec, start)"
VARS = ("x", "c", "six")
START = (4, 4, False)
HALT = "a reset (c = 0 or c = 1, six false) whose new block B = 3*floor(x/2)+7(+t) is even with x even"
KIND = "reset-table"
BOUND = ("585 map terms (orbit_585, native_decide): phases 0-2 without halt; term 585 is S_3(6, c) with "
         "c ~ 2.3e101, so phase 3 needs ~1e101 iterates (NOTES.md: out of reach)")


def _k4T2(B):
    return None if B % 2 == 0 else (4, (B - 5) // 2, False)


def _k5T2(B):
    return (6, (B - 8) // 2, False) if B % 2 == 0 else (5, (B - 5) // 2, False)


def _k4T13(B):
    return None if B % 2 == 0 else (4, (B - 3) // 2, True)


def _k5T13(B):
    return (6, (B - 6) // 2, True) if B % 2 == 0 else (5, (B - 3) // 2, True)


def step(s):
    x, c, six = s
    if x < 1:
        raise Stuck("next_spec needs x >= 1")
    if c >= 2:
        return (3 * x // 2 + 7, c - 2, six), "step"
    tl = 6 if six else 3
    if c == 0:
        B = 3 * (x // 2) + 7 + tl
        r = _k4T2(B) if x % 2 == 0 else _k5T2(B)
        lab = "reset0"
    elif not six:
        B = 3 * (x // 2) + 7
        r = _k4T13(B) if x % 2 == 0 else _k5T13(B)
        lab = "reset1"
    else:
        y = 3 * (x // 2) + 7 if x % 2 == 0 else 3 * (x // 2) + 8
        r = (3 * y // 2 + 4, 1, False)
        lab = "reset1six"
    if r is None:
        return None, "H"
    return r, lab
