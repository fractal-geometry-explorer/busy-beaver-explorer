"""1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC: lean/Doubling.lean `op`, `opIter`, `halts_iff_op`."""
from maps._common import bl

MACHINE = "1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC"
LEAN = "holdouts/1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC/lean/Doubling.lean: op, opIter, halts_iff_op"
VARS = ("c", "u", "v")
START = (0, 2, 5)
HALT = "c = 0 and 2u = v"
KIND = "doubling-mod"
BOUND = "1e11 operations (5.0e10 visits, 54 resets, v ~ 3.5e10), c/odo.c (status.json); 1e7 by native_decide (op_native)"


def step(s):
    c, u, v = s
    if 2 * u < v:
        return (c, 2 * u, v + 1), "dbl"
    if c >= 1:
        if 2 * u == v:
            return (c - 1, 1, v + 2), "empty"
        return (c - 1, 2 * u - v, v + 1), "carry"
    if 2 * u == v:
        return None, "H"
    return (2 * (v - u - 1), 2 * u - v, 2 * u - v + 3), "reset"


def margin(s):
    """With c = 0 the next wrap is a reset, which halts iff 2u = v."""
    c, u, v = s
    if c == 0:
        return bl(2 * u - v)
    return None
