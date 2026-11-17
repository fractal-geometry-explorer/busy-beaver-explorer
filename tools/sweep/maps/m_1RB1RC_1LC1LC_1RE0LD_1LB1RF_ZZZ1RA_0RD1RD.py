"""1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD: lean/Macro.lean `next`, `halts_iff'`."""
from maps._common import bl

MACHINE = "1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD"
LEAN = "holdouts/1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD/lean/Macro.lean: next, halts_iff'"
VARS = ("k", "u", "v")
START = ("P", 3, 0)
HALT = "u = v or u = v + 1"
KIND = "subtractive-3x"
BOUND = "2e7 rounds (halt-hunt/maps, redmaps rc)"


def step(s):
    k, u, v = s
    if u == v or u == v + 1:
        return None, "H"
    if u < v:
        return (k, 3 * u + (2 if k == "P" else 3), v - u - 1), k + "<"
    return ("Q" if k == "P" else "P", 3 * v + (3 if k == "P" else 5), u - v - 2), k + ">"


def margin(s):
    k, u, v = s
    return bl(2 * (u - v) - 1)
