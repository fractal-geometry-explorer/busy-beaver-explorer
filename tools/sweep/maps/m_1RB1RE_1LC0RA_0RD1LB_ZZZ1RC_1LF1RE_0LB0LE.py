"""1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE: lean/Map.lean `f`, `orbit`, `halts_iff_orbit`.

W p 0 r = 0 (10)^p 0 1^r E> 0.  f(p, r) = (2p+2, r-p-1) if r >= p+2; none (halt) if r = p+1; (2, 4p+1) if r = p;
(p-r, 4r+2) if r < p.  Halts from blank iff the orbit of (2, 1) reaches none.
"""
from maps._common import Stuck, bl

MACHINE = "1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE"
LEAN = "holdouts/1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE/lean/Map.lean: f, orbit, halts_iff_orbit"
VARS = ("p", "r")
START = (2, 1)
HALT = "r = p + 1"
KIND = "subtractive-3x"
BOUND = "3e7 map steps, 6.5e6 bits (tools/c/redmaps.c re0, halt-hunt/maps/NOTES.md, 16 Nov 2026)"


def step(s):
    p, r = s
    if r < 1:
        raise Stuck("r = 0 is outside map_step (needs 1 <= r)")
    if r >= p + 2:
        return (2 * p + 2, r - p - 1), "D"
    if r == p + 1:
        return None, "H"
    if r == p:
        return (2, 4 * p + 1), "="
    return (p - r, 4 * r + 2), "<"


def margin(s):
    p, r = s
    return bl(r - p - 1)
