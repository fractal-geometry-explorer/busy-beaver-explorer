"""1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD: lean/MapThm.lean `mstep`, `orbit`, `halts_iff`.

K(x, m, s) = 1^4 0 (10)^x 1^m with the head in C on the cell s right of the block (blank beyond).
mstep(x, m, s):
  m even, x >= 1: (x-1, m+4, !s)                         B
  m even, x = 0 : ((m+6)/2, 3 if s else 1, false)         R
  m odd,  x = 0 : none (halt)                             H
  m odd,  x >= (m+5)/2 : (x-(m+5)/2, 2m+7-[s], s)         C
  m odd,  x+1 = (m+5)/2 and s = false : (2x+3, 1, false)   A'
  m odd,  otherwise : (2x+1, m+4-2x, !s)                  A
Halts from blank iff the orbit of (7, 1, false) reaches none.
"""
from maps._common import bl

MACHINE = "1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD"
LEAN = "holdouts/1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD/lean/MapThm.lean: mstep, orbit, halts_iff"
VARS = ("x", "m", "s")
START = (7, 1, False)
HALT = "m odd and x = 0 (only reachable from a C step with s = 0 landing exactly on x = (m+5)/2)"
KIND = "subtractive-3x"
BOUND = ("10,000 R rounds of the map (py/samplemap.py orbit, status.json: 29,225,208 C steps, 25,330 A steps, "
         "x thousands of bits); map checked against the machine for 1e10 steps (samplemap.py check)")


def step(st):
    x, m, s = st
    if m % 2 == 0:
        if x >= 1:
            return (x - 1, m + 4, not s), "B"
        return ((m + 6) // 2, 3 if s else 1, False), "R"
    if x == 0:
        return None, "H"
    h = (m + 5) // 2
    if h <= x:
        return (x - h, 2 * m + 7 - (1 if s else 0), s), "C"
    if x + 1 == h and not s:
        return (2 * x + 3, 1, False), "A'"
    return (2 * x + 1, m + 4 - 2 * x, not s), "A"


def accel(st):
    """A whole B phase at once: (x, m even, s) -> (0, m+4x, s xor [x odd]) in x steps; otherwise one step.
    (B phases are as long as x itself, up to thousands of bits, so `step` alone cannot get past a long one;
    the engine's step count n therefore becomes astronomically large once they start.)"""
    x, m, s = st
    if m % 2 == 0 and x >= 1:
        return (0, m + 4 * x, s ^ bool(x & 1)), x, "B"
    s2, lab = step(st)
    return s2, 1, lab


def margin(st):
    # halting needs x = 0 with m odd; x lands near 0 only at the end of a chain of C steps with s = 0
    x, m, s = st
    if m % 2 == 1 and not s:
        return bl(x)
    return None
