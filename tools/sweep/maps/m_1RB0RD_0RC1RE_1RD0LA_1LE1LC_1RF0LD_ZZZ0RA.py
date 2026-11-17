"""1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA: lean/Map.lean `next`, `orbit`, `next_none`, `halts_iff`."""
from maps._common import Stuck

MACHINE = "1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA"
LEAN = "holdouts/1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA/lean/Map.lean: next, orbit, next_none, halts_iff"
VARS = ("m", "n")
START = (14, 5)
HALT = "m = 1 and n = 1 mod 3"
KIND = "reset-table"
BOUND = ("6,819 phases evaluated (Lean native, lean/Orbit.lean check_6819: second reset, stack m > 10^2900); "
         "hence the next 10^2899 phases provably exist and no halt in 10^2899 steps (runs_long)")


def step(s):
    m, n = s
    if n < 3:
        raise Stuck("n < 3 never occurs (next_ge) and is not covered by next_reach")
    k, r = (n - 3) // 3, (n - 3) % 3
    if r == 0:
        if m == 0:
            return (2 * k + 4, 5), "r0reset"
        return (m - 1, 8 * k + 19), "r0"
    if r == 1:
        if m == 0:
            return (0, 8 * k + 18), "r1m0"
        if m == 1:
            return None, "H"
        return (m - 2, 8 * k + 29), "r1"
    if m == 0:
        return (0, 8 * k + 18), "r2m0"
    if m == 1:
        return (2 * k + 8, 5), "r2reset"
    return (m - 2, 8 * k + 35), "r2"
