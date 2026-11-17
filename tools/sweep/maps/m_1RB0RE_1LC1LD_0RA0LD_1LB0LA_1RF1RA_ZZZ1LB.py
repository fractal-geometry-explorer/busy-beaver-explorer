"""1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB: lean/Macro.lean `next`, `orbit`, `round`, `halts_iff`."""

MACHINE = "1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB"
LEAN = "holdouts/1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB/lean/Macro.lean: next, orbit, round, halts_iff"
VARS = ("k", "z")
START = (0, 5)
HALT = "k odd and z = 0"
KIND = "reset-table"
BOUND = ("3 rounds (fuel 5, 14, 185) then the start of round 4, (0, 22205951667644132025548), after 138 "
         "applications of next (status.json, py/orbit.py); round 4 cannot halt before its fuel is spent "
         "(~1e22 applications)")


def step(s):
    k, z = s
    j = k // 2
    if k % 2 == 0:
        if z == 0:
            return (0, 3 * j + 2), "e-reset"
        return (3 * j + 1, z - 1), "e"
    if z == 0:
        return None, "H"
    if z == 1:
        return (0, 3 * j + 5), "o-reset"
    return (3 * j + 4, z - 2), "o"
