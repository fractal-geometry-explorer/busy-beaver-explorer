"""1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF: lean/Phase.lean `ph`, `phN`, `endv`, `ends`, `epochs`, `halts_iff`.

Lean iterates whole epochs: `ends c = endv (c % 4) (phN (c / 4) (3, 5))`.  An epoch has c/4 phases, and epoch 3
already has 114,817,814,715,807, so this module steps one PHASE at a time on the configuration P c u x =
0^inf 1^c (01)^u 0 0 (10)^x F>: for c >= 4 one `ph` (P (c+4) u x -> P c (ph (u,x))), for c < 4 the epoch end
`endv c u x` (new epoch P c' 3 5, or the halt).  Composing these steps is literally `ends` (phN is iterated ph),
so the orbit of (3, 3, 5) passes through (epochs k, 3, 5) for every k."""
from maps._common import Stuck

MACHINE = "1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF"
LEAN = ("holdouts/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF/lean/Phase.lean: ph, phN, endv, ends, epochs, "
        "halts_iff, epochs_first, epochs_4")
VARS = ("c", "u", "x")
START = (3, 3, 5)
HALT = "an epoch end (c < 4) with endv c u x = none: c = 2, or c = 0 with u = 2, or c = 1 with u = 3"
KIND = "parity-3/2"
BOUND = ("Lean (kernel): epochs 0-3 have c = 3, 20, 297, 459271258863231 and epoch 3 ends in a new epoch "
         "(epochs_first, epochs_4), so no halt in the first 80 + 114,817,814,715,807 phases; epoch 4's phases "
         "(c4 ~ 10^(2e13)) never computed (README)")


def ph(u, x):
    X = x + u + 4
    return 2 + X % 2, 3 * (X // 2) - 1


def endv(r, u, x):
    if r == 3:
        return 2 * x + 4 + 2 * u
    if (r == 0 and u == 3) or (r == 1 and u == 2):
        return 2 * x + 5
    return None


def step(s):
    c, u, x = s
    if u not in (2, 3):
        raise Stuck("u = %d is outside the phase rule (u = 2 or 3)" % u)
    if c >= 4:
        u2, x2 = ph(u, x)
        return (c - 4, u2, x2), "ph"
    if x < 16 and s != (3, 3, 5):
        raise Stuck("epoch end with x = %d < 16 is outside end_some/end_none" % x)
    c2 = endv(c, u, x)
    if c2 is None:
        return None, "H"
    return (c2, 3, 5), "end%d%d" % (c, u)
