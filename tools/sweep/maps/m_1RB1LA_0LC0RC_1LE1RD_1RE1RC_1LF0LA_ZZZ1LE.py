"""1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE: lean/Reduction.lean `F`, `orbit`, `halts_iff`, `halts_iff_pow2`
(the cases proved in lean/Macro.lean)."""
from maps._common import Stuck, bl

MACHINE = "1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE"
LEAN = ("holdouts/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE/lean/Reduction.lean: F, orbit, K_step, halts_iff, "
        "halts_iff_pow2")
VARS = ("p", "q")
START = (0, 2)
HALT = "p = 1 (equivalently: a sample with q = 1 has p + 3 a power of two, halts_iff_pow2)"
KIND = "power-of-2"
BOUND = ("200,000 samples, p then 40,089 bits (status.json; Lean native time 200000 >= 2^80181, "
         "lean/LowerBound.lean; kernel 5,000 samples)")


def step(s):
    p, q = s
    if p == 1:
        return None, "H"
    if p == 0:
        if q < 1:
            raise Stuck("K 0 0 does not occur (Inv) and is not covered by K_step")
        return (2, q - 1), "zero"
    if p % 2 == 1:
        return ((p - 3) // 2, q + (p + 5) // 2), "odd"
    return (3 * p // 2 + q, 1), "even"


def margin(s):
    """A halving chain p -> (p-3)/2 -> ... reaches 1 iff p + 3 is a power of 2 (>= 4).  Distance of p + 3 to the
    nearest power of 2, measured relative to p (closeness = bits(p+3) - bits(distance), constant along a chain)."""
    p, q = s
    x = p + 3
    L = x.bit_length()
    d = min(x - (1 << (L - 1)), (1 << L) - x)
    return bl(d) + max(bl(p), bl(q)) - bl(x)
