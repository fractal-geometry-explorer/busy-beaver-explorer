"""1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC: lean/Map.lean `f`, `orb`, `sample_step`, `halts_iff`."""
from maps._common import Stuck, bl

MACHINE = "1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC"
LEAN = "holdouts/1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC/lean/Map.lean: f, orb, sample_step, halts_iff"
VARS = ("p", "r")
START = (2, 2)
HALT = "p = 1"
KIND = "power-of-2"
BOUND = ("30,000 samples, numbers 1,835 digits, > 10^3669 machine steps (Lean kernel, lean/Bound.lean; "
         "status.json)")


def step(s):
    p, r = s
    if p < 1 or r < 1:
        raise Stuck("sample_step needs p, r >= 1; got (%d, %d)" % (p, r))
    if p == 1:
        return None, "H"
    if p == 3:
        return ((r + 5, 2), "p3o") if r % 2 == 1 else ((r + 5, 1), "p3e")
    if p % 2 == 0:
        return (3 * ((p - 2) // 2) + r + 4, 1), "even"
    m = (p - 1) // 2
    return (m - 1, m + r + 3), "half"


def margin(s):
    """A halving chain p -> (p-3)/2 -> ... reaches 1 iff p + 3 is a power of 2 (>= 4).  Distance of p + 3 to the
    nearest power of 2, measured relative to p (closeness = bits(p+3) - bits(distance), constant along a chain)."""
    p, r = s
    q = p + 3
    L = q.bit_length()
    d = min(q - (1 << (L - 1)), (1 << L) - q)
    return bl(d) + max(bl(p), bl(r)) - bl(q)
