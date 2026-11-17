"""1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB: lean/Map.lean `f`, `orb`, `sample_step`, `halts_iff`."""
from maps._common import Stuck, bl

try:
    from gmpy2 import mpz as _Z
except ImportError:  # pragma: no cover
    _Z = int

MACHINE = "1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB"
LEAN = "holdouts/1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB/lean/Map.lean: f, orb, sample_step, halts_iff"
VARS = ("p", "r")
START = (3, 1)
HALT = "p = 2 and 3 | r"
KIND = "power-of-3"
BOUND = ("30,000 samples, numbers 1,874 digits, > 10^3747 machine steps (Lean kernel, lean/Bound.lean; "
         "status.json)")


def step(s):
    p, r = s
    if p < 1 or r < 1:
        raise Stuck("sample_step needs p, r >= 1; got (%d, %d)" % (p, r))
    if p == 1:
        return (r + 4, 1), "p1"
    if p == 2:
        if r % 3 == 1:
            return (r + 5, 1), "p2a"
        if r % 3 == 2:
            return (r + 3, 2), "p2b"
        return None, "H"
    if p % 3 == 0:
        return (4 * (p // 3 - 1) + r + 6, 1), "c0"
    if p % 3 == 1:
        return (4 * ((p - 4) // 3) + r + 8, 1), "c1"
    k = (p - 5) // 3
    return (k + 1, 2 * k + r + 5), "div"


def margin(s):
    """A division chain p -> (p-2)/3 -> ... reaches 2 iff p + 1 is a power of 3 (>= 3).  Distance of p + 1 to the
    nearest power of 3, measured relative to p (padded by the bits of p + 1 missing from the state), so that the
    closeness is bits(p) - bits(distance) and stays constant along a chain."""
    p, r = s
    q = p + 1
    e = max(0, int((bl(q) - 1) * 0.6309297535714574) - 1)  # log_3(2): a lower estimate of floor(log_3 q)
    t = _Z(3) ** e
    while t * 3 <= q:
        t *= 3
    while t > q:
        t //= 3
    d = min(q - t, 3 * t - q)
    big = max(bl(p), bl(r))
    return bl(d) + big - bl(q)
