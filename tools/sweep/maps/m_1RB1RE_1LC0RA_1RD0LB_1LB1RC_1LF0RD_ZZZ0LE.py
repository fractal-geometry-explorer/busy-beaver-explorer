"""1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE: lean/Phase1.lean `ph`, `next`, `orbit`, `halts_iff_orbit`.

step = Lean `next n = ph (n-1) 0 0`, evaluating `ph` with each run of identical bounces
(K+1, i, m+1) -> (K, i+1, m) done at once (same function, O(log n) sub-phases instead of O(n) bounces).
accel = the closed form of py/orbit.py / tools/c/redmaps.c `re1` (README derivation; NOT proved in Lean; checked
equal to step here for every n < 200,000 and on the first 10,000 orbit states)."""
from maps._common import Stuck, bl

MACHINE = "1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE"
LEAN = "holdouts/1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE/lean/Phase1.lean: ph, next, orbit, halts_iff_orbit"
VARS = ("n",)
START = (1,)
HALT = "ph (n-1) 0 0 = none (reaches K = 2 with m = 0); in closed form n = c_{i+1}, c_i = 10*2^i - i - 7"
KIND = "power-of-2"
BOUND = ("8e6 map steps, n then 5,332,435 bits (status.json; halt-hunt/maps/NOTES.md, redmaps re1, "
         "checkpoints/map_re1.ck)")


def ph(K, i, m):
    """Lean `ph`; returns (value or None, label of the final case)."""
    while True:
        if m == 0:
            if K == 0:
                return 4 * i + 7, "K0"
            if K == 1:
                return 4 * i + 10, "K1"
            if K == 2:
                return None, "H"
            if K == 3:
                return 2 * i + 9, "K3"
            K, i, m = K - 4, 0, 2 * i + 5
        elif K == 0:
            return 4 * i + (m - 1) + 8, "m"
        else:
            t = min(K, m)  # t bounces (K+1, i, m+1) -> (K, i+1, m)
            K, i, m = K - t, i + t, m - t


def step(s):
    (n,) = s
    if n < 1:
        raise Stuck("samples S n have n >= 1 (ph_pos); n = %d" % n)
    v, lab = ph(n - 1, 0, 0)
    if v is None:
        return None, "H"
    return (v,), lab


def c(i):
    return (10 << i if i >= 0 else 5) - i - 7


def level(n):
    """The i with c_i < n <= c_{i+1}."""
    i = max(-1, n.bit_length() - 5)
    while c(i + 1) < n:
        i += 1
    while c(i) >= n:
        i -= 1
    return i


def accel(s):
    (n,) = s
    if n < 1:
        raise Stuck("samples S n have n >= 1 (ph_pos); n = %d" % n)
    i = level(n)
    if n == c(i + 1):
        return None, 1, "H"
    return (3 * n - 2 * c(i) + i + 3,), 1, "c"


def margin(s):
    (n,) = s
    return bl(c(level(n) + 1) - n)
