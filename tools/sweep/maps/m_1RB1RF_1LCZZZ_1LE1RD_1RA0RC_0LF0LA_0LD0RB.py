"""1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB: lean/Map.lean `emap`, `orbit`, `halts_iff` (`halts_iff_state`)."""
from maps._common import bl

MACHINE = "1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB"
LEAN = "holdouts/1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB/lean/Map.lean: emap, orbit, halts_iff, halts_iff_state"
VARS = ("side", "n", "k")
START = ("D", 3, 0)
HALT = "n odd and k = 1 (along the orbit: reached from D(n, k), n odd, 2k = n + 7)"
KIND = "doubling-pay"
BOUND = "40,000 epochs (1.95e9 jump steps, epoch value N 47,748 bits), c/emap.c (halt-hunt/maps NOTES.md)"


def _oth(s):
    return "D" if s == "A" else "A"


def step(x):
    s, n, k = x
    if k == 0:
        if n % 2 == 0:
            return (_oth(s), n + 3, 0), "k0even"
        return ("D", 1 if s == "A" else 3, (n + 1) // 2), "convert"
    if n % 2 == 0:
        if k == 1:
            return (_oth(s), n + 7, 0), "drain1"
        return (_oth(s), n + 4, k - 1), "drain"
    if k == 1:
        return None, "H"
    dc = 6 if s == "A" else 7
    if 2 * k > n + 5:
        return (s, 2 * n + dc, k - (n + 5) // 2), "double"
    if 2 * k == n + 5:
        return (s, 2 * n + dc + 3, 0), "double0"
    return (_oth(s), n + 6 - 2 * k, 2 * k), "fail"


def accel(x):
    """A run of k - 1 drain steps (n even, k >= 2) at once, as c/emap.c and py/emap.py `jump`."""
    s, n, k = x
    if k >= 2 and n % 2 == 0:
        j = k - 1
        return (s if j % 2 == 0 else _oth(s), n + 4 * j, 1), int(j), "drain"
    s2, lab = step(x)
    return s2, 1, lab


def margin(x):
    """From D(n, k), n odd, k >= 2, the doubling lands on the halting row iff 2k = n + 7."""
    s, n, k = x
    if s == "D" and n % 2 == 1 and k >= 2:
        return bl(2 * k - n - 7)
    return None
