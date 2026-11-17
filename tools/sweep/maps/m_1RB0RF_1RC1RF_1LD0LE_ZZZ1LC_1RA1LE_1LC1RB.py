"""1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB: lean/Macro.lean `f`, `g`, `orbit`, `halts_iff`, `f_none_iff`."""
from maps._common import Stuck, bl

MACHINE = "1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB"
LEAN = "holdouts/1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB/lean/Macro.lean: f, g, orbit, halts_iff, f_none_iff"
VARS = ("n",)
START = (4,)
HALT = "g (n-1) 2 = none, i.e. n + 2 is a power of two >= 4 (f_none_iff)"
KIND = "power-of-2"
BOUND = "200,000 passes, n then 80,223 bits (status.json, py/study.py); 10,000 passes native in Lean (orbit_10000)"


def g(b, c):
    """Lean `g`, with its tail recursion b -> (b-3)/2 unrolled into a loop."""
    while True:
        if b == 0:
            return c + 2 if c % 2 == 0 else (3 * c + 9) // 2, "0"
        if b % 2 == 0:
            return c + 3 * (b // 2) + 2, "e"
        if b == 1:
            return None, "H"
        i = (b - 3) // 2
        b, c = i, c + i + 4


def step(s):
    (n,) = s
    if n < 1:
        raise Stuck("orbit values are positive (orbit_pos); n = %d" % n)
    m, lab = g(n - 1, 2)
    if m is None:
        return None, "H"
    j = ((n + 2) & -(n + 2)).bit_length() - 1
    return (m,), lab + (str(j) if j < 8 else "8+")


def margin(s):
    (n,) = s
    N = n + 2
    L = N.bit_length()
    return bl(min(N - (1 << (L - 1)), (1 << L) - N))
