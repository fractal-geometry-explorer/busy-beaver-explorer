"""1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD (Space Needle): lean/Macro.lean `g`, `orbit`, `halts_iff`.

X(b, c) = 0^inf A>0 1^b 0 0 1^c 0^inf.  g(0, c) = (c+2, 1); g(1, c) = (1, c) (halt); g(2k+2, c) = (5k+c+7, 1);
g(2k+3, c) = (k, k+c+4).  Halts from blank iff the orbit of (3, 1) reaches b = 1.  Equivalent (lean/Collatz.lean
`halts_iff_pow2`) to Doucette's sequence D = b + 3 at the c = 1 visits reaching a power of two.
"""
from maps._common import Stuck, bl

MACHINE = "1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD"
LEAN = "holdouts/1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD/lean/Macro.lean: g, orbit, halts_iff (Collatz.lean: halts_iff_pow2)"
VARS = ("b", "c")
START = (3, 1)
HALT = "b = 1 (equivalently: b + 3 is a power of two at a c = 1 visit)"
KIND = "power-of-2"
BOUND = "3e6 Doucette terms (c/doucette.c, trusted C); 300,000 terms Lean native_decide (Fit_native); community 1e8 terms"


def step(s):
    b, c = s
    if c < 1:
        raise Stuck("c = 0 is outside g_step (needs 1 <= c)")
    if b == 1:
        return None, "H"
    if b == 0:
        return (c + 2, 1), "0"
    if b % 2 == 0:
        k = (b - 2) // 2
        return (5 * k + c + 7, 1), "E"
    k = (b - 3) // 2
    return (k, k + c + 4), "O"


def margin(s):
    # halting needs D = b + 3 to be a power of two; the odd steps halve D, so the deciding quantity is odd(D) - 1
    D = s[0] + 3
    return bl(D // (D & -D) - 1)
