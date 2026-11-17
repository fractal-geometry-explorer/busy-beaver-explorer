"""1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC: lean/Round.lean `next`, `orbit`, `halts_iff`.

E(m, k) = 0^inf D> 110 (10)^m (110)^k 0^inf.  next(3t, k) = (4t+4, k-1) (natural subtraction: k = 0 stays 0);
next(3t+1, k) = (4t+4, k+1); next(3t+2, 0) = none (halt); next(3t+2, k+1) = (4t+5, k+2).
Halts from blank iff the orbit of (8, 1) reaches none.
"""
from maps._common import Stuck

MACHINE = "1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC"
LEAN = "holdouts/1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC/lean/Round.lean: next, orbit, halts_iff"
VARS = ("m", "k")
START = (8, 1)
HALT = "m = 2 mod 3 and k = 0"
KIND = "parity-3/2"
BOUND = "1e6 rounds (status.json, Python py/orbit.py; k = 331,763 at the end)"


def step(s):
    m, k = s
    if m < 1:
        raise Stuck("m = 0 is outside round_some (needs 1 <= m)")
    t, r = divmod(m, 3)
    if r == 0:
        return (4 * t + 4, k - 1 if k > 0 else 0), "0"
    if r == 1:
        return (4 * t + 4, k + 1), "1"
    if k == 0:
        return None, "H"
    return (4 * t + 5, k + 1), "2"


# no margin: the halting test is a small counter k reaching 0 (k ~ n/3 drifts up), not a near-miss of a big number
