"""1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA (Antihydra): lean/Macro.lean `nxt`, `orbit`, `halts_iff`.

Q p a b = 0^inf 1^p 0 1^a 0 1^b B> 0^inf.  nxt(p, a) = (p+2, 3(a div 2)+4) for a odd, (p-1, 3(a div 2)+2) for a
even and p >= 1, none (halt) for a even and p = 0.  Halts from blank iff the orbit of (2, 7) reaches none.
"""
from maps._common import Stuck

MACHINE = "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"
LEAN = "holdouts/1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA/lean/Macro.lean: nxt, orbit, halts_iff"
VARS = ("p", "a")
START = (2, 7)
HALT = "a even and p = 0"
KIND = "parity-3/2"
BOUND = "1e6 walk steps (status.json, Python py/walk.py run; p = 498,505 at the end)"


def step(s):
    p, a = s
    if a < 2:
        raise Stuck("a < 2 is outside nxt_sound (needs 2 <= a)")
    if a % 2 == 1:
        return (p + 2, 3 * (a // 2) + 4), "odd"
    if p == 0:
        return None, "H"
    return (p - 1, 3 * (a // 2) + 2), "even"


# no margin: the halting test is a small counter p reaching 0 (p drifts up by 1/2 per step)
