"""1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA: lean/Map.lean `next`, `orbit`, `halts_iff`.

X(a, b, c) = D> 0 0 1^a 0 1^b (01)^c.  next:
  a >= 4: (a-2, b+3, c);  a = 3: (1, b+3, c)                                   (stretch: a -> a-2, b -> b+3)
  a = 1: b >= 3, c >= 1: (b+1, 4, c-1);  b = 1, c >= 1: (2, 4, c-1);  b >= 3, c = 0: (b+1, 3, 0)
  a = 2: c >= 3: (b+6, 4, c-3);  c = 2: (b+6, 3, 0);  c = 1: (b+5, 3, 0);
         c = 0: (1, 1, b/2+1) if b even, halt if b odd
  anything else (a = 0; a = 1 with b in {0, 2} or (b, c) = (1, 0)): stuck (never on the orbit, Lean `Good`).
Halts from blank iff the orbit of (1, 1, 4) reaches halt.
"""
from maps._common import Stuck

MACHINE = "1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA"
LEAN = "holdouts/1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA/lean/Map.lean: next, orbit, halts_iff"
VARS = ("a", "b", "c")
START = (1, 1, 4)
HALT = "a = 2, c = 0, b odd (the budget c of 01 pairs runs out on an odd b)"
KIND = "parity-3/2"
BOUND = ("4 budget refills survived (cycles 3, 8, 25, 2,549; status.json, py/map.py orbit); the fifth budget is a "
         "1,479-bit c, about 2^1478 rounds, so no run can finish it; machine check 4e8 steps (py/map.py check)")


def step(s):
    a, b, c = s
    if a >= 4:
        return (a - 2, b + 3, c), "s"
    if a == 3:
        return (1, b + 3, c), "s"
    if a == 1:
        if b >= 3 and c >= 1:
            return (b + 1, 4, c - 1), "1"
        if b == 1 and c >= 1:
            return (2, 4, c - 1), "1"
        if b >= 3 and c == 0:
            return (b + 1, 3, 0), "1z"
        raise Stuck("a = 1 with b in {0, 2} or (b, c) = (1, 0): Lean next = stuck")
    if a == 2:
        if c >= 3:
            return (b + 6, 4, c - 3), "2"
        if c == 2:
            return (b + 6, 3, 0), "2"
        if c == 1:
            return (b + 5, 3, 0), "2"
        if b % 2 == 0:
            return (1, 1, b // 2 + 1), "refill"
        return None, "H"
    raise Stuck("a = 0: Lean next = stuck")


def accel(s):
    """A whole stretch at once: from a >= 3, (a-1)//2 steps a -> a-2, b -> b+3, ending at a = 1 (a odd) or 2."""
    a, b, c = s
    if a >= 3:
        k = (a - 1) // 2
        return (a - 2 * k, b + 3 * k, c), k, "s"
    s2, lab = step(s)
    return s2, 1, lab


# no margin: the halting test is a budget counter c (now ~2^1479) running out, then a parity coin on b
