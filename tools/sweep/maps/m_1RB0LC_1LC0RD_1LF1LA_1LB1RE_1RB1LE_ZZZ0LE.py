"""1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE: lean/Map.lean `next`, `land`, `orbit`, `halts_iff`.

X a b c k = E> 0 1^a 0 1 0 1^b (01)^c (11101)^k 1.  next (first matching case, as in Lean):
  c = 0: stuck
  a >= 4: (a-2, b+3, c, k);  a = 3: (1, b+3, c, k);  a = 2: (0, b+3, c, k)           (stretch)
  c >= 2: a = 1, b >= 3: land(b, c-2, k);  a = 0, b >= 3: land(b-1, c-2, k);  a = 1, b = 1: (2, 4, c-1, k);
          a = 1, b in {0, 2} or a = 0, b in {0, 1, 2}: stuck
  c = 1:  a = 1: b odd >= 3: (2, 1, b/2, k+1); b even >= 2: halt; b in {0, 1}: stuck
          a = 0: b even >= 10: (5, 4, b/2-3, k+1); b odd >= 5: (1, 1, b/2, k+1); smaller b: stuck
  land(B, c, k) = (B, 7, c, k) if c >= 1; (B, 10, 1, k-1) if c = 0, k >= 1; stuck if c = k = 0.
Halts from blank iff the orbit of (15, 7, 7, 1) reaches halt.
"""
from maps._common import Stuck

MACHINE = "1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE"
LEAN = "holdouts/1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE/lean/Map.lean: next, land, orbit, halts_iff"
VARS = ("a", "b", "c", "k")
START = (15, 7, 7, 1)
HALT = "a = 1, c = 1, b even (the budget c of 01 pairs runs out with a = 1 on an even b)"
KIND = "parity-3/2"
BOUND = ("4 budget ends survived (phases 4, 34, 683,741, 683,742; status.json, py/map.py orbit); the budget is now "
         "a 399,947-bit c, about 2^399,946 phases, so no run can finish it; machine check 4e8 steps (py/map.py check)")


def land(B, c, k):
    if c >= 1:
        return (B, 7, c, k)
    if k >= 1:
        return (B, 10, 1, k - 1)
    raise Stuck("land with c = k = 0")


def step(s):
    a, b, c, k = s
    if c == 0:
        raise Stuck("c = 0")
    if a >= 4:
        return (a - 2, b + 3, c, k), "s"
    if a == 3:
        return (1, b + 3, c, k), "s"
    if a == 2:
        return (0, b + 3, c, k), "s"
    if c >= 2:
        if a == 1 and b >= 3:
            return land(b, c - 2, k), "1"
        if a == 0 and b >= 3:
            return land(b - 1, c - 2, k), "0"
        if a == 1 and b == 1:
            return (2, 4, c - 1, k), "11"
        raise Stuck("c >= 2 with (a, b) in {(1,0), (1,2), (0,0), (0,1), (0,2)}")
    if a == 1:
        if b % 2 == 1:
            if b >= 3:
                return (2, 1, b // 2, k + 1), "refill1"
            raise Stuck("a = 1, b = 1, c = 1")
        if b >= 2:
            return None, "H"
        raise Stuck("a = 1, b = 0, c = 1")
    if b % 2 == 0:
        if b >= 10:
            return (5, 4, b // 2 - 3, k + 1), "refill0e"
        raise Stuck("a = 0, b even < 10, c = 1")
    if b >= 5:
        return (1, 1, b // 2, k + 1), "refill0o"
    raise Stuck("a = 0, b odd < 5, c = 1")


def accel(s):
    """A whole stretch at once: from a >= 2 (c >= 1), a//2 steps a -> a-2, b -> b+3, ending at a = a mod 2."""
    a, b, c, k = s
    if a >= 2 and c >= 1:
        r = a // 2
        return (a - 2 * r, b + 3 * r, c, k), r, "s"
    s2, lab = step(s)
    return s2, 1, lab


# no margin: the halting test is a budget counter c (now ~2^399947) running out, then parities of a and b
