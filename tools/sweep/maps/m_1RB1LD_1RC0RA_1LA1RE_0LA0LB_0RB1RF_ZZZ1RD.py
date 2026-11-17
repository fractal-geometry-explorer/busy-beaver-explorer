"""1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD: lean/Model.lean `nxt`, `orbit`, `halts_iff`.

Lean's shifted counts: X(a,b,c) is 0^inf 1^a 0 (10)^b 1 D> 0 1^(c+1) 0^inf, Y(a,b,c) is 0^inf 1^(a+3) 00 (10)^b 1 D> 0
1^(c+1) 0^inf, Z(a,c) is 0^inf 1^(a+3) 0 D> 0 1^(c+1) 0^inf.  The state is (tag, a, b, c); Z carries b = None.
(c/xyz.c and py/orbit.py use the real counts: real c = c+1, real Y/Z a = a+3.)"""
from maps._common import Stuck, bl

MACHINE = "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD"
LEAN = "holdouts/1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD/lean/Model.lean: nxt, orbit, halts_iff"
VARS = ("tag", "a", "b", "c")
START = ("X", 2, 0, 2)
HALT = "Z(a, 1) in Lean's shifted counts (real Z(a+3, 2)); reached from a Y run iff c - b = 2 (real c - b = 3)"
KIND = "frame"
BOUND = "9,500 rounds (2.8e8 bulk steps, N 11,902 bits, ~1e7170 machine steps), c/xyz.c (halt-hunt/maps NOTES.md)"


def step(s):
    t, a, b, c = s
    if t == "X":
        if c >= 1:
            if a >= 4:
                return ("X", a - 3, b + 2, c - 1), "X4"
            if a == 3:
                return ("X", 1, b + 1, c - 1), "X3"
            if a == 2:
                return ("X", 2, b + 2, c - 1), "X2"
            if a == 1:
                return ("Y", 0, b, c - 1), "X1"
            if b == 0:
                return ("Z", 0, None, c - 1), "X00"
            return ("Y", 0, b - 1, c - 1), "X0"
        if a >= 5:
            return ("X", a - 5, 0, 2 * b + 8), "Xe5"
        if a == 4:
            return ("X", 4, 0, 2 * b + 6), "Xe4"
        if a == 3:
            return ("X", 4, 0, 2 * b + 4), "Xe3"
        if a == 2:
            return ("X", 0, 0, 2 * b + 8), "Xe2"
        if a == 1:
            return ("X", 1, 0, 2 * b + 4), "Xe1"
        if b == 0:
            return ("X", 1, 0, 2), "Xe00"
        return ("X", 1, 0, 2 * (b - 1) + 4), "Xe0"
    if t == "Y":
        if b >= 1 and c >= 1:
            return ("Y", a + 3, b - 1, c - 1), "Y"
        if b == 0 and c >= 1:
            return ("Z", a + 3, None, c - 1), "Y0"
        return ("X", a + 3, 1, 2 * b + 2), "Ye"
    if t == "Z":
        if c >= 5:
            return ("X", a + 7, 0, c - 5), "Z"
        if c == 0:
            return ("X", a + 3, 1, 0), "Z0"
        if c == 1:
            return None, "H"
        if c == 2:
            return ("X", a + 3, 0, 4), "Z2"
        if c == 3:
            return ("X", a + 5, 0, 2), "Z3"
        return ("X", a + 5, 0, 4), "Z4"
    raise Stuck("bad tag %r" % (t,))


def accel(s):
    """The bulk runs of Model.lean's rules X(a+4,b,c+1)->X(a+1,b+2,c), X(2,b,c+1)->X(2,b+2,c),
    Y(a,b+1,c+1)->Y(a+3,b,c), taken k times at once."""
    t, a, b, c = s
    if t == "X" and c >= 1 and a >= 4:
        k = min((a - 1) // 3, c)
        return ("X", a - 3 * k, b + 2 * k, c - k), int(k), "X4"
    if t == "X" and c >= 1 and a == 2:
        return ("X", 2, b + 2 * c, 0), int(c), "X2"
    if t == "Y" and b >= 1 and c >= 1:
        k = min(b, c)
        return ("Y", a + 3 * k, b - k, c - k), int(k), "Y"
    s2, lab = step(s)
    return s2, 1, lab


def margin(s):
    """At a Y state whose run empties b (c > b): halting needs c - b = 2."""
    t, a, b, c = s
    if t == "Y" and b >= 1 and c > b:
        return bl(c - b - 2)
    return None
