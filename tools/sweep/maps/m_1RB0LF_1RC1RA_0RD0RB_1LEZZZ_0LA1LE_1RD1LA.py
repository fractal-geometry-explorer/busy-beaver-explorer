"""1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA: lean/Map.lean `F`, `overflow`, `orbitFrom`, `halts_iff`, `halts_iff_H`.

Nodes (tag, A, B): ("s", x, None) = S(x+6) = 0^inf 1^(x+6) 1110 B> 0^inf; ("p", a, m) = P(a+3, m) =
0^inf F> 0 0 (10)^(a+3) 1^m 0 1 0^inf; ("q", u, c) = Q(u+1, 2c+1); ("t", u, v) = T(u, v+1).
busycoq PR 60 (external Rocq proof, not compiled here) claims the orbit halts at its A(a, b) with
a = 28*2^85 - 6, i.e. our p((a-6)/2, 0), after ~1e25 returns to S: far beyond a plain run."""
from maps._common import bl

MACHINE = "1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA"
LEAN = ("holdouts/1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA/lean/Map.lean: F, overflow, orbitFrom, halts_iff, "
        "halts_iff_H")
VARS = ("node", "A", "B")
START = ("s", 7, None)
HALT = "a node p(a, 0): a doubling round with no ones"
KIND = "doubling-pay"
BOUND = ("1e8 returns to S (4.6e9 nodes, X up to 1.52e10), c/orbit.c (status.json); 1e7 nodes by native_decide "
         "(orbit_native). busycoq PR 60 claims a halt at a = 28*2^85 - 6 after ~1e25 returns (not compiled here)")


def _overflow(pp, z, r):
    if pp == 0:
        return ("s", 4 * z + 1, None) if r == 0 else ("s", 4 * z + 7, None)
    if pp % 2 == 1:
        return ("p", 2 * (pp // 2) + 3, 4 * z + 2) if r == 0 else ("t", pp // 2, 2 * z + 2)
    return ("q", pp // 2 - 1, 2 * z + 3) if r == 0 else ("s", 4 * (pp // 2 - 1) + 4 * z + 11, None)


def step(s):
    t, A, B = s
    if t == "s":
        return ("p", 0, A + 6), "s"
    if t == "p":
        a, m = A, B
        if 2 * a + 9 <= m:
            return ("p", 2 * a + 6, m - (2 * a + 9)), "dbl"
        if m == 0:
            return None, "H"
        if m == 1:
            return (("s", 2 * a + 7, None) if a % 2 == 0 else ("q", a // 2 + 1, 1)), "p1"
        if m == 2:
            return (("t", a // 2 + 1, 0) if a % 2 == 0 else ("s", 2 * a + 9, None)), "p2"
        return _overflow(a + 2 - (m - 3) // 2, (m - 3) // 2, (m - 3) % 2), "over"
    if t == "q":
        u, c = A, B
        if 4 <= c:
            return ("p", 2 * u + 8, 2 * c - 8), "q"
        if c == 0:
            return ("s", 4 * u + 11, None), "q0"
        if c == 1:
            return ("q", 0, 2 * u + 5), "q1"
        if c == 2:
            return ("p", 3, 4 * u + 10), "q2"
        return ("s", 4 * u + 13, None), "q3"
    return ("q", 0, 2 * A + B + 5), "t"


def margin(s):
    """At the last round of a doubling chain (p a m, m < 2a + 9) it halts iff m = 0."""
    t, A, B = s
    if t == "p" and B < 2 * A + 9:
        return bl(B)
    return None
