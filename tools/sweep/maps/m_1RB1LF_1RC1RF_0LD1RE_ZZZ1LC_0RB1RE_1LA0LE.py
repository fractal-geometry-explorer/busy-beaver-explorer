"""1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE: lean/Map.lean `F`, `inner`, `orbit`, `halts_iff` (`halts_iff_T1`).

Nodes: ("vis", c, a, b) is the visit T(c, a, b) = 0^inf [1^2 0 (10)^c] 1^a 0 (10)^b B> 0^inf, c None (no bracket) or
an int; ("rs", None, None, n) is the fresh sweep Cs none 2 1 (n + 2).  `step` is F, with `inner` run literally
(one Lean recursion per round); `accel` is the same single F step with the runs of rounds of `inner` jumped."""
from maps._common import Stuck, bl

MACHINE = "1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE"
LEAN = "holdouts/1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE/lean/Map.lean: F, inner, orbit, halts_iff, halts_iff_T1"
VARS = ("node", "c", "a", "b")
START = ("vis", None, 2, 0)
HALT = "the visit T(none, 1, b) (vis with no bracket and a = 1)"
KIND = "doubling-mod"
BOUND = ("1e11 inner operations (5.0e10 right-end visits, ~1e31 machine steps, 35 odd pools, 18 without bracket), "
         "c/fast.c (status.json); 1e4 nodes by native_decide (orbit_native)")


def _inner(c, x, n, w, fast):
    """Lean `inner c x n w`: returns a node tuple, or raises Stuck where Lean gives none (not Good)."""
    while True:
        if fast:
            if c is None and x >= 3 and w >= 3:
                k = min((x - 3) // 2 + 1, w - 2)
                x, n, w = x - 2 * k, n + 2 * k, w - k
                continue
            if c is not None and x >= 4 and w >= 3:
                k = min((x - 4) // 2 + 1, w - 2)
                x, n, w = x - 2 * k, n + 2 * k, w - k
                continue
        if c is not None and x == 3:
            if w >= 2:
                c, x, n, w = None, 2, c + n + 3, w - 1
                continue
            if w == 1:
                c, x, n, w = None, 2, c + n + 2, 0
                continue
            return ("vis", None, 2, c + n + 3)
        if c is None and x >= 3:
            if w >= 2:
                x, n, w = x - 2, n + 2, w - 1
                continue
            if w == 1:
                x, n, w = x - 2, n + 1, 0
                continue
            return ("vis", None, x - 2, n + 2)
        if c is not None and x >= 4:
            if w >= 2:
                x, n, w = x - 2, n + 2, w - 1
                continue
            if w == 1:
                x, n, w = x - 2, n + 1, 0
                continue
            return ("vis", c, x - 2, n + 2)
        if x == 2:
            if w >= 4:
                x, n, w = 2 * n + 4, 1, w - 2
                continue
            if w == 3:
                x, n, w = 2 * n + 4, 1, 1
                continue
            if w == 2:
                x, n, w = 2 * n + 4, 0, 0
                continue
            if w == 1:
                return ("vis", c, 2 * n + 4, 0)
            return ("vis", c, 2 * n + 5, 0)
        if c is None and x == 1:
            if w >= 5:
                c, x, n, w = n + 1, 2, 1, w - 3
                continue
            if w == 4:
                c, x, n, w = n + 1, 2, 1, 1
                continue
            if w == 3:
                c, x, n, w = n + 1, 2, 0, 0
                continue
            if w == 2:
                return ("vis", n + 1, 2, 0)
            if w == 1:
                if n >= 1:
                    return ("rs", None, None, n - 1)
                raise Stuck("inner none 1 0 1 (not Good)")
            return ("vis", None, 2 * n + 7, 0)
        raise Stuck("inner %r %r %r %r is none (not Good)" % (c, x, n, w))


def _F(s, fast):
    t, c, a, b = s
    if t == "rs":
        return _inner(None, 2, 1, b + 2, fast), "rs"
    if a >= 2:
        lab = "even" if a % 2 == 0 else "odd"
        if b >= 1:
            return _inner(c, a, 1, b, fast), lab
        return _inner(c, a, 0, 0, fast), lab
    if a == 1 and c is None:
        return None, "H"
    raise Stuck("visit outside Good: c=%r a=%r" % (c, a))


def step(s):
    return _F(s, False)


def accel(s):
    s2, lab = _F(s, True)
    return s2, 1, lab


def _targets_near(A):
    k = 0
    while (1 << (k + 2)) - 2 * k - 3 < A:
        k += 1
    hi = (1 << (k + 2)) - 2 * k - 3
    lo = (1 << (k + 1)) - 2 * k - 1 if k > 0 else hi
    return lo, hi


def margin(s):
    """At an odd pool without bracket, T(none, A, 0): it halts iff A = 2^(k+2) - 2k - 3 (README, trusted)."""
    t, c, a, b = s
    if t == "vis" and c is None and b == 0 and a % 2 == 1:
        lo, hi = _targets_near(a)
        return bl(min(abs(a - lo), abs(hi - a)))
    return None
