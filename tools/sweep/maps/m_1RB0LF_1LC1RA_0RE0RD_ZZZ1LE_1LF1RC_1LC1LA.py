"""1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA: lean/Reset.lean `F`, `chainF`, `sweepv`, `orbitFrom`, `halts_iff_44`.

States: ("z", t) is 1^t A>; ("rs", d) is C> 0 1^(2d+4) (Rc 0 (2d+3)), a restart of the doubling rounds.
sweepv(x, y) = 2y+1+3x (x even), 2y+3x+3 (x odd).
chainF(f, a, d) (fuel f): f = 0 or d = 0 -> halt; d < a -> z(sweepv(a-1-d, 2d+2)); d = a -> z(4a+4);
  d = a+1 -> rs(2a+3); else chainF(f-1, 2a+3, d-a-2).
F z(t): t = 3 halt; t = 0,1 -> z19; 2 -> z6; 4 -> z7; 5 -> z20; t even -> z(sweepv(t/2-2, 3));
  t odd -> chainF((t+3)/2+1, 1, (t+3)/2).   F rs(d) = chainF(d+1, 1, d).
Halts from blank iff the orbit of z(44) reaches none.  Closed form (F_z_none, F_rs_none): z(t) halts iff
t + 2s + 11 = 2^(s+3) (t = 3, 17, 47, 109, 235, ...); rs(d) halts iff d + s + 4 = 2^(s+2).
The inner chainF loop is part of F (O(log d) rounds), so `step` is one application of F.
"""
from maps._common import bl

MACHINE = "1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA"
LEAN = "holdouts/1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA/lean/Reset.lean: F, chainF, orbitFrom, halts_iff_44 (F_z_none, F_rs_none)"
VARS = ("tag", "t (z) or d (rs)")
START = ("z", 44)
HALT = "z(t) with t + 2s + 11 = 2^(s+3), or rs(d) with d + s + 4 = 2^(s+2), for some s (chainF reaches d = 0)"
KIND = "reset-table"
BOUND = "10,000 resets (Lean native_decide, lean/Orbit.lean orbit_10000; t ~3,900 bits); 300 resets kernel (orbit_300)"


def sweepv(x, y):
    return 2 * y + 1 + 3 * x if x % 2 == 0 else 2 * y + 3 * x + 3


def chainF(f, a, d):
    while True:
        if f == 0 or d == 0:
            return None
        if d < a:
            return ("z", sweepv(a - 1 - d, 2 * d + 2))
        if d == a:
            return ("z", 4 * a + 4)
        if d == a + 1:
            return ("rs", 2 * a + 3)
        f, a, d = f - 1, 2 * a + 3, d - a - 2


SMALL = {0: ("z", 19), 1: ("z", 19), 2: ("z", 6), 4: ("z", 7), 5: ("z", 20)}


def step(s):
    kind, v = s
    if kind == "rs":
        n = chainF(v + 1, 1, v)
        return n, ("rs" if n is None else "rs>" + n[0])
    if v == 3:
        return None, "z3"
    if v in SMALL:
        return SMALL[v], "small"
    if v % 2 == 0:
        return ("z", sweepv(v // 2 - 2, 3)), "even"
    h = (v + 3) // 2
    n = chainF(h + 1, 1, h)
    return n, ("odd" if n is None else "odd>" + n[0])


def chain_fast(f, a, d):
    """chainF in closed form.  After i rounds a_i + 3 = 2^i (a+3) and d_i = d + i - (2^i - 1)(a+3); the loop exits
    at the first i with d_i <= a_i + 1, i.e. d + i + (a+3) + 2 <= 2^(i+1) (a+3) (monotone in i), unless the fuel
    runs out first (f - i = 0)."""
    if f == 0 or d == 0:
        return None
    A = a + 3

    def ok(i):
        return d + i + A + 2 <= (A << (i + 1))

    i = max(0, bl(d) - bl(A) - 2)
    while i > 0 and ok(i - 1):
        i -= 1
    while not ok(i):
        i += 1
    if i >= f:
        return None
    ai = (A << i) - 3
    di = d + i - ((1 << i) - 1) * A
    return chainF(f - i, ai, di)  # exits at its first test


def accel(s):
    """Exactly one application of F (n = 1), with the chainF rounds done in closed form."""
    kind, v = s
    if kind == "rs":
        n = chain_fast(v + 1, 1, v)
        return n, 1, ("rs" if n is None else "rs>" + n[0])
    if kind == "z" and v % 2 == 1 and v not in SMALL and v != 3:
        h = (v + 3) // 2
        n = chain_fast(h + 1, 1, h)
        return n, 1, ("odd" if n is None else "odd>" + n[0])
    s2, lab = step(s)
    return s2, 1, lab


def margin(s):
    # distance to the nearest halting value of the same kind: t_s = 2^(s+3) - 2s - 11, d_s = 2^(s+2) - s - 4
    kind, v = s
    L = bl(v)
    best = None
    for e in range(max(L - 2, 2), L + 3):  # e = s+3 (z) or s+2 (rs), the power of two near v
        sv = e - 3 if kind == "z" else e - 2
        if sv < 0:
            continue
        hv = (1 << e) - (2 * sv + 11 if kind == "z" else sv + 4)
        g = bl(v - hv)
        best = g if best is None else min(best, g)
    return best
