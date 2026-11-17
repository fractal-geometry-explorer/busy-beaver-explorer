"""1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE: lean/Macro.lean `mstep` (with `norm`, `tailNext`, `evNext`),
lean/Reduce.lean `s0`, `mrun`, `halts_iff`, `halts_iff_four`.

State (X, a, mid, q, b, t) is 0^inf 1^X F>0 0 (10)^a [mid] (10)^b [tail] 0^inf with mid "none" (nothing), "zero" (a 0)
or "ev" (the block 1^(2q+2) 0; q is None unless mid = "ev"), and t None (no tail) or the tail block 1^(2t+3)."""
from maps._common import Stuck, bl

MACHINE = "1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE"
LEAN = ("holdouts/1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE/lean/Macro.lean: mstep, norm; "
        "lean/Reduce.lean: s0, mrun, halts_iff, halts_iff_four")
VARS = ("X", "a", "mid", "q", "b", "t")
START = (10, 0, "none", None, 0, 0)
HALT = "X = 4, mid none, no tail (a left block of four 1s with only units on its right)"
KIND = "doubling-pay"
BOUND = ("20,000,000 macro steps = 1.92e14 machine steps (macro_runs, native_decide, lean/MacroRun.lean); outer orbit "
         "N = 10, 27, ..., 17220, 8534636888060 (~6.5e25 steps) by py/outer.py with a heuristic (unproved) inner-epoch jump")


def _norm(s):
    X, a, m, q, b, t = s
    if X == 1:
        return (0, a + 1, m, q, b, t)
    return s


def _ev_next(q):
    return ("zero", None) if q == 0 else ("ev", q - 1)


def _tail_next(X, k, q):
    return (X, k + 3, "none", None, 0, None) if q == 0 else (X, k + 2, "none", None, 0, q - 1)


def step(s):
    X, a, m, q, b, t = s
    if m == "ev":
        if X >= 3:
            m2, q2 = _ev_next(q)
            return _norm((X - 2, a + 2, m2, q2, b, t)), "ev"
        if X == 0:
            m2, q2 = _ev_next(q)
            return (0, a + 2, m2, q2, b, t), "ev0"
        raise Stuck("mstep stuck (ev, X=%d)" % X)
    if m == "none" and t is not None:
        if X == 2:
            if a + b == 0:
                return (5, 0, "ev", t, 0, None), "tail2e"
            return (5, 0, "zero", None, a + b - 1, t), "tail2"
        if X >= 3:
            return _norm(_tail_next(X - 2, a + b, t)), "tail"
        if X == 0:
            return _tail_next(0, a + b, t), "tail0"
        raise Stuck("mstep stuck (tail, X=%d)" % X)
    if m == "none":
        if X == 2:
            if a + b == 0:
                raise Stuck("mstep stuck (units only, X=2, a+b=0)")
            return (5, 0, "zero", None, a + b - 1, None), "u2"
        if X >= 5:
            return _norm((X - 4, 0, "none", None, 0, a + b + 1)), "u5"
        if X == 4:
            return None, "H"
        if X == 0:
            return (2 * (a + b) + 4, 0, "none", None, 0, 0), "u0"
        if X == 3:
            return (2 * (a + b) + 6, 0, "none", None, 0, 0), "u3"
        raise Stuck("mstep stuck (units only, X=%d)" % X)
    if m != "zero":
        raise Stuck("bad mid %r" % (m,))
    if X >= 5:
        if b >= 1:
            return _norm((X - 4, 0, "ev", a + 2, b - 1, t)), "z5"
        if t is not None:
            return _norm((X - 4, 0, "ev", a + t + 3, 0, None)), "z5t"
        return _norm((X - 4, 0, "none", None, 0, a + 1)), "z5n"
    if X == 0 or X == 3:
        k = a + 1 if X == 3 else a
        if b >= 2:
            return (2 * k + 7, 0, "zero", None, b - 2, t), "zr"
        if b == 1 and t is not None:
            return (2 * k + 7, 0, "ev", t, 0, None), "zr1t"
        if b == 1:
            return (2 * k + 5, 0, "none", None, 0, 0), "zr1"
        if t is not None:
            return (2 * k + 2 * t + 7, 0, "none", None, 0, 0), "zr0t"
        return (2 * k + 4, 0, "none", None, 0, 0), "zr0"
    raise Stuck("mstep stuck (zero, X=%d)" % X)


def accel(s):
    """Runs of rounds against one block at once: k rounds against an even block (ev q, X >= 4 or X = 0) or the
    tail (X >= 4 or X = 0), stopping before the block shrinks to its last case or X reaches 2 (so `norm` never acts
    inside the batch).  Exactly k Lean steps."""
    X, a, m, q, b, t = s
    if m == "ev" and q >= 1:
        k = q if X == 0 else (min(q, (X - 4) // 2 + 1) if X >= 4 else 0)
        if k >= 2:
            return (X - 2 * k if X else 0, a + 2 * k, "ev", q - k, b, t), int(k), "ev"
    if m == "none" and t is not None and t >= 1:
        k = t if X == 0 else (min(t, (X - 4) // 2 + 1) if X >= 4 else 0)
        if k >= 2:
            return (X - 2 * k if X else 0, a + b + 2 * k, "none", None, 0, t - k), int(k), "tail"
    s2, lab = step(s)
    return s2, 1, lab


def _halting_N(N):
    """Distance from N to the nearest 2^(n+4) - 2n - 10 (outer configurations there halt: Outer.lean outer_halts)."""
    n = 0
    best = None
    while True:
        v = (1 << (n + 4)) - 2 * n - 10
        d = abs(N - v)
        best = d if best is None else min(best, d)
        if v > N:
            return best
        n += 1


def margin(s):
    """At an outer configuration 1^N F>0 0 1^3, the epoch halts iff N = 2^(n+4) - 2n - 10 (proved 'if'; 'only if'
    computed for N <= 3000)."""
    X, a, m, q, b, t = s
    if a == 0 and m == "none" and b == 0 and t == 0:
        return bl(_halting_N(X))
    return None
