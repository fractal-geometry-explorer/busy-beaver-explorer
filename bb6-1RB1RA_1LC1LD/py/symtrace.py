"""Symbolic run of the block machine (astep of py/macro.py) on affine expressions: `pre` by residue classes.

Numbers are affine in nonnegative integer variables.  When a branch depends on a residue or a size the
variable is split (v -> m v' + k, or v -> 0 / v' + 1) and both cases are followed.  Words are a list of
items: ('w', e) one word 0 1^e, ('r', e) e words 0 1 1.  The loop over two words 2 at A (tail_two) is
taken in one go.  The trailing supply is the run ('r', J) with J a large variable (j of the pass).

usage:
  python3 py/symtrace.py one              the classes of pre([x]), x = 18r + c + 36, checked against pre
  python3 py/symtrace.py two [DEPTH]      the classes of pre([z, y]) (blocks y, z before the last), checked, summary
"""
import os
import sys
from collections import Counter
from fractions import Fraction


class E:
    __slots__ = ("c", "k")

    def __init__(self, k=0, c=None):
        self.k = k
        self.c = {v: a for v, a in (c or {}).items() if a}

    @staticmethod
    def v(name, a=1):
        return E(0, {name: a})

    def __add__(self, o):
        o = o if isinstance(o, E) else E(o)
        c = dict(self.c)
        for v, a in o.c.items():
            c[v] = c.get(v, 0) + a
        return E(self.k + o.k, c)

    __radd__ = __add__

    def __sub__(self, o):
        o = o if isinstance(o, E) else E(o)
        return self + E(-o.k, {v: -a for v, a in o.c.items()})

    def __mul__(self, m):
        return E(self.k * m, {v: a * m for v, a in self.c.items()})

    __rmul__ = __mul__

    def div(self, m):
        assert self.k % m == 0 and all(a % m == 0 for a in self.c.values()), (self, m)
        return E(self.k // m, {v: a // m for v, a in self.c.items()})

    def const(self):
        return not self.c

    def subst(self, var, e):
        if var not in self.c:
            return self
        a = self.c[var]
        rest = E(self.k, {v: b for v, b in self.c.items() if v != var})
        return rest + e * a

    def ev(self, env):
        return self.k + sum(a * env[v] for v, a in self.c.items())

    def __repr__(self):
        parts = [f"{a}{v}" if a != 1 else v for v, a in sorted(self.c.items())]
        if self.k or not parts:
            parts.append(str(self.k))
        return "+".join(parts).replace("+-", "-")

    def key(self):
        return (self.k, tuple(sorted(self.c.items())))


class Split(Exception):
    def __init__(self, var, cases):
        self.var, self.cases = var, cases


def mod(e, m):
    """e mod m, or Split on a variable whose coefficient is not divisible by m."""
    for v, a in sorted(e.c.items()):
        if a % m:
            raise Split(v, [E.v(v, m) + k for k in range(m)])
    return e.k % m


def eq(e, n):
    """e == n for a small constant n, assuming variables >= 0 (all coefficients are positive here)."""
    if e.const():
        return e.k == n
    if any(a < 0 for a in e.c.values()):
        raise ValueError(f"negative coefficient in {e}")
    if e.k > n:
        return False
    v = sorted(e.c)[0]
    raise Split(v, [E(0), E.v(v) + 1])


def ge(e, n):
    if e.const():
        return e.k >= n
    if e.k >= n:
        return True
    v = sorted(e.c)[0]
    raise Split(v, [E(0), E.v(v) + 1])


def subst_all(obj, var, e):
    if isinstance(obj, E):
        return obj.subst(var, e)
    if isinstance(obj, tuple):
        return tuple(subst_all(o, var, e) for o in obj)
    if isinstance(obj, list):
        return [subst_all(o, var, e) for o in obj]
    return obj


# words: list of ('w', E) and ('r', E)
def norm(W):
    out = []
    for t, e in W:
        if t == "r" and e.const() and e.k == 0:
            continue
        if t == "w" and e.const() and e.k == 2:
            t, e = "r", E(1)
        if out and t == "r" and out[-1][0] == "r":
            out[-1] = ("r", out[-1][1] + e)
        else:
            out.append((t, e))
    return out


def pop(W):
    """The first word and the rest; None if empty."""
    if not W:
        return None
    t, e = W[0]
    if t == "w":
        return e, W[1:]
    if not ge(e, 1):
        return pop(W[1:])
    return E(2), norm([("r", e - 1)] + W[1:])


def tw(a, j, k):
    """tw a j k: words a, then j words 2, the last k longer."""
    if j.const() and j.k == 0:
        return [("w", a + k)]
    if k.const() and k.k == 0:
        return norm([("w", a), ("r", j)])
    return norm([("w", a), ("r", j - 1), ("w", k + 2)])


def pad(L, n=4):
    return L + [E(0)] * max(0, n - len(L))


def step(q, h, L, W, log):
    """One astep; returns (q, h, L, W) or a tuple ('pass', ...)/('halt',)/None."""
    L = pad(L)
    a, M = L[0], L[1:]
    pw = pop(W)
    k, W1 = pw if pw else (None, None)
    if q == "A" and not eq(h, 0):
        log.append(("a_run", h))
        return ("A", E(0), [a + h] + M, W)
    if q == "A":
        if k is None:
            return ("pass", M, a - 1)
        if eq(k, 0):
            return None
        log.append(("a_tok", k))
        return ("B", E(0), [E(1)] + [E(0)] * (k.k - 1 if k.const() else None) + L, W1) if k.const() else ("BIGZ", k)
    if q in "DE" and eq(h, 0 if q == "D" else 1):
        if k is None:
            return ("halt",)
        a2 = a + (2 if q == "D" else 3)
        if eq(k, 1):
            log.append((q.lower() + "_one",))
            return ("D", E(0), [a2] + M, W1)
        if eq(k, 2):
            log.append((q.lower() + "_two",))
            return ("F", E(0), [E(0), a2] + M, W1)
        if not k.const():
            return ("BIGZ", k)
        log.append((q.lower() + "_tok", k))
        return ("B", E(0), [E(1)] + [E(0)] * (k.k - 3) + [a2] + M, W1)
    if q == "F" and eq(h, 0):
        if k is None:
            return ("pass", M, a)
        log.append(("f_tok", k))
        return ("A", E(0), [a + k + 1] + M, W1)
    if q == "C" and eq(h, 0) and k is not None:
        if not eq(a, 0) and eq(k, 1) and pop(W1) is not None:
            k2, W2 = pop(W1)
            log.append(("c_move", a))
            return ("C", E(0), [E(0)] + M, norm([("w", E(1)), ("w", k2 + a)] + W2))
        if not eq(a, 0):
            if not k.const():
                return ("BIGZ", k)
            log.append(("c_tok", k))
            return ("B", E(0), [E(1)] + [E(0)] * k.k + [a - 1] + M, W1)
        d, M2 = M[0], M[1:]
        if eq(k, 1):
            log.append(("c_one",))
            return ("F", E(0), [E(0), d + 2] + M2, W1)
        if eq(k, 0):
            return None
        if not k.const():
            return ("BIGZ", k)
        log.append(("c_more", k))
        return ("B", E(0), [E(1)] + [E(0)] * (k.k - 2) + [d + 2] + M2, W1)
    if q == "B" and eq(h, 0):
        if k is None:
            if eq(L[0], 1) and eq(L[1], 0):
                return ("pass", [L[3] + 2] + L[4:], L[2] + 1)
            return None
        n, c, d, M = L[0], L[1], L[2], L[3:]
        r = mod(n, 3)
        if r == 1:
            log.append(("b_one", n))
            return ("B", E(0), [c, d] + M, norm([("w", E(0))] + tw(E(1), (n - 1).div(3), k) + W1))
        if eq(n, 2):
            log.append(("b_two0",))
            return ("E", k + 1, [c + 3, d] + M, W1)
        if r == 2:
            log.append(("b_two", n))
            return ("E", E(1), [c + 3, d] + M, norm(tw(E(2), (n - 5).div(3), k) + W1))
        if eq(k, 0):
            log.append(("b_zero", n))
            return ("C", E(0), [c, d] + M, norm(tw(E(1), n.div(3), E(0)) + W1))
        if eq(n, 0):
            log.append(("b_empty",))
            return ("C", E(0), [c, d] + M, norm([("w", k + 1)] + W1))
        if eq(n, 3):
            log.append(("b_three0",))
            return ("A", k + 1, [c + 2, d + 2] + M, W1)
        log.append(("b_three", n))
        return ("A", E(1), [c + 2, d + 2] + M, norm(tw(E(2), (n - 6).div(3), k) + W1))
    return None


def accel(q, h, L, W, log):
    """tail_iter: A, no ones under the head, before a run of at least 2 words 2: take its even part at once."""
    if q != "A" or not (h.const() and h.k == 0) or not W or W[0][0] != "r":
        return None
    n = W[0][1]
    if not ge(n, 2):
        return None
    par = mod(n, 2)
    i = (n - par).div(2)
    L = pad(L, 2)
    log.append(("tail_iter", i))
    return ("A", E(0), [L[0] + i * 4, L[1] + i * 2] + L[2:], norm(([("r", E(1))] if par else []) + W[1:]))


def run(cfg, J="J", fuel=10000):
    """Run from cfg (q, h, L, W) with W ending in the supply run of J words; returns the end and the log, or raises
    Split.  Stops at A before nothing but the supply (pre's stop) and reports the remaining supply."""
    q, h, L, W = cfg
    log = []
    for _ in range(fuel):
        if q == "A" and h.const() and h.k == 0 and len(W) == 1 and W[0][0] == "r" and J in W[0][1].c:
            return ("stop", L, W[0][1]), log
        r = accel(q, h, L, W, log)
        if r is None:
            r = step(q, h, L, W, log)
        if r is None or r[0] in ("pass", "halt", "BIGZ"):
            return r, log
        q, h, L, W = r
    return ("fuel",), log


def explore(cfg, vars_, depth=8, J="J"):
    """All classes: list of (substitution dict, result, log).  Splits variables as needed, up to depth splits."""
    out = []
    stack = [({}, cfg, 0)]
    while stack:
        sub, c, dep = stack.pop()
        try:
            res, log = run(c, J)
            out.append((sub, res, log))
        except Split as s:
            if dep >= depth:
                out.append((sub, ("deep", s.var), []))
                continue
            for e in s.cases:
                nsub = {v: x.subst(s.var, e) for v, x in sub.items()}
                if s.var not in nsub:
                    nsub[s.var] = e
                stack.append((nsub, subst_all(c, s.var, e), dep + 1))
    return out


def _strip(L):
    L = list(L)
    while L and L[-1] == 0:
        L.pop()
    return L


def classes(nblocks, depth=6, base=36):
    """The classes of pre for nblocks blocks before the last, each block 18 v + c + base (nearest first, variables
    r, s, t): a list of (residues, substitution, result, log)."""
    names = "rst"[:nblocks]
    out = []
    J = E.v("J") + 20

    def rec(cs):
        if len(cs) == nblocks:
            L = [E.v(names[i], 18) + (cs[i] + base) for i in range(nblocks)]
            cfg = ("B", E(0), L, [("w", E(0)), ("w", E(1)), ("r", J)])
            for sub, res, log in explore(cfg, list(names), depth=depth):
                out.append((tuple(cs), sub, res, log))
            return
        for c in range(18):
            rec(cs + [c])
    rec([])
    return out


def check(cls, base=36, samples=((0, 0, 0), (1, 2, 1), (3, 1, 2))):
    """Every class that stops, against pre_fast at a few points: the number of mismatches."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from twoblock import run as pre_fast
    bad = 0
    for cs, sub, res, log in cls:
        if not res or res[0] != "stop":
            continue
        names = "rst"[:len(cs)]
        for pt in samples:
            env = dict(zip("rst", pt))
            env["J"] = 7
            vals = [(sub[v].ev(env) if v in sub else env[v]) for v in names]
            Jv = (sub["J"].ev(env) if "J" in sub else env["J"]) + 20
            L = [e.ev(env) for e in res[1]]
            P = pre_fast([18 * vals[i] + cs[i] + base for i in range(len(cs))])
            if _strip(L) != _strip(P[0]) or res[2].ev(env) != Jv - P[2] or P[1] != 0:
                bad += 1
    return bad


def summary(cls):
    kinds = Counter(res[0] if res else None for cs, sub, res, log in cls)
    deep = sorted({cs for cs, sub, res, log in cls if res and res[0] == "deep"})
    per = Counter(Counter(cs for cs, sub, res, log in cls if res and res[0] == "stop").values())
    return kinds, deep, per


if __name__ == "__main__":
    a = sys.argv[1:]
    if not a:
        print(__doc__)
    else:
        n = {"one": 1, "two": 2}[a[0]]
        cls = classes(n, depth=int(a[1]) if len(a) > 1 else 6)
        kinds, deep, per = summary(cls)
        print("classes by outcome:", dict(kinds))
        print("residue tuples with a deeper 3-adic branch:", deep)
        print("residue tuples by number of exact classes:", dict(sorted(per.items())))
        print("mismatches against pre:", check(cls))
