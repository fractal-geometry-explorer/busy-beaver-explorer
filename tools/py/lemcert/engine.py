"""Symbolic configurations with linear counts and an "anything" end, and the moves on them.

A configuration is (q, f, L, R): state q, the head facing side f ('L' or 'R') and reading that side's first cell.
A side is (items, term): items nearest first, each (w, e) = the word w (outward order) repeated e times, e a linear
form in natural-number variables; term is 'B' (blank for ever) or 'A' (any stream at all).

A move maps one configuration to a list of successor configurations whose union covers every concrete
configuration the machine reaches from it (case splits on variables or on the cells of an 'A' end).  A halt
raises Halt.
"""
from fractions import Fraction


class Halt(Exception):
    pass


class Stuck(Exception):
    pass


class ExitS(Exception):
    """The head reads into the caller's part of the tape."""
    pass


# ------------------------------------------------------------------ linear forms
# A Lin is a tuple (c, ((v, a), ...)) with the pairs sorted by variable, a > 0.

def K(c):
    return (c, ())


def V(v, c=0):
    return (c, ((v, 1),))


def ladd(x, y):
    d = dict(x[1])
    for v, a in y[1]:
        d[v] = d.get(v, 0) + a
    return (x[0] + y[0], tuple(sorted((v, a) for v, a in d.items() if a)))


def lsub_const(x, k):
    return (x[0] - k, x[1])


def lmul(x, k):
    if k == 0:
        return K(0)
    return (x[0] * k, tuple((v, a * k) for v, a in x[1]))


def ldiff(x, y):
    """x - y if it is a constant, else None."""
    if x[1] != y[1]:
        return None
    return x[0] - y[0]


def lsubst(x, v, y):
    """Substitute variable v := y (a Lin) in x."""
    a = dict(x[1]).get(v, 0)
    if not a:
        return x
    rest = (x[0], tuple(p for p in x[1] if p[0] != v))
    return ladd(rest, lmul(y, a))


def isconst(x):
    return not x[1]


def lstr(x):
    s = [f"{a}{v}" if a != 1 else f"{v}" for v, a in x[1]]
    if x[0] or not s:
        s.append(str(x[0]))
    return "+".join(s)


def lvars(x):
    return {v for v, _ in x[1]}


# ------------------------------------------------------------------ machines

def parse(m):
    T = {}
    for qi, row in enumerate(m.split("_")):
        for b in (0, 1):
            t = row[3 * b:3 * b + 3]
            T[(qi, b)] = None if t[0] == "-" else (int(t[0]), t[1], ord(t[2]) - 65)
    return T


# ------------------------------------------------------------------ configurations

def wstr(w):
    return "".join(map(str, w))


def side_str(s, left):
    items, term = s
    parts = []
    for w, e in items:
        if e == K(1):
            parts.append(wstr(w))
        else:
            parts.append(f"({wstr(w)})^{lstr(e)}")
    t = {"B": "0^inf", "A": "ANY", "S": "$"}[term]
    if left:
        return " ".join([t] + [p[::-1] if not p.startswith("(") else "(" + p[1:p.index(")")][::-1] + p[p.index(")"):] for p in reversed(parts)])
    return " ".join(parts + [t])


def cfg_str(c):
    q, f, L, R = c
    h = f"{'ABCDEF'[q]}>" if f == 'R' else f"<{'ABCDEF'[q]}"
    return f"{side_str(L, True)} {h} {side_str(R, False)}"


def cvars(c):
    s = set()
    for side in (c[2], c[3]):
        for _, e in side[0]:
            s |= lvars(e)
    return s


def subst_cfg(c, v, y):
    q, f, L, R = c

    def ss(side):
        return (tuple((w, lsubst(e, v, y)) for w, e in side[0]), side[1])
    return (q, f, ss(L), ss(R))


def push(side, w, e=K(1)):
    """Put the word w (outward order) repeated e times in front of side, merging equal neighbours."""
    items, term = side
    if items and items[0][0] == w:
        return (((w, ladd(items[0][1], e)),) + items[1:], term)
    return (((w, e),) + items, term)


def norm_side(side):
    items, term = side
    out = []
    for w, e in items:
        if e == K(0) or not w:
            continue
        if out and out[-1][0] == w:
            out[-1] = (w, ladd(out[-1][1], e))
        else:
            out.append((w, e))
    if term == 'B':
        while out and all(b == 0 for b in out[-1][0]):
            out.pop()
    return (tuple(out), term)


class Engine:
    def __init__(self, machine, fresh_prefix="v"):
        self.m = machine
        self.T = parse(machine)
        self.nv = 0
        self.rules = {}      # (q, f, w, u) -> (v, nsteps) or None
        self.pref = fresh_prefix
        self.nosplit = False

    def fresh(self):
        self.nv += 1
        return f"{self.pref}{self.nv}"

    # -------------------------------------------------------------- popping the facing cell
    def pops(self, c, subs=()):
        """List of (c', sym, subs): c' is c with the facing side's first cell removed, sym that cell, subs the
        substitutions (v, Lin) made on the way (each v replaced everywhere)."""
        q, f, L, R = c
        side = R if f == 'R' else L
        items, term = norm_side(side)
        if not items:
            if term == 'S':
                raise ExitS()
            rest = (items, term)
            outs = [(0, rest)] if term == 'B' else [(0, rest), (1, rest)]
            return [(self._set(c, f, s), b, subs) for b, s in outs]
        w, e = items[0]
        if e[0] >= 1:
            rest = items[1:]
            e1 = lsub_const(e, 1)
            if e1 != K(0):
                rest = ((w, e1),) + rest
            if len(w) > 1:
                rest = ((w[1:], K(1)),) + rest
            return [(self._set(c, f, (rest, term)), w[0], subs)]
        v, _ = e[1][0]
        if self.nosplit:
            raise Stuck(v)
        out = []
        for y in (K(0), V(self.fresh(), 1)):
            c2 = subst_cfg(c, v, y)
            try:
                out.extend(self.pops(c2, subs + ((v, y),)))
            except ExitS:
                out.append((c2, None, subs + ((v, y),)))
        return out

    @staticmethod
    def _set(c, f, side):
        q, _, L, R = c
        return (q, f, L, side) if f == 'R' else (q, f, side, R)

    # -------------------------------------------------------------- one machine step
    def step(self, c):
        """One machine step: list of (c', subs)."""
        out = []
        for c2, b, subs in self.pops(c):
            if b is None:
                out.append((c2, subs))
                continue
            t = self.T[(c2[0], b)]
            if t is None:
                raise Halt(cfg_str(c2) + f" reading {b}")
            wr, d, q2 = t
            _, f, L, R = c2
            if d == 'R':
                out.append(((q2, 'R', norm_side(push(L, (wr,))), R), subs))
            else:
                out.append(((q2, 'L', L, norm_side(push(R, (wr,)))), subs))
        return out

    # -------------------------------------------------------------- shift rules
    def window(self, q, f, w, u):
        """Run from state q facing word w (outward), with the word u (outward) on the other side.
        Returns v (outward on the other side, after u) if the head comes out past w in state q facing the same way
        and u is intact, never looking past w or u; else None."""
        key = (q, f, w, u)
        if key in self.rules:
            return self.rules[key]
        front = list(w)          # facing side, nearest first
        back = list(u)           # other side, nearest first
        st, fac = q, f
        res = None
        for n in range(1, 2000):
            # read
            if fac == f:
                if not front:
                    break
                b = front.pop(0)
            else:
                if not back:
                    break
                b = back.pop(0)
            t = self.T[(st, b)]
            if t is None:
                break
            wr, d, st = t
            nf = 'R' if d == 'R' else 'L'
            # write goes behind the move
            if nf == f:
                back.insert(0, wr)
            else:
                front.insert(0, wr)
            fac = nf
            if fac == f and not front and st == q:
                b2 = tuple(back)
                if b2[:len(u)] == u:
                    res = (b2[len(u):], n)
                break
        self.rules[key] = res
        return res

    def lead_cells(self, side, n):
        cells = ()
        for w, e in side[0]:
            if len(cells) >= n or e != K(1):
                break
            cells += w
        return cells[:n]

    def cross(self, c, umax=3):
        """Try a shift rule on the facing item.  Returns list of successors or None."""
        q, f, L, R = c
        side, other = (R, L) if f == 'R' else (L, R)
        items, term = side
        if not items:
            return None
        w, e = items[0]
        if isconst(e) and e[0] < 3:
            return None
        cells = self.lead_cells(other, umax)
        for ulen in range(0, len(cells) + 1):
            u = cells[:ulen]
            r = self.window(q, f, w, u)
            if r is None:
                continue
            v, n = r
            orest = self._drop_cells(other, len(u))
            ns = push(orest, v, e) if v else orest
            for b in reversed(u):
                ns = push(ns, (b,))
            ns = norm_side(ns)
            nside = (items[1:], term)
            if f == 'R':
                return [(q, f, ns, nside)]
            return [(q, f, nside, ns)]
        return None

    def regroup(self, c, k):
        """Split the facing item w^e into (w^k)^e' w^r by cases on e mod k.  List of (c', subs)."""
        q, f, L, R = c
        side = R if f == 'R' else L
        items, term = side
        w, e = items[0]
        cs = [(c, ())]
        for v, a in e[1]:
            if a % k:
                if self.nosplit:
                    raise Stuck(None)
                nc = []
                for x, sb in cs:
                    for r in range(k):
                        y = (r, ((self.fresh(), k),))
                        nc.append((subst_cfg(x, v, y), sb + ((v, y),)))
                cs = nc
        out = []
        for x, sb in cs:
            side = x[3] if f == 'R' else x[2]
            items, term = side
            w, e = items[0]
            r = e[0] % k
            q0 = ((e[0] - r) // k, tuple((v, a // k) for v, a in e[1]))
            new = []
            if q0 != K(0):
                new.append((w * k, q0))
            if r:
                new.append((w, K(r)))
            ns = (tuple(new) + items[1:], term)
            out.append((self._set(x, f, ns), sb))
        return out

    @staticmethod
    def _drop_cells(side, n):
        items, term = side
        items = list(items)
        while n > 0:
            if not items:
                return None
            w, e = items[0]
            if e != K(1):
                return None
            if len(w) <= n:
                n -= len(w)
                items.pop(0)
            else:
                items[0] = (w[n:], K(1))
                n = 0
        return (tuple(items), term)


# ------------------------------------------------------------------ canonical form of a side

MAXW = 8
LITMAX = [2]


def primitive(w):
    n = len(w)
    for p in range(1, n + 1):
        if n % p == 0 and w[:p] * (n // p) == w:
            return w[:p]
    return w


def compress_side(side, minrep=3, scan=10**9):
    """Merge literal items into one word, absorb copies of a block word next to the block, and fold runs of a
    short word repeated at least minrep times into blocks.  The tape is unchanged."""
    items, term = norm_side(side)
    items = tuple((primitive(w), lmul(e, len(w) // len(primitive(w)))) if e != K(1) and primitive(w) != w else (w, e)
                  for w, e in items)
    items, term = norm_side((items, term))
    out = []
    lit = ()

    def flush_lit(nxt):
        nonlocal lit
        # absorb far-end copies into the next block
        if nxt is not None:
            w, e = nxt
            while lit and len(lit) >= len(w) and lit[len(lit) - len(w):] == w:
                lit = lit[:len(lit) - len(w)]
                e = ladd(e, K(1))
            nxt = (w, e)
        # fold runs inside the literal
        res = []
        i = 0
        cur = []
        while i < len(lit):
            if i >= scan:
                cur.extend(lit[i:])
                break
            best = None
            for p in range(1, MAXW + 1):
                w = lit[i:i + p]
                if len(w) < p or primitive(w) != w:
                    continue
                k = 1
                while lit[i + k * p:i + (k + 1) * p] == w:
                    k += 1
                if k >= minrep and k * p >= 4 and (best is None or k * p > best[0] * len(best[1])):
                    best = (k, w)
            if best:
                if cur:
                    res.append((tuple(cur), K(1)))
                    cur = []
                k, w = best
                res.append((w, K(k)))
                i += k * len(w)
            else:
                cur.append(lit[i])
                i += 1
        if cur:
            res.append((tuple(cur), K(1)))
        out.extend(res)
        lit = ()
        return nxt

    for w, e in items:
        if e == K(1) or (isconst(e) and e[0] * len(w) <= LITMAX[0]):
            lit += w * e[0]
        else:
            nxt = flush_lit((w, e))
            if out and out[-1][0] == nxt[0]:
                out[-1] = (nxt[0], ladd(out[-1][1], nxt[1]))
            else:
                out.append(nxt)
    flush_lit(None)
    # merge equal neighbours again
    res = []
    for w, e in out:
        if res and res[-1][0] == w:
            res[-1] = (w, ladd(res[-1][1], e))
        elif res and res[-1][1] == K(1) and e == K(1):
            res[-1] = (res[-1][0] + w, K(1))
        else:
            res.append((w, e))
    return norm_side((tuple(res), term))


def canon(c):
    q, f, L, R = c
    return (q, f, compress_side(L), compress_side(R))


def compress_near(side):
    """compress_side on the part of the side up to its first repeat; the rest is assumed canonical already."""
    items, term = side
    n = 0
    while n < len(items) and (items[n][1] == K(1) or (isconst(items[n][1]) and items[n][1][0] * len(items[n][0]) <= 2)):
        n += 1
    n = min(n + 2, len(items))
    if n == len(items):
        return compress_side(side)
    head, _ = compress_side((items[:n], 'S'), scan=24)
    rest = items[n:]
    if head and rest and head[-1][0] == rest[0][0]:
        head = head[:-1] + ((head[-1][0], ladd(head[-1][1], rest[0][1])),)
        rest = rest[1:]
    return (head + rest, term)


def canon_near(c):
    q, f, L, R = c
    return (q, f, compress_near(L), compress_near(R))
