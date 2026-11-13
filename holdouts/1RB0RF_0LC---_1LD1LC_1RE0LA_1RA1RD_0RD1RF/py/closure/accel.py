"""Exact accelerated simulator for 1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF (works for any 2-symbol machine).

Copied from holdouts/1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA/py/closure/accel.py (see there and the README of that
machine for the method).  Changes: the event is state A at the left end (EVSTATE); `compress` looks for words of up
to 32 cells (the blocks of this machine have words of 12, 15, 21, 24 and 30 cells) and, at the top level, first
writes out every repeat with fewer than 40 copies, so that a long word that contains short repeats is found;
`selftest` compares cells, not bracketings.  Nothing else is changed; in particular the rules are proved as before.

Level 1 (words): the tape is a list of cells and repeats `(w)^n`.  When the head stands next to a repeat and one,
two or three copies of `w` take it, in the same state, to the far side of the copies without leaving them and a
carried word `u` behind the head (checked by running the plain machine on `u w` between two walls), all copies are
crossed at once (a shift rule; `one_right`, `one_left`).

Level 2 (cycles): at every *event* (the state EVSTATE reaches the left end of the visited tape) the tape is re-bracketed
(`compress`) and its *shape* (the words and the small counts) recorded.  When a shape comes back three times at equal
distance with the large counts moving by constant amounts, a cycle rule is proposed and then *checked by a symbolic
run* of the same engine: each large count n_i is replaced by b_i + M*x_i (x_i >= 0 a free variable) and the engine
runs R*k events (R chosen so that every count moves by a multiple of M).  The engine refuses (Undecided) any
operation whose result would depend on the value of a variable, so a run that ends in the start shape with counts
b_i + D_i + M*x_i is a proof of the rule for all x >= 0, with the step count an affine form in x.  N applications are
then done at once; their step sum is a quadratic polynomial in N computed exactly.

Level 3 (classes; kept from the original, not used for this machine): a run whose one big count is k + c x.  A rule that shrinks that count by d per
application is applied (k - base) // d + 1 + (c / d) x times when d divides c (true for every x); otherwise the run
stops with NeedSplit(d).  Step counts are then polynomials in x (`Pol`), used for validation only.

usage: python3 accel.py MAXSTEPS [options]
  --plain         no cycle rules (level 1 only)
  --shapes T      print the tape at events whose shape (counts >= T wild) is new among the last 6
  --every N       print every N-th event
  --quiet         only the summary
  --start 'cfg'   start from a configuration like '<A> 0 (011)^7 101101 (101011010110)^445 10101'
"""
import sys
from fractions import Fraction
from math import gcd

MACHINE = "1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF"
EVSTATE = 0     # the state whose arrival at the left end of the tape is an event (A)
MAXC = 12
MINN = 6         # shortest repeat a shift rule is tried on
MODULI = (3, 6, 12)    # moduli of the symbolic counts, tried in turn
MAXM = 12
KS = (1, 2, 3)   # numbers of copies of a word a shift rule may take at once
VERBOSE = False
MAXK = 300000    # longest cycle looked for, in events
BIG = 64         # counts >= BIG are variables of a cycle rule
SYMBOLIC_N = True  # a rule may be applied a number of times that is affine in the variable (see `applications`)
TBASE = 40       # symbolic counts are b + M x with TBASE <= b < TBASE + M (BIG >= TBASE + MAXM)


def table(machine):
    T = {}
    for i, s in enumerate(machine.split('_')):
        for b in (0, 1):
            t = s[3 * b:3 * b + 3]
            T[(i, b)] = None if t[2] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return T


T = table(MACHINE)


class Undecided(Exception):
    pass


class NeedSplit(Undecided):
    """A cycle rule would apply a number of times that depends on the variable in a way that is not affine: the
    count it shrinks by d per application is k + c x with d not dividing c.  `d` says how to split the class."""

    def __init__(self, d, msg):
        Undecided.__init__(self, msg)
        self.d = d


class Pol:
    """A polynomial in the variable x0 with rational coefficients (only used for step counts, never for decisions)."""
    __slots__ = ("a",)

    def __init__(self, a):
        a = list(a)
        while a and a[-1] == 0:
            a.pop()
        self.a = a

    @staticmethod
    def of(v):
        if isinstance(v, Pol):
            return v
        if isinstance(v, Lin):
            if any(k != 0 for k in v.c):
                raise Undecided("step polynomial in another variable")
            return Pol([Fraction(v.k), Fraction(v.c.get(0, 0))])
        return Pol([Fraction(v)])

    def __add__(self, o):
        o = Pol.of(o)
        n = max(len(self.a), len(o.a))
        return Pol([(self.a[i] if i < len(self.a) else 0) + (o.a[i] if i < len(o.a) else 0) for i in range(n)])

    __radd__ = __add__

    def __mul__(self, o):
        o = Pol.of(o)
        r = [Fraction(0)] * (len(self.a) + len(o.a))
        for i, x in enumerate(self.a):
            for j, y in enumerate(o.a):
                r[i + j] += x * y
        return Pol(r)

    __rmul__ = __mul__

    def at(self, x):
        v = sum(c * x ** i for i, c in enumerate(self.a))
        assert v.denominator == 1
        return int(v)

    def __lt__(self, o):       # only so that `steps < maxsteps` does not fail; symbolic runs pass maxsteps=None
        raise Undecided("comparison of a step polynomial")

    def __repr__(self):
        return ' + '.join("%s*x^%d" % (c, i) for i, c in enumerate(self.a)) or '0'


class Lin:
    """k + sum c[v] x_v with x_v >= 0 free; all c[v] > 0."""
    __slots__ = ("k", "c")

    def __init__(self, k, c=None):
        self.k = k
        self.c = {v: a for v, a in (c or {}).items() if a}

    def __add__(self, o):
        if isinstance(o, int):
            return Lin(self.k + o, self.c)
        c = dict(self.c)
        for v, a in o.c.items():
            c[v] = c.get(v, 0) + a
        return Lin(self.k + o.k, c)

    __radd__ = __add__

    def __sub__(self, o):
        if isinstance(o, int):
            return Lin(self.k - o, self.c)
        c = dict(self.c)
        for v, a in o.c.items():
            c[v] = c.get(v, 0) - a
        return Lin(self.k - o.k, c)

    def __mul__(self, a):
        return Lin(self.k * a, {v: b * a for v, b in self.c.items()})

    __rmul__ = __mul__

    def __eq__(self, o):
        if isinstance(o, int):
            return not self.c and self.k == o
        return self.k == o.k and self.c == o.c

    def __repr__(self):
        return "%d%s" % (self.k, ''.join("+%d*x%d" % (a, v) for v, a in sorted(self.c.items())))


def norm(n):
    """A Lin without variables is an int."""
    if isinstance(n, Lin):
        if any(a < 0 for a in n.c.values()):
            raise Undecided("negative coefficient")
        if not n.c:
            return n.k
    return n


# What the engine asked about counts with variables (each answer holds for every value of the variables, or the run
# stops with Undecided): number of comparisons and their smallest margin (constant part minus bound), divisions,
# decrements.
QUERIES = {"ge": 0, "margin": None, "div": 0, "dec": 0}


def ge(n, k):
    """n >= k, for every value of the variables."""
    if isinstance(n, int):
        return n >= k
    if n.c:
        QUERIES["ge"] += 1
        if n.k >= k and (QUERIES["margin"] is None or n.k - k < QUERIES["margin"]):
            QUERIES["margin"] = n.k - k
    if n.k >= k:
        return True
    raise Undecided("count %r >= %d ?" % (n, k))


def lt(n, k):
    return not ge(n, k)


def div(n, k):
    """(n // k, n % k)."""
    if isinstance(n, int):
        return divmod(n, k)
    QUERIES["div"] += 1
    if any(a % k for a in n.c.values()):
        raise Undecided("count %r / %d" % (n, k))
    return norm(Lin(n.k // k, {v: a // k for v, a in n.c.items()})), n.k % k


def dec(n):
    """n - 1 for a count that is surely >= 2, or None when n == 1."""
    if isinstance(n, int):
        return None if n == 1 else n - 1
    QUERIES["dec"] += 1
    if n.k >= 2:
        return n - 1
    raise Undecided("pop from %r" % (n,))


# ---------------------------------------------------------------- shift rules (plain machine between two walls)
cacheR = {}
cacheL = {}


def one_right(q, u, w):
    """u q> w  ->  v u q>  without leaving the cells of u w: returns (v, steps) or None."""
    key = (q, u, w)
    if key in cacheR:
        return cacheR[key]
    tape = list(u) + list(w)
    lw, lu = len(w), len(u)
    p, st, n, N, res = lu, q, 0, len(tape), None
    while n < 5000:
        if p < 0:
            break
        if p >= N:
            if st == q and tuple(tape[lw:]) == tuple(u):
                res = (tuple(tape[:lw]), n)
            break
        t = T[(st, tape[p])]
        if t is None:
            break
        tape[p] = t[0]
        p += t[1]
        st = t[2]
        n += 1
    cacheR[key] = res
    return res


def one_left(q, u, w):
    """w q> u  ->  q> u v  (head on the first cell of u) without leaving the cells of w u: (v, steps) or None."""
    key = (q, u, w)
    if key in cacheL:
        return cacheL[key]
    tape = list(w) + list(u)
    lw, lu = len(w), len(u)
    p, st, n, N, res = lw, q, 0, len(tape), None
    while n < 5000:
        if p < 0 or p >= N:
            break
        t = T[(st, tape[p])]
        if t is None:
            break
        tape[p] = t[0]
        p += t[1]
        st = t[2]
        n += 1
        if p == 0 and st == q and tuple(tape[:lu]) == tuple(u):
            res = (tuple(tape[lu:]), n)
            break
    cacheL[key] = res
    return res


# ---------------------------------------------------------------- the engine
class Sim:
    """L: tokens left of the head (far end first); R: tokens from the head rightwards, stored reversed (R[-1] is the
    cell under the head).  A token is a cell 0/1 or a list [word, count]."""

    def __init__(s):
        s.L = []
        s.R = []
        s.st = 0
        s.steps = 0
        s.halt = False
        s.used = {}

    def pushL(s, w, n):
        if s.L and isinstance(s.L[-1], list) and s.L[-1][0] == w:
            s.L[-1][1] = s.L[-1][1] + n
        else:
            s.L.append([w, n])

    def pushR(s, w, n):
        if s.R and isinstance(s.R[-1], list) and s.R[-1][0] == w:
            s.R[-1][1] = s.R[-1][1] + n
        else:
            s.R.append([w, n])

    def popR(s):
        if not s.R:
            return 0
        t = s.R[-1]
        if isinstance(t, int):
            s.R.pop()
            return t
        w = t[0]
        d = dec(t[1])
        if d is None:
            s.R.pop()
        else:
            t[1] = d
        for c in reversed(w[1:]):
            s.R.append(c)
        return w[0]

    def popL(s):
        if not s.L:
            return 0
        t = s.L[-1]
        if isinstance(t, int):
            s.L.pop()
            return t
        w = t[0]
        d = dec(t[1])
        if d is None:
            s.L.pop()
        else:
            t[1] = d
        for c in w[:-1]:
            s.L.append(c)
        return w[-1]

    def lits_L(s, k):
        out = []
        for t in reversed(s.L):
            if not isinstance(t, int) or len(out) >= k:
                break
            out.append(t)
        return tuple(reversed(out))

    def lits_R(s, k):
        out = []
        for t in reversed(s.R):
            if not isinstance(t, int) or len(out) >= k:
                break
            out.append(t)
        return tuple(out)

    def try_cross(s):
        if s.R and isinstance(s.R[-1], list) and ge(s.R[-1][1], MINN):
            w, n = s.R[-1]
            lit = s.lits_L(MAXC)
            for k in KS:
                for lu in range(0, len(lit) + 1):
                    u = lit[len(lit) - lu:]
                    r = one_right(s.st, u, w * k)
                    if r:
                        v, c = r
                        m, rem = div(n, k)
                        if rem:
                            s.R[-1][1] = rem
                        else:
                            s.R.pop()
                        del s.L[len(s.L) - lu:]
                        s.pushL(v, m)
                        s.L.extend(u)
                        s.steps = s.steps + c * m
                        s.used[('R', s.st, u, w * k, v)] = c
                        s.last = ('R', 'ABCDEF'[s.st], u, w * k, v, m, c)
                        return True
        if s.L and isinstance(s.L[-1], list) and ge(s.L[-1][1], MINN):
            w, n = s.L[-1]
            lit = s.lits_R(MAXC)
            for k in KS:
                for lu in range(1, len(lit) + 1):
                    u = lit[:lu]
                    r = one_left(s.st, u, w * k)
                    if r:
                        v, c = r
                        m, rem = div(n, k)
                        if rem:
                            s.L[-1][1] = rem
                        else:
                            s.L.pop()
                        del s.R[len(s.R) - lu:]
                        s.pushR(v, m)
                        s.R.extend(reversed(u))
                        s.steps = s.steps + c * m
                        s.used[('L', s.st, u, w * k, v)] = c
                        s.last = ('L', 'ABCDEF'[s.st], u, w * k, v, m, c)
                        return True
        return False

    def step(s):
        """One move: a shift rule ('x') or a machine step ('r'/'l'); 'h' on the halting transition."""
        if s.try_cross():
            return 'x'
        r = s.popR()
        t = T[(s.st, r)]
        if t is None:
            s.R.append(r)
            s.halt = True
            return 'h'
        w, m, ns = t
        s.st = ns
        s.steps = s.steps + 1
        if m == 1:
            s.L.append(w)
            return 'r'
        s.R.append(w)
        s.R.append(s.popL())
        return 'l'

    def flat(s):
        return list(s.L) + ['H'] + list(reversed(s.R))

    def recompress(s):
        s.L = compress(s.L)
        s.R = list(reversed(compress(list(reversed(s.R)))))

    def event(s, r):
        """State E has just arrived at the left end of the visited tape."""
        return r == 'l' and s.st == EVSTATE and not s.L


def small(n, k):
    return isinstance(n, int) and n < k


def compress(seq, top=True):
    """Re-bracket a token list (cells left to right): repeats of count < 3 are written out, a repeat absorbs equal
    words next to it and is rotated as far left as it goes, runs of >= 4 equal words of <= 14 cells become repeats."""
    out = []
    for t in seq:
        if isinstance(t, list):
            w = t[0]
            for d in range(1, len(w)):
                if len(w) % d == 0 and w[:d] * (len(w) // d) == w:
                    t = [w[:d], t[1] * (len(w) // d)]
                    break
        if isinstance(t, list) and small(t[1], 40 if top else 3):
            out.extend(list(t[0]) * t[1])
        else:
            out.append(t if not isinstance(t, list) else [t[0], t[1]])
    changed = True
    while changed:
        changed = False
        i = 0
        while i < len(out):
            t = out[i]
            if isinstance(t, list):
                w = t[0]
                Lw = len(w)
                if i + 1 < len(out) and isinstance(out[i + 1], list) and out[i + 1][0] == w:
                    t[1] = t[1] + out[i + 1][1]
                    del out[i + 1]
                    changed = True
                    continue
                if i >= Lw and all(isinstance(x, int) for x in out[i - Lw:i]) and tuple(out[i - Lw:i]) == w:
                    del out[i - Lw:i]
                    i -= Lw
                    t[1] = t[1] + 1
                    changed = True
                    continue
                if i >= 1 and isinstance(out[i - 1], int) and out[i - 1] == w[-1]:
                    x = out[i - 1]
                    out[i - 1] = [(x,) + w[:-1], t[1]]
                    out[i] = x
                    i -= 1
                    changed = True
                    continue
                if all(isinstance(x, int) for x in out[i + 1:i + 1 + Lw]) and tuple(out[i + 1:i + 1 + Lw]) == w:
                    del out[i + 1:i + 1 + Lw]
                    t[1] = t[1] + 1
                    changed = True
                    continue
            i += 1
    res = []
    i = 0
    n = len(out)
    while i < n:
        if not isinstance(out[i], int):
            res.append(out[i])
            i += 1
            continue
        j = i
        while j < n and isinstance(out[j], int):
            j += 1
        s = out[i:j]
        k = 0
        m = len(s)
        while k < m:
            best = None
            for Lw in range(1, 33):
                c = 1
                while k + (c + 1) * Lw <= m and s[k + c * Lw:k + (c + 1) * Lw] == s[k:k + Lw]:
                    c += 1
                if c >= 4 and (best is None or c * Lw > best[0] * best[1]):
                    best = (c, Lw)
            if best:
                res.append([tuple(s[k:k + best[1]]), best[0]])
                k += best[0] * best[1]
            else:
                res.append(s[k])
                k += 1
        i = j
    if any(isinstance(t, list) for t in res) and res != out:
        return compress(res, False)       # new repeats may merge with their neighbours
    return res


def fmt(tokens, st):
    out = []
    lit = ''
    for t in tokens:
        if isinstance(t, int):
            lit += str(t)
        else:
            if lit:
                out.append(lit)
                lit = ''
            if t == 'H':
                out.append('<%s>' % 'ABCDEF'[st])
            else:
                out.append('(%s)^%s' % (''.join(map(str, t[0])), t[1]))
    if lit:
        out.append(lit)
    return ' '.join(out)


def parse(txt):
    s = Sim()
    left, right = [], []
    cur = left
    for part in txt.split():
        if part.startswith('<'):
            s.st = 'ABCDEF'.index(part[1])
            cur = right
        elif part.startswith('('):
            w, e = part[1:].split(')^')
            cur.append([tuple(int(c) for c in w), int(e)])
        else:
            cur.extend(int(c) for c in part)
    s.L = left
    s.R = list(reversed(right))
    return s


# ---------------------------------------------------------------- cycle rules
def isbig(n, big=BIG):
    """n >= big; a count with variables must be surely big (or the question is Undecided)."""
    return n >= big if isinstance(n, int) else ge(n, big)


def shape(toks, st, big=BIG):
    return (st,) + tuple(t if not isinstance(t, list) else (t[0], -1 if isbig(t[1], big) else t[1]) for t in toks)


def bigs(toks, big=BIG):
    return [t[1] for t in toks if isinstance(t, list) and isbig(t[1], big)]


def val(n, env):
    """The value of a count at the point env of the variables."""
    return n if isinstance(n, int) else n.k + sum(a * env[v] for v, a in n.c.items())


def concrete(toks, env):
    return [[t[0], val(t[1], env)] if isinstance(t, list) else t for t in toks]


class Rule:
    __slots__ = ("events", "base", "D", "S", "uses", "M", "shape")


def run_events(s, nev, max_moves=10 ** 9):
    """Advance by nev events (re-bracketing at each, and now and then in between)."""
    n = 0
    last = 0
    while nev > 0:
        r = s.step()
        n += 1
        if r == 'h':
            return False
        if s.event(r):
            s.recompress()
            nev -= 1
            last = n
        elif n - last > 2000:
            s.recompress()
            last = n
        if n > max_moves:
            raise Undecided("too long")
    return True


def verify(toks, st, d, k):
    """Try to prove the cycle of k events with count increments d from the shape of toks, with the smallest modulus
    that works.  Returns a Rule or None."""
    for m in MODULI:
        r = verify_mod(toks, st, d, k, m)
        if r is not None:
            return r
    return None


def verify_mod(toks, st, d, k, M):
    g = M
    for x in d:
        g = gcd(g, abs(x))
    R = M // g
    counts = bigs(toks)
    base = [TBASE + 2 * R * abs(x) + (n - TBASE - 2 * R * abs(x)) % M for n, x in zip(counts, d)]
    if any(b > n for b, n in zip(base, counts)):
        return None
    sym = Sim()
    sym.st = st
    cur = sym.L
    i = 0
    for t in toks:
        if t == 'H':
            cur = sym.R
        elif isinstance(t, list) and t[1] >= BIG:
            cur.append([t[0], Lin(base[i], {i: M})])
            i += 1
        elif isinstance(t, list):
            cur.append([t[0], t[1]])
        else:
            cur.append(t)
    sym.R.reverse()
    sym.steps = Lin(0)
    try:
        if not run_events(sym, R * k):
            return None
        end = compress(sym.flat())
    except Undecided as e:
        if VERBOSE:
            sys.stderr.write("   M=%d undecided: %s\n" % (M, e))
        return None
    want = []
    i = 0
    for t in toks:
        if isinstance(t, list) and t[1] >= BIG:
            want.append([t[0], Lin(base[i] + R * d[i], {i: M})])
            i += 1
        elif isinstance(t, list):
            want.append([t[0], t[1]])
        else:
            want.append(t)
    if VERBOSE:
        sys.stderr.write("   M=%d end  %s\n         want %s\n" % (M, fmt(end, sym.st), fmt(want, st)))
    if sym.st != st or len(end) != len(want):
        return None
    for a, b in zip(end, want):
        if isinstance(a, list) != isinstance(b, list):
            return None
        if isinstance(a, list):
            if a[0] != b[0] or not (norm(a[1]) == norm(b[1])):
                return None
        elif a != b:
            return None
    r = Rule()
    r.events = R * k
    r.base = base
    r.D = [R * x for x in d]
    r.S = sym.steps if isinstance(sym.steps, Lin) else Lin(sym.steps)
    r.uses = 0
    r.M = M
    r.shape = shape(toks, st)
    return r


def applications(rule, counts):
    """How many times the rule applies in a row from these counts (0 if it does not apply)."""
    N = None
    symN = None
    M = rule.M
    for n, b, D in zip(counts, rule.base, rule.D):
        if isinstance(n, Lin):
            # a count with variables: the rule must apply for every value of them
            if n.k < b or (n.k - b) % M or any(a % M for a in n.c.values()):
                return 0
            if D < 0:
                # the rule shrinks it by d = -D per application.  It applies while the count is >= b, that is
                # (n - b) // d + 1 times; with n = k + c x and d | c this is (k - b) // d + 1 + (c / d) x for every x.
                if not SYMBOLIC_N:
                    return 0
                if any(a % (-D) for a in n.c.values()):
                    raise NeedSplit(-D, "rule shrinks %r by %d per application" % (n, -D))
                if symN is not None:
                    raise Undecided("two shrinking counts with a variable")
                symN = Lin((n.k - b) // (-D) + 1, {v: a // (-D) for v, a in n.c.items()})
            continue
        if n < b or (n - b) % M:
            return 0
        if D < 0:
            c = (n - b) // (-D) + 1
            N = c if N is None else min(N, c)
    if symN is not None:
        if N is None:
            return symN
        if N <= symN.k:          # the number count runs out first, for every x
            return N
        raise Undecided("which count runs out first depends on x")
    return N if N is not None else 0       # a rule that shrinks nothing is not used (it would never stop)


def apply_rule(s, toks, rule, N):
    counts = bigs(toks)
    M = rule.M
    symN = isinstance(N, Lin)
    PN = Pol.of(N) if symN else N
    tot = PN * rule.S.k
    for i, a in rule.S.c.items():
        n = counts[i]
        if isinstance(n, Lin):
            x = Lin((n.k - rule.base[i]) // M, {v: c // M for v, c in n.c.items()})
        else:
            x = (n - rule.base[i]) // M
        if symN:
            tot = tot + a * (PN * Pol.of(x)) + (a * (rule.D[i] // M)) * (PN * (PN + (-1))) * Fraction(1, 2)
        else:
            tot = tot + (a * N) * x + a * ((rule.D[i] // M) * N * (N - 1) // 2)
    i = 0
    new = []
    for t in toks:
        if isinstance(t, list) and isbig(t[1]):
            new.append([t[0], norm(t[1] + N * rule.D[i])])
            i += 1
        elif isinstance(t, list):
            new.append([t[0], t[1]])
        else:
            new.append(t)
    h = new.index('H')
    s.L = new[:h]
    s.R = list(reversed(new[h + 1:]))
    s.steps = (Pol.of(s.steps) + tot) if symN else s.steps + tot
    rule.uses += 1


class Driver:
    def __init__(self, sim=None, accel=True):
        self.s = sim or Sim()
        self.accel = accel
        self.rules = {}          # shape -> [Rule]
        self.hist = {}           # shape -> [(event index, counts, steps)]
        self.failed = {}
        self.ev = 0
        self.jumps = 0
        self.nrules = 0
        self.nfail = 0
        self.moves = 0
        self.skipped = 0         # events jumped over
        self.env = None          # values of the variables (a symbolic run), used only to look for cycles

    def at_event(self):
        """Called at an event, after re-bracketing.  Returns the token list (after a possible jump)."""
        toks = self.at_event1()
        if self.env is not None and not any(isinstance(t, list) and isinstance(t[1], Lin) for t in toks):
            return compress(self.s.flat())
        return toks

    def at_event1(self):
        s = self.s
        toks = compress(s.flat())
        if not self.accel:
            return toks
        full = shape(toks, s.st)
        sh = hash(full)
        counts = bigs(toks)
        if not counts:
            return toks
        for rule in self.rules.get(sh, ()):
            N = applications(rule, counts) if rule.shape == full else 0
            if isinstance(N, Lin) or N >= 1:
                apply_rule(s, toks, rule, N)
                self.jumps += 1
                self.skipped += N * rule.events
                self.ev += N * rule.events
                self.hist.pop(sh, None)
                return compress(s.flat())
        if self.env is not None:
            real = counts
            toks0, toks = toks, concrete(toks, self.env)
            counts = bigs(toks)
        h = self.hist.setdefault(sh, [])
        h.append((self.ev, counts, None))
        if len(h) > 3:
            del h[0]
        if len(self.hist) > 1500000:
            self.hist.clear()
        if len(h) < 3:
            return toks
        k = h[2][0] - h[1][0]
        if isinstance(k, Lin):               # event numbers carry the variable after a symbolic jump
            k = norm(k)
        if isinstance(k, Lin) or isinstance(h[1][0] - h[0][0], Lin) and norm(h[1][0] - h[0][0]) != k:
            return toks
        if k != h[1][0] - h[0][0] or k > MAXK:
            return toks
        d = [b - a for a, b in zip(h[1][1], h[2][1])]
        if d != [b - a for a, b in zip(h[0][1], h[1][1])] or not any(x < 0 for x in d):
            return toks
        if any(x < 0 and n + 6 * MAXM * x < TBASE + MAXM for n, x in zip(counts, d)):
            return toks                      # not worth a rule: too few applications fit
        key = (sh, tuple(d), tuple(n % MAXM for n in counts))
        f = self.failed.get(key, 0)
        if f:
            self.failed[key] = f - 1
            return toks
        if VERBOSE:
            sys.stderr.write("verify at %s ev %d k=%d d=%s counts=%s\n" % (s.steps, self.ev, k, d, counts))
        rule = verify(toks, s.st, d, k)
        if VERBOSE:
            sys.stderr.write("   -> %s\n" % ((None if rule is None else (rule.M, rule.events, rule.D)),))
        if rule is None:
            self.nfail += 1
            self.failed[key] = 50
            if len(self.failed) > 100000:
                self.failed.clear()
            return toks
        self.nrules += 1
        self.rules.setdefault(sh, []).append(rule)
        if self.env is not None:
            toks, counts = toks0, real
        N = applications(rule, counts)
        if isinstance(N, Lin) or N >= 1:
            apply_rule(s, toks, rule, N)
            self.jumps += 1
            self.skipped += N * rule.events
            self.ev += N * rule.events
            self.hist.pop(sh, None)
            return compress(s.flat())
        return toks

    def run(self, maxsteps, on_event=None, max_moves=None):
        """Run until maxsteps (None: until on_event returns True)."""
        s = self.s
        last = 0
        while (maxsteps is None or s.steps < maxsteps) and not s.halt:
            r = s.step()
            self.moves += 1
            if s.event(r):
                s.recompress()
                self.ev += 1
                toks = self.at_event()
                last = self.moves
                if on_event and on_event(self, toks):
                    break
            elif self.moves - last > 2000:
                s.recompress()
                last = self.moves
            if max_moves and self.moves >= max_moves:
                break
        return s


def cells(toks):
    """The cells of a token list with numeric counts ('H' kept as a marker)."""
    out = []
    for t in toks:
        if isinstance(t, (list, tuple)):
            out.extend(t[0] * t[1])
        else:
            out.append(t)
    return out


def selftest(rule, xs=(0, 1, 3)):
    """Re-check a cycle rule on numbers: from its shape with counts b_i + M x_i (x_i from xs, in a few mixes) the
    plain engine (no cycle rules) must reach the counts b_i + D_i + M x_i in rule.events events and S(x) steps."""
    nv = len(rule.base)
    tests = [[x] * nv for x in xs] + [[xs[(i + j) % len(xs)] for i in range(nv)] for j in range(1, len(xs))]
    for x in tests:
        s = Sim()
        s.st = rule.shape[0]
        cur = s.L
        want = []
        i = 0
        for t in rule.shape[1:]:
            if t == 'H':
                cur = s.R
                want.append(t)
            elif isinstance(t, tuple):
                if t[1] == -1:
                    n = rule.base[i] + rule.M * x[i]
                    want.append([t[0], n + rule.D[i]])
                    i += 1
                else:
                    n = t[1]
                    want.append([t[0], n])
                cur.append([t[0], n])
            else:
                cur.append(t)
                want.append(t)
        s.R.reverse()
        d = Driver(s, False)
        left = [rule.events]

        def on_event(d, toks):
            left[0] -= 1
            return left[0] == 0

        d.run(None, on_event)
        steps = rule.S.k + sum(a * x[i] for i, a in rule.S.c.items())
        if s.halt or cells(s.flat()) != cells(want) or s.steps != steps:
            return False
    return True


# ---------------------------------------------------------------- a cycle that only grows: a proof of non-halting
MS = 16          # modulus of the variables of the final cycle
PBASE = 2 * BIG  # its counts are b + MS x with PBASE <= b < PBASE + MS


def symbolic_copy(toks, st, grow):
    """The configuration toks with the i-th large count replaced by b_i + MS x_i when grow[i]."""
    sym = Sim()
    sym.st = st
    sym.steps = Lin(0)
    cur = sym.L
    env = {}
    base = {}
    i = 0
    for t in toks:
        if t == 'H':
            cur = sym.R
        elif isinstance(t, list) and isbig(t[1]):
            if grow[i]:
                b = PBASE + (t[1] - PBASE) % MS
                if b > t[1]:
                    return None
                env[i] = (t[1] - b) // MS
                base[i] = b
                cur.append([t[0], Lin(b, {i: MS})])
            else:
                cur.append([t[0], t[1]])
            i += 1
        elif isinstance(t, list):
            cur.append([t[0], t[1]])
        else:
            cur.append(t)
    sym.R.reverse()
    return sym, env, base


def prove_growth(driver, toks, st, grow, max_events, log=None):
    """Try to prove that the configuration toks (an event), with the growing large counts as variables, comes back to
    itself with those counts larger by multiples of MS.  The symbolic run uses the cycle rules of `driver` (each one
    proved for all values of its variables) and may prove new ones.  Returns a dict describing the proof, or None."""
    r = symbolic_copy(toks, st, grow)
    if r is None:
        return None
    sym, env, base = r
    start = compress(sym.flat())
    start_shape = shape(start, st)
    d2 = Driver(sym, True)
    d2.rules = driver.rules
    d2.env = env
    res = {}

    def on_event(d, tk):
        if d.ev > max_events:
            return True
        if d.s.st != st or len(tk) != len(start):
            return False
        inc = {}
        for a, b in zip(tk, start):
            if isinstance(a, list) != isinstance(b, list):
                return False
            if not isinstance(a, list):
                if a != b:
                    return False
                continue
            if a[0] != b[0]:
                return False
            if isinstance(b[1], Lin):
                if not isinstance(a[1], Lin) or a[1].c != b[1].c or a[1].k < b[1].k:
                    return False
                v = next(iter(b[1].c))
                inc[v] = a[1].k - b[1].k
            elif not (isinstance(a[1], int) and a[1] == b[1]):
                return False
        if not any(inc.values()) or any(x % MS for x in inc.values()):
            return False          # same shape, but not yet a step of the family b + MS x: go on
        res.update(inc=inc, events=d.ev, steps=d.s.steps, start=fmt(start, st), end=fmt(tk, st), base=base, env=env,
                   moves=d.moves, jumps=d.jumps)
        return True

    try:
        d2.run(None, on_event)
    except Undecided as e:
        if log:
            log("   symbolic run undecided after %d events: %s" % (d2.ev, e))
        return None
    if d2.s.halt or not res:
        if log:
            log("   symbolic run: no return in %d events" % d2.ev)
        return None
    return res


def search_proof(maxtime, log=print, sparse=1):
    """Run from blank tape; at events with at most `sparse` large counts remember the shape; when a shape comes back
    with large counts only grown, try to prove the growth cycle.  Returns (driver, proof or None)."""
    import time
    t0 = time.time()
    d = Driver()
    seen = {}
    out = {}
    tried = [0]

    def on_event(d, toks):
        if time.time() - t0 > maxtime:
            return True
        counts = bigs(toks)
        if not counts or len(counts) > sparse:
            return False
        full = shape(toks, d.s.st)
        prev = seen.get(full)
        seen[full] = (d.ev, counts, d.s.steps)
        if prev is None or tried[0] >= 20:
            return False
        dd = [b - a for a, b in zip(prev[1], counts)]
        if any(x < 0 for x in dd) or not any(dd):
            return False
        tried[0] += 1
        log("shape seen at event %d (steps %d) is back at event %d (steps %d), large counts %s -> %s"
            % (prev[0], prev[2], d.ev, d.s.steps, prev[1], counts))
        pr = prove_growth(d, toks, d.s.st, [x > 0 for x in dd], 4 * (d.ev - prev[0]) + 1000, log)
        if pr:
            pr.update(at_event=d.ev, at_steps=d.s.steps, first_event=prev[0], first_steps=prev[2],
                      config=fmt(toks, d.s.st))
            out.update(pr)
            return True
        return False

    d.run(None, on_event)
    return d, (out or None)


def main(argv):
    opts = argv[2:]
    if argv[1] == 'prove':
        global MS, PBASE
        if '--ms' in opts:
            MS = int(opts[opts.index('--ms') + 1])
        if '--pbase' in opts:
            PBASE = int(opts[opts.index('--pbase') + 1])
        d, pr = search_proof(float(opts[0]) if opts and opts[0][0] != '-' else 500)
        print("events", d.ev, "moves", d.moves, "jumps", d.jumps, "rules", d.nrules, "failed", d.nfail)
        rules = [r for rs in d.rules.values() for r in rs]
        print("cycle rules: %d; re-checked on numbers with the plain engine: %s"
              % (len(rules), "all pass" if all(selftest(r) for r in rules) else "FAILURE"))
        for r in rules:
            print("  rule: %d events, modulus %d, counts %s by %s, steps %r, used %d times\n        from %s"
                  % (r.events, r.M, r.base, r.D, r.S, r.uses, fmt([list(t) if isinstance(t, tuple) else t for t in
                     [('n%d' % 0,) and t for t in r.shape[1:]]], r.shape[0]).replace('^-1', '^n')))
        if pr:
            print("PROVED: growth cycle")
            for k in ("first_event", "first_steps", "at_event", "at_steps", "config", "start", "end", "base", "env",
                      "inc", "events", "steps", "moves", "jumps"):
                print("  %-12s %s" % (k, pr[k]))
        else:
            print("no proof found")
        return
    maxsteps = float(argv[1])
    accel = '--plain' not in opts
    quiet = '--quiet' in opts
    every = int(opts[opts.index('--every') + 1]) if '--every' in opts else 0
    thr = int(opts[opts.index('--shapes') + 1]) if '--shapes' in opts else 0
    sim = parse(opts[opts.index('--start') + 1]) if '--start' in opts else None
    recent = []
    cnt = [0]
    first = float(opts[opts.index('--from') + 1]) if '--from' in opts else 0
    global VERBOSE
    VERBOSE = '--verbose' in opts

    def on_event(d, toks):
        cnt[0] += 1
        if quiet or d.s.steps < first:
            return
        if thr:
            sig = shape(toks, d.s.st, thr)
            if sig not in recent:
                print(d.s.steps, fmt(toks, d.s.st))
                sys.stdout.flush()
            recent.append(sig)
            del recent[:-6]
        elif every and cnt[0] % every == 0 or not every:
            print(d.s.steps, fmt(toks, d.s.st))

    d = Driver(sim, accel)
    d.run(maxsteps, on_event)
    s = d.s
    print("HALT" if s.halt else "END", s.steps, "events", d.ev, "moves", d.moves, "jumps", d.jumps, "rules", d.nrules,
          "failed", d.nfail)
    print("TAPE", fmt(compress(s.flat()), s.st))


if __name__ == "__main__":
    main(sys.argv)
