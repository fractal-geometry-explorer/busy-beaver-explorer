"""Digit-level engine for the wall-visit recursion G, with run tokens and automatic cycle rules.

A word of pairs X = 10, Y = 11 is a list of digits (run lengths of Y between X's; the last digit is the trailing run).
    G([a])            = 0^a 2
    G([a, k])         = EVENT (the head reaches the blank right end in D)
    G([a, 0, u0, U])  = 0^a (3+u0) U
    G([a, k, u0, U])  = 0^a (1 + G^k((2+u0) U))
With h(T) = G(0 T) (a "hit"):  G(a T) = 0^a h(T),  h(0 T) = 3 + T,  h(k T) = 1 + G^k(2 + T),  h(1 0 T) = 1 0 h(T).

Tokens (cons list, T = (tok, tail) or None): an int >= 1 (a digit), ('Z', m) = 0^m, ('R', n) = (1 0)^n,
('P', n, w) = w^n for a tuple of digits w, ('O', c) = an opaque rest that has received c hits (rule discovery only),
('E', T) = the rest T, known to answer its next hit with an event.

Rules are found by running the recursion with symbolic counts (class Lin: every comparison is recorded as a linear
condition, so a rule is applied only while its conditions hold):
  cycle rules     op^p(prefix[n] X) = (1 0)^e prefix[n + d] h^c(X)                    (discover, try_at)
  run rules       h(k w^n T) = E^(n-1) h(k w T),  or  h(k w T) = E h(k' T)            (run_discover)
  recursion rules h(prefix[n] X) = F h(prefix[n + d] h^c(X))                          (rdiscover, try_rrule)
C[0] counts machine steps with the constants CST (see calibrate.py).  After an event, EVTRACE holds the open
sub-tape frames (S, done, W, cost, k): G^done(S) = W and the next visit of W is the event.
"""
import sys
sys.setrecursionlimit(30000000)


class Event(Exception):
    pass


class Opaque(Exception):
    pass


class Budget(Exception):
    pass


# ------------------------------------------------------------------ symbolic counts (rule discovery)
class Rec:
    cons = None          # list of (coef dict, const, sense, thr) while recording
    work = 0
    limit = 0


class Lin:
    __slots__ = ("v", "c", "k")

    def __init__(self, v, c, k):
        self.v, self.c, self.k = v, c, k          # concrete value, coefficients {var: coef}, constant

    @staticmethod
    def var(i, value):
        return Lin(value, {i: 1}, 0)

    def __add__(self, o):
        if isinstance(o, Lin):
            c = dict(self.c)
            for a, b in o.c.items():
                c[a] = c.get(a, 0) + b
            return Lin(self.v + o.v, c, self.k + o.k)
        return Lin(self.v + o, self.c, self.k + o)
    __radd__ = __add__

    def __sub__(self, o):
        if isinstance(o, Lin):
            c = dict(self.c)
            for a, b in o.c.items():
                c[a] = c.get(a, 0) - b
            return Lin(self.v - o.v, c, self.k - o.k)
        return Lin(self.v - o, self.c, self.k - o)

    def __mul__(self, o):
        if o == 1:
            return self
        return Lin(self.v * o, {a: b * o for a, b in self.c.items()}, self.k * o)
    __rmul__ = __mul__

    def _rec(self, sense, thr):
        Rec.cons.append((self.c, self.k, sense, thr))

    def _cmp(self, o):
        if isinstance(o, Lin):
            return (self - o), 0
        return self, o

    def __ge__(self, o):
        f, t = self._cmp(o)
        if f.v >= t:
            f._rec(1, t); return True
        f._rec(-1, t - 1); return False

    def __gt__(self, o):
        f, t = self._cmp(o)
        if f.v > t:
            f._rec(1, t + 1); return True
        f._rec(-1, t); return False

    def __le__(self, o):
        f, t = self._cmp(o)
        if f.v <= t:
            f._rec(-1, t); return True
        f._rec(1, t + 1); return False

    def __lt__(self, o):
        f, t = self._cmp(o)
        if f.v < t:
            f._rec(-1, t - 1); return True
        f._rec(1, t); return False

    def __eq__(self, o):
        f, t = self._cmp(o)
        if f.v == t:
            f._rec(1, t); f._rec(-1, t); return True
        if f.v > t:
            f._rec(1, t + 1)
        else:
            f._rec(-1, t - 1)
        return False

    def __ne__(self, o):
        return not self.__eq__(o)

    __hash__ = None

    def pin(self):
        self._rec(1, self.v); self._rec(-1, self.v)
        return self.v

    def __repr__(self):
        return "Lin(%d)" % self.v


def conc(x):
    return x.pin() if isinstance(x, Lin) else x


# ------------------------------------------------------------------ constructors
def zcons(m, T):
    if m == 0:
        return T
    if T is not None:
        t = T[0]
        if type(t) is tuple and t[0] == 'Z':
            return (('Z', m + t[1]), T[1])
    return (('Z', m), T)


W100 = (1, 0, 0)


def rcons(n, T):
    if n == 0:
        return T
    if T is not None:
        t = T[0]
        if type(t) is tuple:
            if t[0] == 'R':
                return (('R', n + t[1]), T[1])
            if t[0] == 'Z' and T[1] is not None:
                u = T[1][0]
                if type(u) is tuple and u[0] == 'P' and u[2] == W100:
                    if n == 1 and t[1] == 1:
                        return (('P', u[1] + 1, W100), T[1][1])
                elif type(u) is tuple and u[0] == 'R' and T[1][1] is not None:
                    v = T[1][1][0]
                    if type(v) is tuple and v[0] == 'Z' and n == 1 and t[1] == 1 and u[1] == 1:
                        return pcons(2, W100, zcons(v[1] - 1, T[1][1][1]))
    return (('R', n), T)


def primitive(w):
    L = len(w)
    for p in range(1, L):
        if L % p == 0 and w[:p] * (L // p) == w:
            return w[:p], L // p
    return w, 1


def econs(n, E, T):
    """prepend E^n (E a tuple of digits)"""
    E, r = primitive(tuple(E))
    n = n * r
    if E == (1, 0):
        return rcons(n, T)
    if E == (0,):
        return zcons(n, T)
    return pcons(n, E, T)


def pcons(n, w, T):
    if n == 0:
        return T
    if T is not None:
        t = T[0]
        if type(t) is tuple and t[0] == 'P' and t[2] == w:
            return (('P', n + t[1], w), T[1])
        if w == W100 and type(t) is tuple and t[0] == 'R' and T[1] is not None:
            v = T[1][0]
            if type(v) is tuple and v[0] == 'Z' and t[1] == 1:
                return pcons(n + 1, w, zcons(v[1] - 1, T[1][1]))
    return (('P', n, w), T)


def dcons(d, T):
    """prepend the digit d >= 1"""
    if T is not None and d == 1:
        t = T[0]
        if type(t) is tuple and t[0] == 'Z':
            m = t[1]
            if m == 1:
                return rcons(1, T[1])
            return rcons(1, (('Z', m - 1), T[1]))
    return (d, T)


def untok(T):
    """(first digit, rest) of a nonempty list; the first digit as a number (0 for Z)"""
    t, tail = T
    if type(t) is tuple:
        k = t[0]
        if k == 'Z':
            m = t[1]
            return 0, (tail if m == 1 else (('Z', m - 1), tail))
        if k == 'R':
            n = t[1]
            return 1, zcons(1, tail if n == 1 else (('R', n - 1), tail))
        if k == 'E':
            return untok(t[1])
        if k == 'P':
            n = t[1]
            w = t[2]
            rest = tail if n == 1 else (('P', n - 1, w), tail)
            for d in reversed(w[1:]):
                rest = zcons(1, rest) if d == 0 else dcons(d, rest)
            return w[0], rest
        raise Opaque()
    return t, tail


def add(c, T):
    d, rest = untok(T)
    return dcons(d + c, rest)


# ------------------------------------------------------------------ step costs
C = [0]                                   # machine steps of the operations done (int, or Lin in a discovery)
CST = {'g0': 0, 'cend': 0, 'c1': 0, 'd1': 0, 'd0': 0}     # per machine, see calibrate.py


# ------------------------------------------------------------------ the recursion
EVTRACE = []          # after an event: the nested sub-tape frames (S, done, W, cost, k), innermost first
EVLEAF = [None]


def leaf(kind):
    del EVTRACE[:]
    EVLEAF[0] = kind
    raise Event()


def h(T):
    if T is None:
        C[0] = C[0] + CST['cend']
        return (2, None)
    if RD[0] is not None:
        r = rd_check(T)
        if r is not None:
            return r
    t, tail = T
    if type(t) is tuple:
        k = t[0]
        if k == 'R':
            C[0] = C[0] + t[1] * CST['cR']
            return rcons(t[1], h(tail))
        if k == 'O' or k == 'QY':
            return ((k, t[1] + 1), tail)
        if k == 'E':
            leaf('wrap')           # known: the next hit of this rest is an event
        if k == 'P' and tail is not None and FZ[0]:
            cf = frozen_cost(t[2])
            if cf is not None:
                # h(w^n X) = w^n h(X) for a frozen word w (checked symbolically, any nonempty X)
                C[0] = C[0] + t[1] * cf
                return pcons(t[1], t[2], h(tail))
        if k == 'Z':
            m = t[1]
            rest = tail if m == 1 else (('Z', m - 1), tail)
            if rest is None:
                leaf('end')
            C[0] = C[0] + CST['c1']
            return add(3, rest)
        t, tail = untok(T)
        if t == 0:
            if tail is None:
                leaf('end')
            C[0] = C[0] + CST['c1']
            return add(3, tail)
    if tail is None:
        leaf('end')
    th = tail[0]
    if type(th) is tuple:
        kk = th[0]
        if kk == 'Q':
            return (('QD', t), tail[1])
        if (kk == 'P' or kk == 'R') and th[1] >= 3:
            w = th[2] if kk == 'P' else (1, 0)
            tc = conc(t)
            E = RUNRULES.get((tc, w), 0)
            if E == 0:
                E = run_discover(tc, w)
            if E is not None:
                n = th[1]
                if len(E) == 3:          # h(k w T) = E h(k' T): peel one unit
                    C[0] = C[0] + E[1]
                    restw = (('P', n - 1, w), tail[1]) if kk == 'P' else (('R', n - 1), tail[1])
                    return build(list(E[0]), h((E[2], restw)))
                one = (('P', 1, w), tail[1]) if kk == 'P' else (('R', 1), tail[1])
                C[0] = C[0] + (n - 1) * E[1]
                return econs(n - 1, E[0], h((t, one)))
    if Rec.cons is None and len(STACK) > RDEPTH[0] and ACCEL[0]:
        if FZ[0] and FUNF[0] and type(t) is int and t in FIDX:
            r = frozen_unfolded(t, tail)
            if r is not None:
                return r
        r = try_rrule(T)
        if r is not None:
            return r
    C[0] = C[0] + CST['d1'] * conc(t) + CST['d0']
    S = add(2, tail)
    c_before = C[0]
    W, done = gpow(t, S)
    if done is not True:
        if Rec.cons is None:
            EVTRACE.append((S, done, W, C[0] - c_before, t))
        raise Event()
    return add(1, W)


def G(W):
    t, tail = W
    if type(t) is tuple:
        k = t[0]
        if k == 'Z':
            m = t[1]
            C[0] = C[0] + CST['g0']
            return h(tail if m == 1 else (('Z', m - 1), tail))
        if k == 'R':
            n = t[1]
            C[0] = C[0] + (CST['g0'] + 4)
            return zcons(1, h(zcons(1, tail if n == 1 else (('R', n - 1), tail))))
        t, tail = untok(W)
        if t == 0:
            C[0] = C[0] + CST['g0']
            return h(tail)
    C[0] = C[0] + t * 4 + CST['g0']
    return zcons(t, h(tail))


RUNRULES = {}
RUN = [None]

# ------------------------------------------------------------------ frozen words
# A word w of digits is frozen when h(w X) = w h(X) for every nonempty X, at a fixed cost: found by running h on
# w followed by an opaque rest (any look into the rest aborts), so the law holds for every X.  Frozen words are
# stripped from the front of a run of hits (like the units 1 0), and a cycle rule may emit one per cycle.
FZ = [__import__('os').environ.get('NOFROZEN') is None]
FROZEN = {}
FPC = {}
FMAX = 400           # longest frozen word tried (digits)
FEMIT = 40           # most tokens of an emitted frozen word


def frozen_cost(w):
    """steps of one hit crossing the frozen word w (a tuple of digits), or None if w is not frozen"""
    r = FROZEN.get(w, 0)
    if r != 0:
        return r
    FROZEN[w] = None
    if not w or len(w) > FMAX:
        return None
    T = build(to_tokens(from_digits(list(w))), (('O', 0), None))
    saved = Rec.cons, Rec.work, Rec.limit, C[0]
    Rec.cons = []
    Rec.work = 0
    Rec.limit = 4000
    C[0] = 0
    res = None
    try:
        out = to_tokens(h(T))
        if out and out[-1] == ('O', 1) and not isinstance(C[0], Lin):
            if tok_digits(out[:-1], len(w) + 2) == tuple(w):
                res = C[0]
    except (Opaque, Budget, Event):
        res = None
    finally:
        Rec.cons, Rec.work, Rec.limit, C[0] = saved
    FROZEN[w] = res
    STATS["frozen"] = STATS.get("frozen", 0) + (res is not None)
    if res is not None and len(w) <= FUNMAX:
        L = FIDX.setdefault(w[0], [])
        L.append(w)
        L.sort(key=len, reverse=True)          # longest first
        for r in range(1, len(w)):
            if w[r] != 0 and len(w) >= 4:
                frozen_cost(w[r:] + w[:r])     # rotations of a frozen word are often frozen too
    return res


# A frozen word written out as digits (not as a run token): a hit crosses it at its fixed cost, and the word is
# folded into a run token, so that it merges with a run of the same word that follows (pcons).
FUNF = [__import__('os').environ.get('NOFUNF') is None]
FUNMAX = 40          # longest frozen word looked for in digit form
FIDX = {}            # first digit -> frozen words (found by frozen_cost)


def frozen_match(t0, tail):
    """(n, u, R) if t0 tail = u^n R for a frozen word u (n = 1 with u in digit form, or a v^n Y = u2^n a Y with
    a = u[:i] the digits read so far, v = b a and u2 = a b frozen), R nonempty; else None.  No steps are counted."""
    for u in FIDX[t0]:
        R = tail
        ok = True
        try:
            for i in range(1, len(u)):
                if R is None:
                    ok = False; break
                x = R[0]
                if type(x) is tuple:
                    if x[0] == 'P' and type(x[1]) is int and R[1] is not None:
                        # a = u[:i] before a run v^n with v = b a: a (b a)^n Y = (a b)^n a Y, if a b is frozen
                        v = x[2]
                        L = len(v) - i
                        if L > 0 and v[L:] == u[:i]:
                            u2 = u[:i] + v[:L]
                            if u2 == u or frozen_cost(u2) is not None:
                                Y = R[1]
                                for d in reversed(u[1:i]):
                                    Y = zcons(1, Y) if d == 0 else dcons(d, Y)
                                STATS["funfrun"] = STATS.get("funfrun", 0) + 1
                                return x[1], u2, (t0, Y)
                    if x[0] not in ('Z', 'R', 'P'):
                        ok = False; break
                e, R = untok(R)
                if e != u[i]:
                    ok = False; break
        except Opaque:
            ok = False
        if ok and R is not None:
            STATS["funf"] = STATS.get("funf", 0) + 1
            return 1, u, R
    return None


def frozen_unfolded(t0, tail):
    """h(t0 tail) when t0 tail begins with a frozen word u in digit form: u h(X), with u folded into a run token.
    The hit then crosses, in a loop (not by recursion), every following unit (1 0)^n, frozen run token and frozen
    word in digit form, and h is called once on what is left."""
    m = frozen_match(t0, tail)
    if m is None:
        return None
    pre = []
    while m is not None:
        n, u, R = m
        C[0] = C[0] + n * FROZEN[u]
        pre.append(('P', n, u))
        while R[1] is not None:
            x = R[0]
            if type(x) is not tuple:
                break
            if x[0] == 'R':
                C[0] = C[0] + x[1] * CST['cR']
            elif x[0] == 'P':
                cf = frozen_cost(x[2])
                if cf is None:
                    break
                C[0] = C[0] + x[1] * cf
            else:
                break
            pre.append(x)
            R = R[1]
        m = frozen_match(R[0], R[1]) if type(R[0]) is int and R[0] in FIDX and R[1] is not None else None
    out = h(R)
    for x in reversed(pre):
        out = rcons(x[1], out) if x[0] == 'R' else pcons(x[1], x[2], out)
    return out


def tok_digits(toks, limit=FMAX):
    """the digits of a list of concrete tokens, or None (symbolic, opaque or too long)"""
    out = []
    for t in toks:
        if isinstance(t, Lin):
            return None
        if type(t) is tuple:
            if t[0] not in ('Z', 'R', 'P') or isinstance(t[1], Lin):
                return None
            n = t[1]
            w = (0,) if t[0] == 'Z' else (1, 0) if t[0] == 'R' else t[2]
            if n * len(w) > limit:
                return None
            out.extend(w * n)
        else:
            out.append(t)
        if len(out) > limit:
            return None
    return tuple(out)


def frozen_emit(F):
    """(digits, crossing cost) if the concrete token list F is a frozen word, else None"""
    d = tok_digits(F)
    if not d:
        return None
    cf = frozen_cost(d)
    if cf is None:
        return None
    return (d, cf)


def frozen_prefix(T):
    """(number of tokens, cost of a hit crossing them) for the longest frozen prefix of T (at most 10 whole
    tokens, the rest nonempty), or None"""
    t0 = T[0]
    if type(t0) is tuple:
        if t0[0] == 'P':
            cf = frozen_cost(t0[2])
            if cf is not None:
                return 1, t0[1] * cf
        if t0[0] not in ('Z',):
            return None
    toks = []
    node = T
    while node is not None and node[1] is not None and len(toks) < 10:
        t = node[0]
        if type(t) is tuple and (t[0] not in ('Z', 'R', 'P') or t[1] > 64):
            break
        toks.append(t)
        node = node[1]
    full = tuple(toks)
    r = FPF.get(full, 0)
    if r != 0:
        return r
    best = None
    for i in range(len(toks), 0, -1):
        key = tuple(toks[:i])
        r = FPC.get(key, 0)
        if r == 0:
            d = tok_digits(toks[:i])
            r = frozen_cost(d) if d else None
            FPC[key] = r
        if r is not None:
            best = (i, r)
            break
    if len(FPF) > 200000:
        FPF.clear()
    FPF[full] = best          # deterministic in the tokens (frozen_cost is cached), so the answer can be cached
    return best


FPF = {}

# ------------------------------------------------------------------ recursion rules
# h(pre[n] X) = F h(pre[n + deltas] h^c(X)): a frame whose last sub-visit opens the same frame again (this is how a
# level is turned into a run of fuel).  Found by running h on pre[n] Omega with symbolic counts, and stopping at
# the first inner hit whose word has the same shape.
RDEPTH = [int(__import__('os').environ.get('RDEPTH', '300'))]
RD = [None]
RRULES = {}
RNEG = {}
RLEN = 9


def rd_check(T):
    rd = RD[0]
    if rd['first']:
        rd['first'] = False
        return None
    toks = rd['toks']
    ps = rd['ps']
    node = T
    deltas = []
    extra = []
    for i, t0 in enumerate(toks):
        if node is None:
            return None
        t = node[0]
        if type(t0) is tuple:
            if not (type(t) is tuple and t[0] == t0[0] and t[2:] == t0[2:]):
                return None
            val = t[1]
        elif ps[i] is None:
            if isinstance(t, Lin) or type(t) is tuple or t != t0:
                return None
            deltas.append(0)
            node = node[1]
            continue
        else:
            if type(t) is tuple:
                return None
            val = t
        if isinstance(val, Lin):
            if val.c != {i: 1}:
                return None
            deltas.append(val.k)
        elif val == ps[i]:
            extra.append(({i: 1}, 0, 1, val)); extra.append(({i: 1}, 0, -1, val))
            deltas.append(0)
        else:
            return None
        node = node[1]
    if node is None or not (type(node[0]) is tuple and node[0][0] == 'O') or node[1] is not None:
        return None
    if rd['found'] is not None:
        raise Opaque()
    rd['found'] = (deltas, node[0][1], extra)
    return (('QH',), None)


def rdiscover(toks):
    STATS["rdisc"] = STATS.get("rdisc", 0) + 1
    ps = params(toks)
    if all(p is None for p in ps):
        return None
    sym = [None if p is None else Lin.var(i, p) for i, p in enumerate(ps)]
    T = build_raw(with_params(toks, sym), (('O', 0), None))
    saved = Rec.cons, Rec.work, Rec.limit, C[0]
    Rec.cons = []
    Rec.work = 0
    Rec.limit = 6000
    C[0] = 0
    RD[0] = {'toks': toks, 'ps': ps, 'first': True, 'found': None}
    try:
        out = to_tokens(h(T))
        f = RD[0]['found']
        if f is None or not out or out[-1] != ('QH',):
            return None
        F = out[:-1]
        for x in F:
            if type(x) is tuple:
                if x[0] not in ('Z', 'R', 'P') or isinstance(x[1], Lin):
                    return None
            elif isinstance(x, Lin):
                return None
        if not F:
            return None
        deltas, c, extra = f
        if all(d == 0 for d in deltas):
            return None
        # the cost of one level: everything before the inner hit (the rest of the outer frame costs nothing more)
        total = C[0]
        cost = total
        if isinstance(cost, Lin):
            cost = (dict(cost.c), cost.k)
        else:
            cost = ({}, cost)
        cons = [(dict(cf), k, s, thr) for cf, k, s, thr in Rec.cons] + extra
        return (tuple(to_digits(build_raw(F, None))), deltas, c, cons, cost)
    except (Opaque, Budget, Event):
        return None
    finally:
        RD[0] = None
        Rec.cons, Rec.work, Rec.limit, C[0] = saved


def try_rrule(T):
    toks, rest = flat(T, RLEN)
    # shapes, counts and capped counts of all prefixes at once (the same values as shape_of / params of each
    # prefix, computed once instead of once per prefix length)
    psa = params(toks)
    sha = shape_of(toks)
    capa = tuple(p if p is None or p < 64 else 64 for p in psa)
    for i in range(2, len(toks) + 1):
        if i == len(toks) and rest is None:
            break
        key = sha[:i]
        rules = RRULES.get(key)
        if not rules:
            nk = (key, capa[:i])
            if nk in RNEG:
                continue
        pre = toks[:i]
        ps = psa[:i]
        if rules is None:
            rules = RRULES[key] = []
        found = None
        for rule in rules:
            mc = max_cycles((1, rule[2], 0, rule[1], rule[3], rule[4]), ps)
            if mc is not None and mc >= 1:
                found = (rule, mc); break
        if found is None and len(rules) < 4:
            nk = (key, capa[:i])
            if nk in RNEG:
                continue
            rule = rdiscover(pre)
            if rule is None:
                RNEG[nk] = 1
                continue
            rules.append(rule)
            mc = max_cycles((1, rule[2], 0, rule[1], rule[3], rule[4]), ps)
            if mc is not None and mc >= 1:
                found = (rule, mc)
        if found is None:
            continue
        rule, j = found
        F, deltas, c, cons, cost = rule
        tail = build_raw(toks[i:], rest)
        c0 = C[0]
        if c > 0:
            tail, d2 = hpow(c * j, tail)
            if d2 is not True:
                C[0] = c0
                return None
        cf, ck = cost
        f0 = ck
        slope = 0
        for iv, a in cf.items():
            f0 += a * ps[iv]
            slope += a * deltas[iv]
        C[0] = C[0] + j * f0 + slope * (j * (j - 1) // 2)
        newps = [None if a is None else a + j * d for a, d in zip(ps, deltas)]
        STATS["rjumps"] = STATS.get("rjumps", 0) + 1
        inner = h(build(with_params(pre, newps), tail))
        return econs(j, F, inner)
    return None


def run_discover(k, w):
    """h(k w T) = E h(k T) for every T?  returns E (a tuple of digits) or None"""
    T = (('Q',), None)
    for d in reversed(w):
        T = (('Z', 1), T) if d == 0 else (d, T)
    T = (k, T)
    saved = Rec.cons, Rec.work, Rec.limit, C[0]
    Rec.cons = []
    Rec.work = 0
    Rec.limit = 3000
    C[0] = 0
    E = None
    try:
        out = to_tokens(h(T))
        if out and type(out[-1]) is tuple and out[-1][0] == 'QD' and out[-1][1] == k:
            E = tuple(to_digits(build_raw(out[:-1], None)))
            if not E:
                E = None
            else:
                E = (E, C[0])
        elif out and type(out[-1]) is tuple and out[-1][0] == 'QD' and len(out) >= 2 \
                and not any(type(x) is tuple and x[0] in ('Q', 'QD', 'O') for x in out[:-1]):
            E = (tuple(out[:-1]), C[0], out[-1][1])
    except (Opaque, Budget, Event):
        E = None
    finally:
        Rec.cons, Rec.work, Rec.limit, C[0] = saved
    RUNRULES[(k, w)] = E
    return E


# ------------------------------------------------------------------ powers, with cycle rules
THRESH = int(__import__('os').environ.get('THRESH', '24'))   # use rules when at least this many applications remain
LMAX = 14            # longest prefix (tokens) tried for a rule
DMAX = [int(__import__('os').environ.get('DMAX', '14'))]  # longest prefix for which a new rule is looked for
DLIMIT = [int(__import__('os').environ.get('DLIMIT', '600'))]   # work budget of one cycle-rule discovery (was 1500)
DREM = [int(__import__('os').environ.get('DREM', '4096'))]  # prefixes longer than 6 tokens: only when this many applications remain
PMAX = 40            # longest cycle
BIGDIGIT = 12        # digits from here on are symbolic in a rule
RULES = {}           # (op name, shape) -> list of rules
STATS = {"jumps": 0, "explicit": 0, "disc": 0, "disc_ok": 0}
ACCEL = [True]


def gpow(q, T):
    """G^q(T): returns (T', True), or (T', done) with done < q complete visits when visit done+1 is an event"""
    return power(G, 'G', q, T)


def hpow(q, T):
    return power(h, 'h', q, T)


def flat(T, n):
    out = []
    while T is not None and len(out) < n:
        t = T[0]
        if type(t) is tuple and t[0] == 'E':
            break
        out.append(t); T = T[1]
    return out, T


def strip_e(T):
    """remove the 'E' wrappers (canonical list)"""
    toks = []
    found = False
    while T is not None:
        t = T[0]
        if type(t) is tuple and t[0] == 'E':
            T = t[1]; found = True
            continue
        toks.append(t); T = T[1]
    return build(toks, None) if found else build_raw(toks, None)


def shape_of(toks):
    s = []
    for t in toks:
        if type(t) is tuple:
            s.append(t[0] if t[0] != 'P' else t[2])
        elif t >= BIGDIGIT:
            s.append('D')
        else:
            s.append(t)
    return tuple(s)


def power(op, name, q, T):
    q = conc(q)
    if NEST[0] and T is not None:
        if Rec.cons is not None:
            if HYP[0] is not None:
                r = hyp_match(name, q, T)
                if r is not None:
                    return r, True
        elif ACCEL[0] and len(STACK) > NDEPTH[0] and nsample():
            r = try_nest(op, name, q, T)
            if r is not None:
                return r
    fr = [name, q, 0, T, T]
    STACK.append(fr)
    T = None             # the frame (fr[3], fr[4]) and power_ hold the input; see DROP below
    # cost scoping: the frame counts its own steps from 0 and adds them to the caller's count when it ends (also on
    # an exception), so the snapshots taken inside it (c0, c_before) are of its own, small count and not of the
    # huge running total.  Exact: integer addition is associative.  SCOPE=0 restores the old global count.
    if SCOPE[0]:
        save = C[0]
        C[0] = 0
        try:
            return power_(op, name, q, fr[3], fr)
        finally:
            C[0] = save + C[0]
            STACK.pop()
    try:
        return power_(op, name, q, fr[3], fr)
    finally:
        STACK.pop()


STACK = []
DROP = [__import__('os').environ.get('NODROP') is None]
NDROP = [int(__import__('os').environ.get('NDROP', '1500'))]   # drop inputs of levels deeper than this


class Replay(Exception):
    """a carry that dropped its inputs (DROP) stopped early: redo the whole call without dropping"""


DROPPED = ('DROPPED',)
SCOPE = [__import__('os').environ.get('NOSCOPE') is None]


def power_(op, name, q, T, fr):
    done = 0
    in_disc = Rec.cons is not None
    leads = []
    stripped = []
    nojump = 0
    backoff = 64
    strip = name == 'h' and not in_disc
    while done < q:
        if strip:
            while T is not None and T[1] is not None:
                t0 = T[0]
                if type(t0) is tuple and t0[0] == 'R':
                    # the hits still to come cross these units: charged when the count of hits is known
                    leads.append((t0[1] * CST['cR'], done))
                    stripped.append(t0)
                    T = T[1]
                    continue
                if not FZ[0]:
                    break
                fp = frozen_prefix(T)
                if fp is None:
                    break
                ntok, cf = fp
                for _ in range(ntok):
                    stripped.append(T[0]); T = T[1]
                leads.append((cf, done))
        rem = q - done
        fr[2] = done; fr[3] = T
        if rem >= THRESH and not in_disc and not nojump and ACCEL[0] and T is not None:
            EVF[0] = False
            T = None
            r = try_jump(op, name, rem, fr)
            T = fr[3]
            if EVF[0]:
                nojump = backoff
                backoff *= 2
                EVF[0] = False
            if r is not None:
                T, adv = r
                done += adv
                continue
        if in_disc:
            Rec.work += 1
            if Rec.work > Rec.limit:
                raise Budget()
        c0 = C[0]
        if rem >= THRESH and not in_disc:
            LAST[0] = (name, rem, T, nojump)
        try:
            T = op(T)
        except Event:
            C[0] = c0
            for n, d0 in leads:
                C[0] = C[0] + n * (done - d0)
            return (build(stripped, T) if stripped else T), done
        done += 1
        if nojump:
            nojump -= 1
        STATS["explicit"] += 1
    for n, d0 in leads:
        C[0] = C[0] + n * (done - d0)
    return (build(stripped, T) if stripped else T), True


def params(toks):
    """the counts of the tokens (None for small digits)"""
    out = []
    for t in toks:
        if type(t) is tuple:
            out.append(t[1])
        elif t >= BIGDIGIT:
            out.append(t)
        else:
            out.append(None)
    return out


def with_params(toks, ps):
    out = []
    for t, p in zip(toks, ps):
        if p is None:
            out.append(t)
        elif type(t) is tuple:
            out.append((t[0], p) + t[2:])
        else:
            out.append(p)
    return out


def build(toks, tail):
    """the cons list toks ++ tail, through the smart constructors"""
    T = tail
    for t in reversed(toks):
        if type(t) is tuple:
            if t[0] == 'Z':
                T = zcons(t[1], T)
            elif t[0] == 'R':
                T = rcons(t[1], T)
            elif t[0] == 'P':
                T = pcons(t[1], t[2], T)
            else:
                T = (t, T)
        else:
            T = dcons(t, T)
    return T


def discover(op, name, toks, has_rest):
    """look for p with op^p(toks Omega) = R(e) toks' Omega_c, toks' = toks with shifted counts.
    returns (p, c, e, deltas, constraints) or None"""
    STATS["disc"] += 1
    ps = params(toks)
    sym = [None if p is None else Lin.var(i, p) for i, p in enumerate(ps)]
    T0 = with_params(toks, sym)
    sh = shape_of(toks)
    T = build_raw(T0, (('O', 0), None) if has_rest else None)
    Rec.cons = []
    Rec.work = 0
    Rec.limit = DLIMIT[0]
    csave = C[0]
    C[0] = 0
    try:
        for p in range(1, PMAX + 1):
            T = op(T)
            out, rest = flat(T, len(toks) + (2 + FEMIT if FZ[0] and name == 'h' else 2))
            # locate Omega
            c = None
            body = None
            for i, t in enumerate(out):
                if type(t) is tuple and t[0] == 'O':
                    c = t[1]; body = out[:i]; break
            if has_rest:
                if body is None:
                    continue
            else:
                if rest is not None:
                    continue
                body, c = out, 0
            e = 0
            if len(body) == len(toks) + 1 and name == 'h' and type(body[0]) is tuple and body[0][0] == 'R' \
                    and not isinstance(body[0][1], Lin):
                e = body[0][1]; body = body[1:]
            if len(body) > len(toks) and name == 'h' and not e and FZ[0]:
                F = body[:len(body) - len(toks)]
                fe = frozen_emit(F)
                if fe is not None:
                    e = fe; body = body[len(F):]
            if len(body) != len(toks):
                continue
            ok = True
            deltas = []
            extra = []
            for i, (t, t0) in enumerate(zip(body, toks)):
                if type(t0) is tuple:
                    if not (type(t) is tuple and t[0] == t0[0] and t[2:] == t0[2:]):
                        ok = False; break
                    val = t[1]
                elif ps[i] is None:
                    if isinstance(t, Lin) or type(t) is tuple or t != t0:
                        ok = False; break
                    deltas.append(0); continue
                else:
                    if type(t) is tuple:
                        ok = False; break
                    val = t
                if isinstance(val, Lin):
                    if val.c != {i: 1}:
                        ok = False; break
                    deltas.append(val.k)
                elif val == ps[i]:
                    extra.append(({i: 1}, 0, 1, val)); extra.append(({i: 1}, 0, -1, val))
                    deltas.append(0)
                else:
                    ok = False; break
            if not ok:
                continue
            cons = [(dict(cf), k, s, thr) for cf, k, s, thr in Rec.cons] + extra
            cost = C[0]
            if isinstance(cost, Lin):
                cost = (dict(cost.c), cost.k)
            else:
                cost = ({}, cost)
            return (p, c, e, deltas, cons, cost)
        return None
    except (Opaque, Budget, Event):
        return None
    finally:
        Rec.cons = None
        C[0] = csave


def build_raw(toks, tail):
    T = tail
    for t in reversed(toks):
        T = (t, T)
    return T


def max_cycles(rule, ps):
    """how many cycles of the rule can be applied in a row to counts ps (0 if its path conditions fail now)"""
    p, c, e, deltas, cons, cost = rule
    best = None
    for cf, k, s, thr in cons:
        val = k
        slope = 0
        for i, a in cf.items():
            val += a * ps[i]
            slope += a * deltas[i]
        if s == 1:
            if val < thr:
                return 0
            if slope < 0:
                b = (val - thr) // (-slope) + 1
                best = b if best is None else min(best, b)
        else:
            if val > thr:
                return 0
            if slope > 0:
                b = (thr - val) // slope + 1
                best = b if best is None else min(best, b)
    return best          # None = unbounded


NEG = {}


FULL = {}
LAST = [None]
SOFT = [False]
EVF = [False]


def try_jump(op, name, rem, fr):
    toks, rest = flat(fr[3], LMAX)
    hr = rest is not None
    box = [rest]
    rest = None
    fkey = (name, shape_of(toks), hr)
    f = FULL.get(fkey)
    if f is None:
        f = FULL[fkey] = [0, None, 0]          # full scans, candidate prefix lengths, calls
    f[2] += 1
    if f[1] is None or (f[2] % 512 == 0 and f[0] < 6):
        f[0] += 1
        cands = []
        res = None
        for i in range(1, len(toks) + 1):
            r = try_at(op, name, rem, toks, box, i)
            if RULES.get((name, shape_of(toks[:i]), (i < len(toks)) or hr)):
                cands.append(i)
            if r is not None:
                res = r
                break
            if EVF[0]:
                f[1] = sorted(set((f[1] or []) + cands))
                f[0] -= 1
                return None
        else:
            f[1] = cands
            return None
        f[1] = sorted(set((f[1] or []) + cands))
        return res
    for i in f[1]:
        r = try_at(op, name, rem, toks, box, i)
        if r is not None or EVF[0]:
            return r
    return None


def try_at(op, name, rem, toks, box, i):
    rest = box[0]
    has_rest = (i < len(toks)) or (rest is not None)
    pre = toks[:i]
    key = (name, shape_of(pre), has_rest)
    rules = RULES.get(key)
    if rules is None:
        rules = RULES[key] = []
    ps = params(pre)
    found = None
    for rule in rules:
        mc = max_cycles(rule, ps)
        if mc is None or mc >= 1:
            found = (rule, mc); break
    if found is None and len(rules) < 6 and i <= DMAX[0] and (i <= 6 or rem >= DREM[0]):
        nk = (key, tuple(p if p is None or p < 64 else 64 for p in ps))
        if nk in NEG:
            return None
        rule = discover(op, name, pre, has_rest)
        if rule is None:
            NEG[nk] = 1
            return None
        STATS["disc_ok"] += 1
        rules.append(rule)
        mc = max_cycles(rule, ps)
        if mc is None or mc >= 1:
            found = (rule, mc)
    if found is None:
        if rules:
            SOFT[0] = True
        return None
    rule, mc = found
    p, c, e, deltas, cons, cost = rule
    j = rem // p
    if mc is not None:
        j = min(j, mc)
    if j < 1:
        SOFT[0] = True
        return None
    tail = build_raw(toks[i:], rest)
    if c > 0:
        if tail is None:
            return None
        c0 = C[0]
        if DROP[0] and Rec.cons is None and len(STACK) > NDROP[0]:
            # deep in a carry through the levels: let go of this level's input while the hits are passed on, so
            # that each open level does not keep its own old copy of the whole rest (memory ~ depth^2).  The
            # input is needed again only if the carry stops early (an event); then the hook is redone without
            # dropping (Replay, caught in msim.try_hook).
            fr = STACK[-1]
            fr[3] = fr[4] = DROPPED
            box[0] = DROPPED
            rest = None
            tb = [tail]
            tail = None
            R2, d2 = power(h, 'h', c * j, tb.pop())
            if d2 is not True:
                STATS["replays"] = STATS.get("replays", 0) + 1
                raise Replay()
        else:
            R2, d2 = hpow(c * j, tail)
        if d2 is not True:
            EVF[0] = True
            j = d2 // c
            if j < 1:
                SOFT[0] = True
                C[0] = c0
                if d2 == 0 and not (type(tail[0]) is tuple and tail[0][0] == 'E'):
                    return build_raw(toks[:i], (('E', tail), None)), 0
                return None
            if d2 % c:
                C[0] = c0
                R2, d2 = hpow(c * j, tail)
                assert d2 is True
            else:
                R2 = (('E', R2), None)
    else:
        R2 = tail
    newps = [None if a is None else a + j * d for a, d in zip(ps, deltas)]
    T2 = build(with_params(pre, newps), R2)
    # steps of the j cycles made inside the prefix: sum over t < j of cost(ps + t deltas)
    cf, ck = cost
    f0 = ck
    slope = 0
    for iv, a in cf.items():
        f0 += a * ps[iv]
        slope += a * deltas[iv]
    C[0] = C[0] + j * f0 + slope * (j * (j - 1) // 2)
    if e and type(e) is tuple:
        # a frozen word F emitted once per cycle (in front of the prefix): cycle t's p hits cross the t copies
        # emitted before it, at cf steps a copy
        Fd, cf = e
        C[0] = C[0] + p * cf * (j * (j - 1) // 2)
        T2 = econs(j, Fd, T2)
        e = 0
    if e:
        # the emitted units are crossed by the later hits of the jump: cycle t emits e units at its end
        # (the cost of a cycle counts crossings of what it emitted itself); units emitted by earlier cycles
        # are crossed by every hit of the later ones: e * p * cR * (0 + 1 + ... + (j-1))
        C[0] = C[0] + e * p * CST['cR'] * (j * (j - 1) // 2)
        T2 = rcons(e * j, T2)
    STATS["jumps"] += 1
    return T2, p * j


# ------------------------------------------------------------------ nested frames
# A power op^q(A[n] X) whose computation opens the same power op^q(A[n + d] X) (same q, same prefix shape A, the
# same rest X untouched) as an inner frame, and then goes on working on the inner result: a recursion of depth
# ~n.  The law is found by running the outer frame with symbolic counts and an opaque rest, the inner frame
# answering with a word U ++ Y (U concrete, Y opaque): if the outer frame then ends with U ++ V ++ h^c(Y) (V
# concrete; frozen if c > 0), then by induction from a base level whose result starts with U,
#     op^q(A[n] X) = U ++ V^j ++ h^(c j)(Z),    where op^q(A[n + j d] X) = U ++ Z   (computed directly)
# for the j levels on which the recorded conditions hold.
NEST = [__import__('os').environ.get('NONEST') is None]
NDEPTH = [int(__import__('os').environ.get('NDEPTH', '200'))]
HYP = [None]
NCNT = [12345]
NRULES = {}


def nsample():
    # a deterministic pseudo-random sample of 1/16 of the deep power calls (a fixed period could alias with the
    # period of a nested recursion)
    x = (NCNT[0] * 1103515245 + 12345) & 0x7fffffff
    NCNT[0] = x
    return (x >> 16) & 15 == 0
NNEG = {}


def hyp_match(name, q, T):
    hyp = HYP[0]
    if name != hyp['name'] or q != hyp['q']:
        return None
    node = T
    for i, t0 in enumerate(hyp['toks']):
        if node is None:
            return None
        t = node[0]
        want = hyp['inner'][i]
        if want is None:
            if isinstance(t, Lin) or t != t0:
                return None
        else:
            if type(t0) is tuple:
                if not (type(t) is tuple and t[0] == t0[0] and t[2:] == t0[2:]):
                    return None
                val = t[1]
            else:
                if type(t) is tuple:
                    return None
                val = t
            if not (isinstance(val, Lin) and val.c == want.c and val.k == want.k):
                return None
        node = node[1]
    if node is None or node[0] != ('O', 0) or node[1] is not None:
        return None
    hyp['hits'] += 1
    if hyp['hits'] > 1:
        raise Opaque()
    return build(hyp['U'], (('QY', 0), None))


def nest_detect(name, q, T):
    """(prefix tokens of T, inner-outer deltas) if a frame of the stack is the same power on the same rest"""
    for k in range(len(STACK) - 1, max(-1, len(STACK) - 40), -1):
        fr = STACK[k]
        if fr[0] != name or fr[1] != q:
            continue
        A, B = fr[4], T
        if A is DROPPED:
            continue
        ta, tb = [], []
        while A is not None and B is not None and A is not B and len(ta) <= LMAX:
            ta.append(A[0]); tb.append(B[0])
            A, B = A[1], B[1]
        if A is not B or not ta or len(ta) > LMAX:
            continue
        if shape_of(ta) != shape_of(tb):
            continue
        pa, pb = params(ta), params(tb)
        ok = True
        for x, y, u, v in zip(pa, pb, ta, tb):
            if x is None and u != v:
                ok = False
            if type(u) is tuple and u[2:] != v[2:]:
                ok = False
        if not ok or pa == pb:
            continue
        return tb, [None if x is None else y - x for x, y in zip(pa, pb)]
    return None


def try_nest(op, name, q, T):
    toks, rest = flat(T, LMAX)
    rules = NRULES.get((name, q))
    if rules:
        for rule in rules:
            n = rule['len']
            if n > len(toks) or shape_of(toks[:n]) != rule['shape']:
                continue
            if any(type(t) is tuple and t[2:] != u[2:] for t, u in zip(toks[:n], rule['toks'])):
                continue
            r = apply_nest(op, name, q, rule, toks[:n], build_raw(toks[n:], rest))
            if r is not None:
                return r
    d = nest_detect(name, q, T)
    if d is None:
        return None
    A, deltas = d
    key = (name, q, shape_of(A), tuple(deltas), tuple(t[2:] if type(t) is tuple else () for t in A))
    if key in NNEG:
        return None
    STATS["ndisc"] = STATS.get("ndisc", 0) + 1
    tail = build_raw(toks[len(A):], rest)
    rule = nest_discover(op, name, q, A, deltas, tail)
    if rule is None:
        NNEG[key] = 1
        return None
    STATS["ndisc_ok"] = STATS.get("ndisc_ok", 0) + 1
    NRULES.setdefault((name, q), []).append(rule)
    return apply_nest(op, name, q, rule, A, tail)


def nest_levels(rule, ps):
    return max_cycles((1, 0, 0, rule['deltas'], rule['cons'], None), ps)


def base_params(ps, deltas, j):
    return [None if a is None else a + j * d for a, d in zip(ps, deltas)]


def nest_discover(op, name, q, A, deltas, tail):
    ps = params(A)
    # a probe base: as many levels as keep every count >= 1
    j = None
    for a, d in zip(ps, deltas):
        if a is not None and d < 0:
            b = (a - 1) // (-d)
            j = b if j is None else min(j, b)
    if not j:
        return None
    c0 = C[0]
    Rb, done = power(op, name, q, build(with_params(A, base_params(ps, deltas, j)), tail))
    C[0] = c0
    if done is not True:
        return None
    btoks = flat(Rb, 40)[0]
    for L in (2, 4, 8, 12, 16, 24, 32, 48):
        Ud = []
        for t in btoks:
            dd = tok_digits([t], 64)
            if dd is None:
                break
            Ud.extend(dd)
            if len(Ud) >= L:
                break
        if len(Ud) < L:
            break
        Ud = Ud[:L]
        rule = nest_symbolic(op, name, q, A, ps, deltas, Ud)
        if rule is not None:
            return rule
    return None


def nest_symbolic(op, name, q, A, ps, deltas, Ud):
    sym = [None if p is None else Lin.var(i, p) for i, p in enumerate(ps)]
    T = build_raw(with_params(A, sym), (('O', 0), None))
    inner = [None if p is None else p + d for p, d in zip(sym, deltas)]
    saved = Rec.cons, Rec.work, Rec.limit, C[0], HYP[0]
    Rec.cons = []
    Rec.work = 0
    Rec.limit = 20000
    C[0] = 0
    U = to_tokens(from_digits(list(Ud))) if Ud else []
    HYP[0] = {'name': name, 'q': q, 'toks': A, 'inner': inner, 'U': U, 'hits': 0}
    try:
        R, done = power_(op, name, q, T, [name, q, 0, T, T])
        if done is not True or HYP[0]['hits'] != 1:
            return None
        out = to_tokens(R)
        if not out or type(out[-1]) is not tuple or out[-1][0] != 'QY':
            return None
        c = out[-1][1]
        dg = tok_digits(out[:-1], 100000)
        if dg is None or tuple(dg[:len(Ud)]) != tuple(Ud):
            return None
        V = tuple(dg[len(Ud):])
        cf = 0
        if c > 0 and V:
            cf = frozen_cost(V)
            if cf is None:
                return None
        cost = C[0]
        cost = (dict(cost.c), cost.k) if isinstance(cost, Lin) else ({}, cost)
        cons = [(dict(cf_), k, s_, thr) for cf_, k, s_, thr in Rec.cons]
        return {'len': len(A), 'shape': shape_of(A), 'toks': list(A), 'deltas': deltas, 'U': tuple(Ud), 'V': V,
                'c': c, 'cf': cf, 'cons': cons, 'cost': cost}
    except (Opaque, Budget, Event):
        return None
    finally:
        Rec.cons, Rec.work, Rec.limit, C[0], HYP[0] = saved


def apply_nest(op, name, q, rule, A, tail):
    ps = params(A)
    deltas = rule['deltas']
    j = nest_levels(rule, ps)
    if j is None or j < 1:
        return None
    c0 = C[0]
    Rb, done = power(op, name, q, build(with_params(A, base_params(ps, deltas, j)), tail))
    if done is not True:
        C[0] = c0
        return None
    # split the base result into U ++ Z
    Ud = rule['U']
    Z = Rb
    got = []
    while len(got) < len(Ud):
        if Z is None:
            C[0] = c0
            return None
        d, Z = untok(Z)
        got.append(d)
    if tuple(got) != Ud:
        C[0] = c0
        return None
    c = rule['c']
    if c:
        if Z is None:
            C[0] = c0
            return None
        Z, d2 = hpow(c * j, Z)
        if d2 is not True:
            C[0] = c0
            return None
        C[0] = C[0] + c * rule['cf'] * (j * (j - 1) // 2)
    cf, ck = rule['cost']
    f0 = ck
    slope = 0
    for iv, a in cf.items():
        f0 += a * ps[iv]
        slope += a * deltas[iv]
    # levels i = 0 .. j-1 (outermost first) have counts ps + i deltas
    C[0] = C[0] + j * f0 + slope * (j * (j - 1) // 2)
    STATS["njumps"] = STATS.get("njumps", 0) + 1
    R = econs(j, rule['V'], Z) if rule['V'] else Z
    return build(to_tokens(from_digits(list(Ud))), R), True


# ------------------------------------------------------------------ conversions
def from_digits(ds):
    T = None
    for d in reversed(ds):
        T = zcons(1, T) if d == 0 else dcons(d, T)
    return T


def to_tokens(T):
    out = []
    while T is not None:
        t = T[0]
        if type(t) is tuple and t[0] == 'E':
            T = t[1]
            continue
        out.append(t); T = T[1]
    return out


def to_digits(T, limit=10 ** 7):
    out = []
    while T is not None:
        t = T[0]
        if type(t) is tuple:
            if t[0] == 'Z':
                out.extend([0] * t[1])
            elif t[0] == 'R':
                out.extend([1, 0] * t[1])
            elif t[0] == 'P':
                out.extend(list(t[2]) * t[1])
            elif t[0] == 'E':
                T = t[1]
                continue
            else:
                raise Opaque()
        else:
            out.append(t)
        assert len(out) <= limit
        T = T[1]
    return out


def show(T, n=60):
    out = []
    for t in to_tokens(T)[:n]:
        if type(t) is tuple:
            if t[0] == 'P':
                out.append("(%s)^%s" % ("".join(map(str, t[2])), t[1]))
            else:
                out.append("%s%s" % ({"Z": "0^", "R": "(10)^", "O": "Om"}[t[0]], t[1]))
        else:
            out.append(str(t))
    return " ".join(out)


def Gref(ds):
    """the recursion on plain digit lists (reference); None at an event"""
    if len(ds) == 1:
        return [0] * ds[0] + [2]
    if len(ds) == 2:
        return None
    a, k = ds[0], ds[1]
    U = ds[2:]
    if k == 0:
        return [0] * a + [3 + U[0]] + U[1:]
    W = [2 + U[0]] + U[1:]
    for _ in range(k):
        W = Gref(W)
        if W is None:
            return None
    return [0] * a + [1 + W[0]] + W[1:]
