"""Hashlife over the carries of a phase, on the tail alone (prototype of lean/TailHash.lean).

`lean/ResetExc.lean` checks a phase by running each of its ~X/4 carries (`cc Eg wg`, one tail excursion
`Exc [0,0,1,1] A D [0,0,1,0]` followed by the cells 1010) on the actual tail.  That costs X/4 excursions per phase.
Here the same excursion simulator (a mirror of `lean/ExcSim.lean`) runs with *symbolic counts*: a run of the tail
whose count is at least TH stands for a variable, and the simulator records the linear conditions on the variables
that its decisions used (concolic: decisions are taken at the concrete values).  A *transform* says what 2^j carries
do to every tail whose first L runs have given words and (small) counts: the new first runs, with counts affine in
the old ones, under the recorded conditions.  Level j is two level-(j-1) transforms composed.

usage: python3 tailhash.py own|twin PHASES [TH]
"""
import sys, time

# ---------------------------------------------------------------- the machine
A, B, C, D, E, F = range(6)
TABLES = {
    'own': {(A, 0): (1, 'R', B), (A, 1): (0, 'L', F), (B, 0): (0, 'L', C), (B, 1): (0, 'R', E),
            (C, 0): (0, 'R', A), (C, 1): (1, 'L', D), (D, 0): (1, 'L', B), (D, 1): (0, 'L', D),
            (E, 0): (0, 'R', A), (E, 1): (1, 'R', C), (F, 0): (1, 'L', A)},
}
delta = TABLES['own']

WS = [(1, 0, 1, 0), (0, 1, 0, 1), (1, 1, 0, 0), (0, 1, 1, 0), (0, 0, 1, 1), (1, 0, 0, 1)]


class Fail(Exception):
    pass


class NeedMore(Exception):
    pass


# ---------------------------------------------------------------- linear forms over positions
# A Lin is a tuple (const, ((var, coeff), ...)) with vars sorted.  Values are ints.
def K(c):
    return (c, ())


def ladd(a, b):
    if not b[1]:
        return (a[0] + b[0], a[1])
    if not a[1]:
        return (a[0] + b[0], b[1])
    d = dict(a[1])
    for v, k in b[1]:
        d[v] = d.get(v, 0) + k
    return (a[0] + b[0], tuple(sorted((v, k) for v, k in d.items() if k)))


def lconst(a, c):
    return (a[0] + c, a[1])


def lneg(a):
    return (-a[0], tuple((v, -k) for v, k in a[1]))


def lev(a, env):
    s = a[0]
    for v, k in a[1]:
        s += k * env[v]
    return s


def lsub(a, m):
    """substitute var -> Lin m[var]"""
    out = K(a[0])
    for v, k in a[1]:
        e = m[v]
        out = ladd(out, (e[0] * k, tuple((w, c * k) for w, c in e[1])))
    return out


# ---------------------------------------------------------------- the symbolic excursion simulator
class Ctx:
    """env: concrete values of the variables; conds: Lins that must be >= 0."""
    __slots__ = ('env', 'conds')

    def __init__(self, env):
        self.env = env
        self.conds = []

    def val(self, n):
        return n[0] if not n[1] else lev(n, self.env)

    def is_zero(self, n):
        """decide n == 0 (n >= 0 assumed by the caller's conditions)"""
        if not n[1]:
            return n[0] == 0
        if lev(n, self.env) == 0:
            self.conds.append(lneg(n))      # -n >= 0
            return True
        self.conds.append(lconst(n, -1))    # n - 1 >= 0
        return False


def pushCells(u, s):
    return [((b,), K(1)) for b in u] + s


def popB(cx, s):
    """first cell and rest; None at the end of the side"""
    i = 0
    while i < len(s):
        w, n = s[i]
        if len(w) == 0 or cx.is_zero(n):
            i += 1
            continue
        a = w[0]
        rest = s[i + 1:]
        n1 = lconst(n, -1)
        rest = rest if cx.is_zero(n1) else [(w, n1)] + rest
        return a, pushCells(w[1:], rest)
    return None


def peelB(cx, j, s):
    u = []
    for _ in range(j):
        p = popB(cx, s)
        if p is None:
            return None
        u.append(p[0])
        s = p[1]
    return tuple(u), s


def peelLB(j, s):
    """first j cells when they are literal runs ([b], 1)"""
    if len(s) < j:
        return None
    u = []
    for i in range(j):
        w, n = s[i]
        if len(w) != 1 or n != (1, ()):
            return None
        u.append(w[0])
    return tuple(u), s[j:]


def rc(w, n, s):
    if s and s[0][0] == w:
        return [(w, ladd(n, s[0][1]))] + s[1:]
    return [(w, n)] + s


def nrm(s):
    if not s or s[0][1] != (1, ()):
        return s
    for w in WS:
        p = peelLB(len(w), s)
        if p is None or p[0] != w:
            continue
        s1 = p[1]
        if not s1:
            continue
        if s1[0][0] == w:
            return [(w, lconst(s1[0][1], 1))] + s1[1:]
        p2 = peelLB(len(w), s1)
        if p2 is not None and p2[0] == w:
            return rc(w, K(2), p2[1])
    return s


def bstep(c):
    l, r, q = c
    if not r:
        return None
    t = delta.get((q, r[0]))
    if t is None:
        return None
    w, d, s = t
    if d == 'R':
        return ((w,) + l, r[1:], s)
    if not l:
        return None
    return (l[1:], (l[0], w) + r[1:], s)


def bsteps(n, c):
    for _ in range(n):
        c = bstep(c)
        if c is None:
            return None
    return c


def findR(fuel, c):
    acc = 0
    while True:
        if not c[1]:
            return acc
        if fuel == 0:
            return None
        c = bstep(c)
        if c is None:
            return None
        fuel -= 1
        acc += 1


def findL(q0, u, fuel, c):
    acc = 0
    while fuel > 0:
        c = bstep(c)
        if c is None:
            return None
        acc += 1
        l2, r2, q2 = c
        if not l2 and q2 == q0 and r2[:len(u)] == u:
            return acc
        fuel -= 1
    return None


CROSS = {}


def cross_rule(kind, u, w, q):
    """the bounded run of one crossing (cached): returns written word or None"""
    key = (kind, u, w, q)
    if key in CROSS:
        return CROSS[key]
    res = None
    fuel = 8 * (len(w) + len(u)) + 16
    if kind == 'R':
        s = findR(fuel, (u, w, q))
        if s is not None:
            c = bsteps(s, (u, w, q))
            if c is not None and not c[1] and c[2] == q and c[0][:len(u)] == u:
                res = c[0][len(u):]
    else:
        s = findL(q, u, fuel, (w, u, q))
        if s is not None:
            c = bsteps(s, (w, u, q))
            if c is not None and not c[0] and c[2] == q and c[1][:len(u)] == u:
                res = c[1][len(u):]
    CROSS[key] = res
    return res


def xcrossR(cx, j, l, r, q):
    if not r:
        return None
    w, n = r[0]
    if len(w) < 2:
        return None
    p = peelB(cx, j, l)
    if p is None:
        return None
    u, l2 = p
    v = cross_rule('R', u, w, q)
    if v is None:
        return None
    return pushCells(u, rc(v, n, l2)), r[1:]


def xcrossL(cx, j, l, r, q):
    if not l:
        return None
    w, n = l[0]
    if len(w) < 2:
        return None
    p = peelB(cx, j, r)
    if p is None:
        return None
    u, r2 = p
    v = cross_rule('L', u, w, q)
    if v is None:
        return None
    return l[1:], pushCells(u, rc(v, n, r2))


def popR(cx, s, endB):
    p = popB(cx, s)
    if p is None:
        if not endB:
            raise NeedMore()
        return 0, []
    return p


def xmove(cx, l, r, q, endB):
    """one move; returns ('c', l, r, q) or ('x', q, w, r) or raises Fail on a halt"""
    # Moves that fail add no conditions that matter for soundness (conditions only restrict), but to keep the
    # recorded conditions minimal we snapshot and restore them.
    for j in range(4):
        n0 = len(cx.conds)
        x = xcrossR(cx, j, l, r, q)
        if x is not None:
            return ('c', x[0], x[1], q)
        del cx.conds[n0:]
    for j in range(4):
        n0 = len(cx.conds)
        x = xcrossL(cx, j, l, r, q)
        if x is not None:
            return ('c', x[0], x[1], q)
        del cx.conds[n0:]
    a, r2 = popR(cx, r, endB)
    t = delta.get((q, a))
    if t is None:
        raise Fail('halt')
    w, d, s = t
    if d == 'R':
        return ('c', nrm([((w,), K(1))] + l), r2, s)
    p = popB(cx, l)
    if p is None:
        return ('x', s, w, r2)
    b, l2 = p
    return ('c', l2, nrm([((b,), K(1)), ((w,), K(1))] + r2), s)


FUEL = 100000000


def exc(cx, u, q, q2, v, T, endB):
    l, r = pushCells(u, []), T
    for _ in range(FUEL):
        m = xmove(cx, l, r, q, endB)
        if m[0] == 'x':
            s, w, r = m[1], m[2], m[3]
            if s != q2:
                raise Fail('exit state')
            p = peelB(cx, len(v) - 1, r)
            if p is None or (w,) + p[0] != v:
                raise Fail('exit cells')
            return p[1]
        _, l, r, q = m
    raise Fail('fuel')


def preL(w, T):
    for a in reversed(w):
        T = nrm([((a,), K(1))] + T)
    return T


def cc(cx, es, w, T, endB):
    for (u, q, q2, v) in es:
        T = exc(cx, u, q, q2, v, T, endB)
    return preL(w, T)


def bits(s):
    return tuple(int(c) for c in s)


Ere = [(bits('0010'), A, B, bits('1001')), (bits('0100'), E, C, bits('0101')), (bits('0100'), E, C, bits('0101')),
       (bits('0011'), A, D, bits('0101')), (bits('0011'), A, D, bits('0101'))]
wre = bits('1010101010101')
Ero = [(bits('1001'), B, D, bits('1011')), (bits('1010'), C, A, bits('1010')), (bits('1001'), B, D, bits('1011')),
       (bits('0011'), A, D, bits('0101')), (bits('0011'), A, D, bits('0101'))]
wro = bits('101010101')
Eg = [(bits('0011'), A, D, bits('0010'))]
wg = bits('1010')
we0 = bits('11010')
Ee1 = [(bits('0011'), A, D, bits('0010')), (bits('0010'), A, B, bits('1010'))]
we1 = bits('0101010')


def f(X):
    return 3 * X // 2 + (1 if X % 2 == 0 else 3)


# ---------------------------------------------------------------- concrete sides
def ccC(es, w, T):
    """cc on a concrete side (counts are ints in K form)"""
    return cc(Ctx(None), es, w, T, True)


def ofList(cells):
    s = []
    for a in reversed(cells):
        s = nrm([((a,), K(1))] + s)
    return s


# ---------------------------------------------------------------- transforms
TH = 16


class Tr:
    __slots__ = ('pat', 'endB', 'out', 'conds', 'n')


def spec_of(cnt):
    return 'v' if cnt >= TH else cnt


def key_of(s, L):
    if L > len(s):
        return None
    return tuple((w, spec_of(n[0])) for w, n in s[:L]) + (('END',) if L == len(s) else ())


def match(t, s):
    """env if t applies to s"""
    L = len(t.pat)
    if L > len(s) or (t.endB and L != len(s)):
        return None
    env = []
    for (w, sp), (w2, n) in zip(t.pat, s):
        if w != w2:
            return None
        c = n[0]
        if sp != 'v' and sp != c:
            return None
        env.append(c)
    for e in t.conds:
        if lev(e, env) < 0:
            return None
    return env


def apply(t, s, env):
    return [(w, K(lev(e, env))) for w, e in t.out] + s[len(t.pat):]


def base_at(s, Lc, endB):
    pat = [(w, spec_of(n[0])) for w, n in s[:Lc]]
    env = [n[0] for w, n in s[:Lc]]
    T = [(w, (0, ((i, 1),)) if sp == 'v' else K(sp)) for i, (w, sp) in enumerate(pat)]
    cx = Ctx(env)
    out = cc(cx, Eg, wg, T, endB)
    t = Tr()
    t.pat, t.endB, t.out, t.n = pat, endB, out, 1
    t.conds = simp(cx.conds)
    return t, T


def base(s):
    """one carry (cc Eg wg) as a transform valid at s, on as few runs of s as it reads"""
    L = 1
    while True:
        Lc = min(L, len(s))
        try:
            t, T = base_at(s, Lc, Lc == len(s))
        except NeedMore:
            L *= 2
            continue
        k = 0
        while k < min(len(T), len(t.out)) and T[len(T) - 1 - k] == t.out[len(t.out) - 1 - k]:
            k += 1
        if k:
            try:
                t2, _ = base_at(s, Lc - k, False)
                return t2
            except NeedMore:
                pass
        return t


def simp(conds):
    """one condition per term vector: the strongest (least constant); constants >= 0 dropped"""
    best = {}
    for c, tv in conds:
        if not tv:
            if c < 0:
                raise Fail('false constant condition')
            continue
        if tv not in best or c < best[tv]:
            best[tv] = c
    return [(c, tv) for tv, c in best.items()]


def compose(t1, t2):
    o = len(t1.out)
    L2 = len(t2.pat)
    if t1.endB and L2 > o:
        raise Fail('compose: t2 reads past end')
    m = {}
    conds = list(t1.conds)
    for k in range(L2):
        w, sp = t2.pat[k]
        if k < o:
            w1, e = t1.out[k]
            if w1 != w:
                raise Fail('compose: words')
            if sp == 'v':
                m[k] = e
                if e[1]:
                    conds.append(e)
            else:
                m[k] = K(sp)
                if e[1]:
                    conds.append(lconst(e, -sp))
                    conds.append(lneg(lconst(e, -sp)))
                elif e[0] != sp:
                    raise Fail('compose: literal')
        else:
            pos = len(t1.pat) + k - o
            m[k] = (0, ((pos, 1),)) if sp == 'v' else K(sp)
    for e in t2.conds:
        conds.append(lsub(e, m))
    t = Tr()
    t.pat = t1.pat + (t2.pat[o:] if L2 > o else [])
    t.endB = t1.endB or (t2.endB and L2 >= o)
    if t2.endB and L2 < o:
        raise Fail('compose: endB inside')
    t.out = [(w, lsub(e, m)) for w, e in t2.out] + t1.out[L2:]
    t.conds = simp(conds)
    t.n = t1.n + t2.n
    return t


class Hash:
    def __init__(self):
        self.memo = {}   # (j, key) -> [Tr]
        self.Ls = {}
        self.made = 0

    def look(self, j, s):
        for L in sorted(self.Ls.get(j, ()), reverse=True):
            lst = self.memo.get((j, key_of(s, L)))
            if lst:
                for t in lst:
                    env = match(t, s)
                    if env is not None:
                        return t, env
        return None

    def get(self, j, s):
        r = self.look(j, s)
        if r:
            return r
        if j == 0:
            t = base(s)
        else:
            t1, env1 = self.get(j - 1, s)
            s1 = apply(t1, s, env1)
            t2, env2 = self.get(j - 1, s1)
            t = compose(t1, t2)
        env = match(t, s)
        assert env is not None, 'new transform does not match its state'
        self.Ls.setdefault(j, set()).add(len(t.pat))
        self.memo.setdefault((j, key_of(s, len(t.pat))), []).append(t)
        self.made += 1
        return t, env

    def gen(self, m, s, JMAX=60):
        """m carries"""
        while m:
            j = min(m.bit_length() - 1, JMAX)
            t, env = self.get(j, s)
            s = apply(t, s, env)
            m -= 1 << j
        return s


def phase(H, X, T):
    if X % 2 == 0:
        T = ccC(Ere, wre, T)
        e = X // 2 - 18 + 11
    else:
        T = ccC(Ero, wro, T)
        e = X // 2 - 18 + 12
    T = H.gen(e // 2, T) if H else gen_plain(e // 2, T)
    T = ccC(Eg, we0, T) if e % 2 == 0 else ccC(Ee1, we1, T)
    return f(X), T


def gen_plain(m, T):
    for _ in range(m):
        T = ccC(Eg, wg, T)
    return T




def lean_list(name):
    import re, os
    p = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'lean', 'ResetExc.lean')
    src = open(p).read()
    m = re.search(r'def %s : List Bool := \[([^\]]*)\]' % name, src)
    return tuple(1 if x.strip() == 'true' else 0 for x in m.group(1).split(','))


def start(which):
    if which == 'own':
        return 40, ofList(lean_list('L0own'))
    return 52, ofList(lean_list('L0twin'))


if __name__ == '__main__':
    which, K_ = sys.argv[1], int(sys.argv[2])
    if len(sys.argv) > 3:
        TH = int(sys.argv[3])
    plain = len(sys.argv) > 4 and sys.argv[4] == 'plain'
    X, T = start(which)
    H = None if plain else Hash()
    t0 = time.time()
    for k in range(K_):
        X, T = phase(H, X, T)
        print('phase %d X %s runs %d time %.1f transforms %s' % (k + 1, X if X < 10**15 else '%.4e' % X, len(T),
              time.time() - t0, H.made if H else '-'), flush=True)
