"""A record-skipping run of the block macro machine (blockmm.py), in the style of Hashlife but over time.

A state is a left record (ell, c, blocks), blocks = [(D, x)].  Whether one macro step depends on a block only through
its *shape*: D itself when D < 8, else (parity of D, x) (blockmm crosses such blocks with rules symbolic in D).  A
*transform* is what 2^j macro steps do to a state whose first L blocks have given shapes: the new head (ell, c), the
new first blocks as affine expressions in the old D's (the blocks from L on are untouched), the steps as an affine
expression, the number of resets passed, and linear conditions on the old D's under which this holds (the shapes of
the intermediate records must be the ones assumed).  Level-0 transforms come from one macro step on a generic
instance (each long block a distinct huge number, decoded afterwards) and are checked against the concrete step.
Level j is two level-(j-1) transforms composed, memoized by (j, head, shapes of the first L blocks).
"""
from fractions import Fraction as Fr
from blockmm import macro_step, Fail


DS = 64   # blocks with D >= DS are crossed by rules symbolic in D (blockmm needs D >= 8 and, after normalize, a few more)


def shape(b):
    D, x = b
    return (D, x) if D < DS else ('L', D & 1, x)


class Track(list):
    """A block list that remembers how far macro_step looked."""
    def __init__(self, it):
        super().__init__(it)
        self.reach = 0

    def __getitem__(self, i):
        if isinstance(i, slice):
            self.reach = max(self.reach, i.start or 0)
        else:
            self.reach = max(self.reach, i + 1)
        return super().__getitem__(i)


# affine expressions: dict {var: Fraction, None: const}; var = position of a block of the input
def const(v):
    return {None: Fr(v)}


def ev(e, Ds):
    s = e.get(None, 0)
    for k, a in e.items():
        if k is not None:
            s += a * Ds[k]
    assert s.denominator == 1, e
    return int(s)


def sub(e, m):
    """Substitute var k -> expression m[k]."""
    out = {None: e.get(None, Fr(0))}
    for k, a in e.items():
        if k is None:
            continue
        for k2, b in m[k].items():
            out[k2] = out.get(k2, Fr(0)) + a * b
    return {k: v for k, v in out.items() if v != 0 or k is None}


def add(e, f):
    out = dict(e)
    for k, v in f.items():
        out[k] = out.get(k, Fr(0)) + v
    return {k: v for k, v in out.items() if v != 0 or k is None}


def has_vars(e):
    return any(k is not None for k in e)


class T:
    __slots__ = ('L', 'head', 'out', 'cons', 'steps', 'n', 'resets', 'halt', 'endkey')


def key_of(state, L):
    ell, c, bl = state
    return (tuple(ell), c, tuple(shape(bl[i]) if i < len(bl) else 'END' for i in range(L)))


def holds(t, Ds):
    for e, op, v in t.cons:
        x = ev(e, Ds)
        if op == '>=' and x < v:
            return False
        if op == '==' and x != v:
            return False
    return True


def Dvec(state, L):
    bl = state[2]
    return [bl[i][0] if i < len(bl) else 0 for i in range(L)]


def apply(t, state):
    ell, c, bl = state
    Ds = Dvec(state, t.L)
    out = [(ev(e, Ds), x) for e, x in t.out] + list(bl[t.L:])
    while out and out[-1] == (0, 0):
        out.pop()
    return (t.head[0], t.head[1], out), ev(t.steps, Ds)


SH = 64


def level0(state):
    ell, c, bl = state
    tr = Track(bl)
    r = macro_step(ell, c, tr)
    t = T()
    t.n = 1
    if r[0] is None:
        t.halt = r
        t.L = tr.reach
        return t, None
    t.halt = None
    A = min(len(bl), tr.reach + 2)
    gen, base = [], {}
    for i in range(len(bl)):
        D, x = bl[i]
        if i < A and D >= DS:
            B = 1 << (SH * (i + 1))
            gen.append((8 + (D & 1) + 2 * B, x))
            base[i] = B
        else:
            gen.append((D, x))
    tr2 = Track(gen)
    r2 = macro_step(ell, c, tr2)
    assert r2[0] is not None and r2[0][:2] == r[0][:2]
    order = sorted(base, reverse=True)

    def decode(v, half):
        """v = const + sum a_i * D_i (half: in terms of t_i = (D_i - 8 - par)/2 = B_i)."""
        e = {}
        for i in order:
            B = base[i]
            unit = B if half else 2 * B
            a = (v + unit // 2) // unit
            if a:
                e[i] = Fr(a) if not half else Fr(a, 2)
                v -= a * (gen[i][0] if not half else B)
                if half:
                    e[None] = e.get(None, Fr(0)) - Fr(a * (8 + (gen[i][0] & 1)), 2)
        e[None] = e.get(None, Fr(0)) + v
        return e
    out2 = r2[0][2]
    # untouched suffix: output blocks equal to input blocks from position L on
    L = max(tr2.reach, tr.reach)
    n_out = len(out2) - (len(bl) - L) if len(bl) >= L else len(out2)
    while True:
        tail_in = list(gen[L:]) if L <= len(gen) else []
        if n_out >= 0 and list(out2[n_out:]) == tail_in and n_out <= len(out2):
            break
        L += 1
        n_out = len(out2) - max(0, len(bl) - L)
        if L > len(bl) + 2:
            raise Fail('no untouched suffix')
    t.L = L
    t.head = r2[0][:2]
    t.out = [(decode(D, False), x) for D, x in out2[:n_out]]
    t.steps = decode(r2[1], True)
    t.cons = []
    o = r[0][2]
    t.resets = 1 if ((tuple(r[0][0]), r[0][1]) == ((1,), 1) and len(o) > 1 and o[0] == (0, 0)) else 0
    # check on the concrete state
    s2, st = apply(t, state)
    assert (s2[0], s2[1], s2[2]) == (r[0][0], r[0][1], r[0][2]) and st == r[1], 'level-0 decode mismatch'
    return t, s2


def compose(t1, t2, state):
    """t2 after t1, both valid at state / t1(state); returns the transform for state."""
    n1o = len(t1.out)
    L = t1.L + max(0, t2.L - n1o)
    m = {}
    for k in range(t2.L):
        m[k] = t1.out[k][0] if k < n1o else {t1.L + k - n1o: Fr(1)}
    cons = list(t1.cons)
    s1 = apply(t1, state)[0]
    for k in range(min(t2.L, n1o)):
        e = t1.out[k][0]
        if not has_vars(e):
            continue
        D = s1[2][k][0] if k < len(s1[2]) else 0
        if D >= DS:
            cons.append((e, '>=', DS))
        else:
            cons.append((e, '==', D))
    for e, op, v in t2.cons:
        cons.append((sub(e, m), op, v))
    t = T()
    t.L = L
    t.head = t2.head
    cons = simplify(cons)
    t.out = [(sub(e, m), x) for e, x in t2.out] + t1.out[t2.L:]
    t.steps = add(t1.steps, sub(t2.steps, m))
    t.cons = cons
    t.n = t1.n + t2.n
    t.resets = t1.resets + t2.resets
    t.halt = None
    return t


def simplify(cons):
    """Keep one condition per linear form: the largest lower bound, or the equality."""
    ge, eq = {}, {}
    for e, op, v in cons:
        lin = tuple(sorted((k, a) for k, a in e.items() if k is not None))
        if not lin:
            continue
        b = v - e.get(None, Fr(0))
        if op == '>=':
            if lin not in ge or b > ge[lin]:
                ge[lin] = b
        else:
            assert eq.get(lin, b) == b, 'inconsistent equalities'
            eq[lin] = b
    out = []
    for lin, b in ge.items():
        if lin in eq:
            continue
        out.append((dict(lin), '>=', b))
    for lin, b in eq.items():
        out.append((dict(lin), '==', b))
    return out


class Acc:
    def __init__(self):
        self.memo = {}      # (j, L) -> {key: [transforms]}
        self.Ls = {}        # j -> set of L
        self.made = 0

    def look(self, j, state):
        for L in sorted(self.Ls.get(j, ()), reverse=True):
            lst = self.memo[j, L].get(key_of(state, L))
            if lst:
                Ds = Dvec(state, L)
                for t in lst:
                    if holds(t, Ds):
                        return t
        return None

    def store(self, j, state, t):
        self.Ls.setdefault(j, set()).add(t.L)
        self.memo.setdefault((j, t.L), {}).setdefault(key_of(state, t.L), []).append(t)
        self.made += 1

    def get(self, j, state):
        """The transform of 2^j records at state; or a halting level-0 transform (t.halt set) met on the way, with the
        state where it happens and the records before it."""
        t = self.look(j, state)
        if t is not None:
            return t, None
        if j == 0:
            t, _ = level0(state)
            if t.halt:
                return t, (state, 0)
            self.store(0, state, t)
            return t, None
        t1, h = self.get(j - 1, state)
        if h:
            return t1, h
        s1, _ = apply(t1, state)
        t2, h = self.get(j - 1, s1)
        if h:
            return t2, (h[0], t1.n + h[1])
        t = compose(t1, t2, state)
        self.store(j, state, t)
        return t, None
