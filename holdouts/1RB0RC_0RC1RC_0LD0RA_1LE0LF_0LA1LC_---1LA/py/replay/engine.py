"""The replay engine of 1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA: the Python model of `lean/Exec.lean`.

This is the algorithm that the Lean executor runs (and is proved sound for), written so that the two agree move for
move.  It is independent of `py/closure/accel.py` except for the idea.

A side of the tape is a list of tokens, the cell nearest the head LAST in the Python list (FIRST in Lean).  A token
is a cell (0/1) or a block `(w, n)`: the word `w` (nearest cell first, so words of the left side are stored
reversed) repeated `n` times.  A count is `(c, a)`: c + sum a[i] * x_i with x_i >= 0 free.

Static mode (`Engine(shift, rules)`): the tables are fixed; this is what Lean runs.
Discovery mode (`discover=True`): shift rules and cycle rules are found on the way and appended to the tables.
"""
import sys

MACHINE = "1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA"
MINN = 6        # a block is crossed by a shift rule only if its count is surely >= MINN
MAXC = 10
BIG = 64
TBASE = 40
MAXK = 300000
MAXLW = 14
NORM_ROUNDS = 3


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


# ---------------------------------------------------------------- counts
def cst(n):
    return (n, ())


def cadd(x, y):
    a, b = x[1], y[1]
    if not b:
        return (x[0] + y[0], a)
    if not a:
        return (x[0] + y[0], b)
    n = max(len(a), len(b))
    a = a + (0,) * (n - len(a))
    b = b + (0,) * (n - len(b))
    return (x[0] + y[0], tuple(p + q for p, q in zip(a, b)))


def cmul(x, k):
    return (x[0] * k, tuple(p * k for p in x[1]))


def cdiv(x, k):
    """x = k * q + r with r a number, or None."""
    if any(p % k for p in x[1]):
        return None
    return (x[0] // k, tuple(p // k for p in x[1])), x[0] % k


def isconst(x):
    return all(p == 0 for p in x[1])


def cval(x, env):
    return x[0] + sum(p * env[i] for i, p in enumerate(x[1]) if p)


def cfmt(x):
    return str(x[0]) + ''.join("+%d*x%d" % (p, i) for i, p in enumerate(x[1]) if p)


# ---------------------------------------------------------------- shift rules by plain simulation between walls
def one_right(q, u, w):
    """u q> w -> v u q> (reading order): (v, steps) or None."""
    tape = list(u) + list(w)
    lw, lu = len(w), len(u)
    p, st, n, N = lu, q, 0, len(tape)
    while n < 5000:
        if p < 0:
            return None
        if p >= N:
            if st == q and tuple(tape[lw:]) == tuple(u):
                return tuple(tape[:lw]), n
            return None
        t = T[(st, tape[p])]
        if t is None:
            return None
        tape[p] = t[0]
        p += t[1]
        st = t[2]
        n += 1
    return None


def one_left(q, u, w):
    """w q> u -> q> u v (reading order, head on the first cell of u): (v, steps) or None."""
    tape = list(w) + list(u)
    lw, lu = len(w), len(u)
    p, st, n, N = lw, q, 0, len(tape)
    while n < 5000:
        if p < 0 or p >= N:
            return None
        t = T[(st, tape[p])]
        if t is None:
            return None
        tape[p] = t[0]
        p += t[1]
        st = t[2]
        n += 1
        if p == 0 and st == q and tuple(tape[:lu]) == tuple(u):
            return tuple(tape[lu:]), n
    return None


# ---------------------------------------------------------------- sides
def popcell(side):
    """Take the nearest cell off a side (mutates).  Undecided if a block's count is not surely >= 1."""
    if not side:
        return 0
    t = side[-1]
    if isinstance(t, int):
        side.pop()
        return t
    w, n = t
    if n[0] < 1:
        raise Undecided("pop from %s" % cfmt(n))
    side.pop()
    if not (n[0] == 1 and isconst(n)):
        side.append((w, (n[0] - 1, n[1])))
    for b in reversed(w[1:]):
        side.append(b)
    return w[0]


def take(side, u):
    """Remove the word u (nearest first) from the side if it is there (cells are popped, which may open blocks).
    Returns True/False; the side is unchanged on False."""
    k = len(u)
    if k == 0:
        return True
    suf = side[-k:]
    try:
        for b in u:
            if popcell(suf) != b:
                return False
    except Undecided:
        return False
    side[-k:] = suf
    return True


def pushblk(side, w, n):
    if side and not isinstance(side[-1], int) and side[-1][0] == w:
        side[-1] = (w, cadd(n, side[-1][1]))
    else:
        side.append((w, n))


# ---------------------------------------------------------------- normal form of a side (list nearest FIRST here)
def root(w):
    for d in range(1, len(w)):
        if len(w) % d == 0 and w[:d] * (len(w) // d) == w:
            return w[:d], len(w) // d
    return w, 1


def cell_onto(b, rest):
    if rest and not isinstance(rest[0], int):
        w, n = rest[0]
        if w[-1] == b:
            return blk_onto((b,) + w[:-1], n, cell_onto(b, rest[1:]))
    return [b] + rest


def blk_onto(w, n, rest):
    w, j = root(w)
    if j > 1:
        n = cmul(n, j)
    lw = len(w)
    while True:
        if rest and not isinstance(rest[0], int) and rest[0][0] == w:
            n = cadd(n, rest[0][1])
            rest = rest[1:]
            continue
        if len(rest) >= lw and tuple(rest[:lw]) == w:
            n = (n[0] + 1, n[1])
            rest = rest[lw:]
            continue
        break
    if isconst(n) and n[0] < 3:
        for b in reversed(w * n[0]):
            rest = cell_onto(b, rest)
        return rest
    return [(w, n)] + rest


def npass(toks):
    out = []
    for t in reversed(toks):
        if isinstance(t, int):
            out = cell_onto(t, out)
        else:
            out = blk_onto(t[0], t[1], out)
    return out


def best_repeat(s):
    """s: the literal cells from here to the next block.  (w, c) with c >= 4 copies of w at the start of s,
    of largest total length (shortest word on ties), or None."""
    best = None
    m = len(s)
    for lw in range(1, MAXLW + 1):
        c = 1
        while (c + 1) * lw <= m and s[c * lw:(c + 1) * lw] == s[:lw]:
            c += 1
        if c >= 4 and (best is None or c * lw > best[0] * best[1]):
            best = (c, lw)
    return best


def form(toks):
    out = []
    i = 0
    n = len(toks)
    while i < n:
        if not isinstance(toks[i], int):
            out.append(toks[i])
            i += 1
            continue
        j = i
        while j < n and isinstance(toks[j], int):
            j += 1
        b = best_repeat(toks[i:j])
        if b:
            out.append((tuple(toks[i:i + b[1]]), cst(b[0])))
            i += b[0] * b[1]
        else:
            out.append(toks[i])
            i += 1
    return out


def norm(toks):
    """Nearest-first token list -> its normal form (same cells)."""
    t = npass(toks)
    for _ in range(NORM_ROUNDS):
        t = npass(form(t))
    return t


def flat(toks, env=None):
    out = []
    for t in toks:
        if isinstance(t, int):
            out.append(t)
        else:
            out.extend(t[0] * (cval(t[1], env) if env is not None else t[1][0]))
    return out


def fmt(toks):
    out = []
    lit = ''
    for t in toks:
        if isinstance(t, int):
            lit += str(t)
        else:
            if lit:
                out.append(lit)
                lit = ''
            out.append('(%s)^%s' % (''.join(map(str, t[0])), cfmt(t[1])))
    if lit:
        out.append(lit)
    return ' '.join(out)


def parse(txt):
    """'0 (011)^5 11' -> nearest-first tokens of a right side."""
    out = []
    for part in txt.split():
        if part.startswith('('):
            w, e = part[1:].split(')^')
            out.append((tuple(int(c) for c in w), cst(int(e))))
        else:
            out.extend(int(c) for c in part)
    return out


# ---------------------------------------------------------------- cycle rules
class Rule:
    """tmpl: list of cell | ('f', w, n) | ('v', w, b0, b1) for the right side at an event (left side empty, state E).
    K: moves of the proof run (empty rule table); events: events of one application; S: steps (affine)."""

    def __init__(self, tmpl, events):
        self.tmpl = tmpl
        self.events = events
        self.K = None
        self.S = None
        self.uses = 0

    def sym(self, which):
        out = []
        for i, t in enumerate(self.tmpl):
            if isinstance(t, int):
                out.append(t)
            elif t[0] == 'f':
                out.append((t[1], cst(t[2])))
            else:
                out.append((t[1], (t[2 + which], (0,) * i + (2,))))
        return out

    def napp(self, toks):
        """Number of applications N >= 1 from the tokens, or 0."""
        if len(toks) != len(self.tmpl):
            return 0
        N = None
        for t, r in zip(toks, self.tmpl):
            if isinstance(r, int):
                if t != r:
                    return 0
            elif isinstance(t, int) or t[0] != r[1]:
                return 0
            elif r[0] == 'f':
                if not (isconst(t[1]) and t[1][0] == r[2]):
                    return 0
            else:
                c = t[1][0]
                b0, b1 = r[2], r[3]
                if c < b0 or (c - b0) % 2 or any(p % 2 for p in t[1][1]):
                    return 0
                if b1 < b0:
                    k = (c - b0) // (b0 - b1) + 1
                    N = k if N is None else min(N, k)
        return N or 0

    def shift(self, toks, N):
        out = []
        for t, r in zip(toks, self.tmpl):
            if isinstance(r, int) or r[0] == 'f':
                out.append(t)
            else:
                b0, b1 = r[2], r[3]
                c = t[1][0]
                c = c + N * (b1 - b0) if b1 >= b0 else c - N * (b0 - b1)
                out.append((t[0], (c, t[1][1])))
        return out


class Halt(Exception):
    pass


class Engine:
    def __init__(self, shiftR=None, shiftL=None, rules=None, discover=False):
        self.L = []
        self.R = []
        self.st = 0
        self.shiftR = shiftR if shiftR is not None else {}     # (st, w) -> [(k, u, v, steps)]
        self.shiftL = shiftL if shiftL is not None else {}
        self.rules = rules if rules is not None else []
        self.discover = discover
        self.moves = 0
        self.ev = 0
        self.jumps = 0
        self.env = None
        self.hist = {}
        self.failed = {}
        self.use_rules = True
        self.steps = cst(0)     # affine; only tracked through cross and step (rule jumps add their own)
        self.nq = 0             # quadratic part is not tracked: steps are exact only when counts are numbers

    # -- shift rules
    def cross(self):
        R, L, st = self.R, self.L, self.st
        if R and not isinstance(R[-1], int) and R[-1][1][0] >= MINN:
            w, n = R[-1]
            for k, u, v, c in self.shiftR.get((st, w), ()):
                d = cdiv(n, k)
                if d is None or d[0][0] < 1:
                    continue
                if not take(L, u):
                    continue
                R.pop()
                if d[1]:
                    R.append((w, cst(d[1])))
                pushblk(L, v, d[0])
                L.extend(reversed(u))
                self.steps = cadd(self.steps, cmul(d[0], c))
                return True
            if self.discover and self.find_right():
                return self.cross()
        if L and not isinstance(L[-1], int) and L[-1][1][0] >= MINN:
            w, n = L[-1]
            for k, u, v, c in self.shiftL.get((st, w), ()):
                d = cdiv(n, k)
                if d is None or d[0][0] < 1:
                    continue
                if not take(R, u):
                    continue
                L.pop()
                if d[1]:
                    L.append((w, cst(d[1])))
                pushblk(R, v, d[0])
                R.extend(reversed(u))
                self.steps = cadd(self.steps, cmul(d[0], c))
                return True
            if self.discover and self.find_left():
                return self.cross()
        return False

    def lits(self, side):
        out = []
        for t in reversed(side):
            if not isinstance(t, int) or len(out) >= MAXC:
                break
            out.append(t)
        return tuple(out)       # nearest first

    def find_right(self):
        w, n = self.R[-1]
        lit = self.lits(self.L)
        for k in (1, 2):
            d = cdiv(n, k)
            if d is None or d[0][0] < 1:
                continue
            for lu in range(0, len(lit) + 1):
                u = lit[:lu]
                r = one_right(self.st, tuple(reversed(u)), w * k)
                if r:
                    self.shiftR.setdefault((self.st, w), []).append((k, u, tuple(reversed(r[0])), r[1]))
                    return True
        return False

    def find_left(self):
        w, n = self.L[-1]
        lit = self.lits(self.R)
        for k in (1, 2):
            d = cdiv(n, k)
            if d is None or d[0][0] < 1:
                continue
            for lu in range(1, len(lit) + 1):
                u = lit[:lu]
                r = one_left(self.st, u, tuple(reversed(w * k)))
                if r:
                    self.shiftL.setdefault((self.st, w), []).append((k, u, r[0], r[1]))
                    return True
        return False

    # -- one move
    def move(self):
        """A shift rule, or one machine step followed (at an event) by normalisation and cycle rules."""
        self.moves += 1
        if self.cross():
            return
        r = popcell(self.R)
        t = T[(self.st, r)]
        if t is None:
            raise Halt()
        w, m, ns = t
        self.st = ns
        self.steps = (self.steps[0] + 1, self.steps[1])
        if m == 1:
            self.L.append(w)
            return
        self.R.append(w)
        self.R.append(popcell(self.L))
        if ns == 4 and not self.L:
            self.ev += 1
            self.at_event()

    def toks(self):
        return list(reversed(self.R))

    def at_event(self):
        toks = norm(self.toks())
        self.R = list(reversed(toks))
        if not self.use_rules:
            return
        for rule in self.rules:
            N = rule.napp(toks)
            if N >= 1:
                self.apply(rule, toks, N)
                return
        if self.discover:
            self.look_for_rule(toks)

    def apply(self, rule, toks, N):
        new = rule.shift(toks, N)
        self.R = list(reversed(new))
        self.jumps += 1
        self.ev += N * rule.events
        rule.uses += 1
        # steps: sum over j < N of S(x + j d), x_i = (n_i - b0_i) / 2, d_i = (b1_i - b0_i) / 2
        if rule.S is not None:
            tot = cst(N * rule.S[0])
            for i, a in enumerate(rule.S[1]):
                if not a:
                    continue
                r = rule.tmpl[i]
                n = toks[i][1]
                x = ((n[0] - r[2]) // 2, tuple(p // 2 for p in n[1]))
                tot = cadd(tot, cmul(x, a * N))
                tot = (tot[0] + a * ((r[3] - r[2]) // 2) * (N * (N - 1) // 2), tot[1])
            self.steps = cadd(self.steps, tot)

    # -- discovery of cycle rules (as accel.py's Driver)
    def look_for_rule(self, toks):
        def big(n):
            return (not isconst(n)) or n[0] >= BIG
        shape = tuple(t if isinstance(t, int) else (t[0], -1 if big(t[1]) else t[1][0]) for t in toks)
        env = self.env
        counts = [cval(t[1], env) if env is not None else t[1][0]
                  for t in toks if not isinstance(t, int) and big(t[1])]
        if not counts:
            return
        h = self.hist.setdefault(shape, [])
        h.append((self.ev, counts))
        if len(h) > 3:
            del h[0]
        if len(h) < 3:
            return
        k = h[2][0] - h[1][0]
        if k != h[1][0] - h[0][0] or k > MAXK:
            return
        d = [b - a for a, b in zip(h[1][1], h[2][1])]
        if d != [b - a for a, b in zip(h[0][1], h[1][1])] or not any(x < 0 for x in d):
            return
        if any(x < 0 and n + 96 * x < TBASE + 16 for n, x in zip(counts, d)):
            return
        key = (shape, tuple(d), tuple(n % 2 for n in counts))
        f = self.failed.get(key, 0)
        if f:
            self.failed[key] = f - 1
            return
        Rm = 1 if all(x % 2 == 0 for x in d) else 2
        base = [TBASE + 2 * Rm * abs(x) + (n - TBASE - 2 * Rm * abs(x)) % 2 for n, x in zip(counts, d)]
        if any(b > n for b, n in zip(base, counts)):
            return
        tmpl = []
        i = 0
        for t in toks:
            if isinstance(t, int):
                tmpl.append(t)
            elif big(t[1]):
                tmpl.append(('v', t[0], base[i], base[i] + Rm * d[i]))
                i += 1
            else:
                tmpl.append(('f', t[0], t[1][0]))
        rule = Rule(tmpl, Rm * k)
        if not prove_rule(rule, self.shiftR, self.shiftL, True):
            self.failed[key] = 50
            sys.stderr.write("rule proposal failed: %s\n" % fmt(rule.sym(0)))
            return
        self.rules.append(rule)
        self.hist.pop(shape, None)
        N = rule.napp(toks)
        if N >= 1:
            self.apply(rule, toks, N)


def prove_rule(rule, shiftR, shiftL, discover):
    """Run the engine without cycle rules from sym0 for rule.events events; must end exactly at sym1.
    Sets rule.K (moves) and rule.S (steps)."""
    e = Engine(shiftR, shiftL, [], discover)
    e.use_rules = False
    e.st = 4
    e.R = list(reversed(rule.sym(0)))
    try:
        while e.ev < rule.events:
            e.move()
            if e.moves > 2000000:
                return False
    except (Undecided, Halt):
        return False
    if e.st != 4 or e.L or e.toks() != rule.sym(1):
        return False
    rule.K = e.moves
    rule.S = e.steps
    return True
