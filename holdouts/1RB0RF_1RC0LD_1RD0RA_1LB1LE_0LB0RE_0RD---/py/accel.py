"""Exact accelerated simulator for a two-symbol Turing machine (any machine; written for the G09 pair
1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD--- and 1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---).

Tape: two stacks of tokens (literal cells 0/1, the blank end 'B', blocks Rep(word, count)).  A move is a single
machine step or a *shift rule*: a block (w)^n is crossed in one go when one copy of w takes the head, in the same
state, across the copy carrying a short literal word u along (u w -> v u).  Every time the head reaches a fresh cell
(an *event*) the tape is re-compressed into blocks (deterministically) and its *shape* (state, side, the token list
with counts removed) is recorded.

Acceleration.  When a shape recurs twice with the same change d of the block counts, the period is re-run
*symbolically*: every block whose count changes (or is large) gets the count x_i + T_i (x_i a variable over the
naturals, T_i <= its current value), the others keep their value.  If the symbolic run reaches the same shape after
the same number of events, with counts x_i + T_i + d_i and a step count that is linear in the x_i, the period is a
theorem for all x_i >= 0 (at the level of this code), and it is applied k times at once, k as large as the shrinking
blocks allow; the steps are summed in closed form.  So the simulation is exact: the same step count and tape as the
plain machine, only faster.  A halt anywhere raises Halted.

usage (from the repo root):
  python3 holdouts/1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---/py/accel.py MACHINE MAXSTEPS [PRINT_EVERY_JUMPS]
"""
import sys
import os

sys.setrecursionlimit(10000)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import Lin  # noqa: E402

BL = 'B'


class Halted(Exception):
    pass


class NeedSplit(Exception):
    pass


class Rep:
    __slots__ = ('w', 'n')

    def __init__(s, w, n):
        s.w = tuple(w)
        s.n = n

    def __repr__(s):
        return '(%s)^%s' % (''.join(map(str, s.w)), s.n)


def ge1(n):
    return n >= 1 if isinstance(n, int) else n.surely_ge(1)


def iszero(n):
    return n == 0 if isinstance(n, int) else n.is_zero()


def scal(n, k):
    return n * k if isinstance(n, int) else k * n


class Machine:
    def __init__(s, M):
        s.M = M
        s.TT = {}
        for st, g in enumerate(M.split('_')):
            for y in range(2):
                t = g[3 * y:3 * y + 3]
                s.TT[(st, y)] = None if t[2] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
        s.cache = {}

    def one_right(s, q, u, w, maxn=2000):
        key = ('r', q, u, w)
        if key in s.cache:
            return s.cache[key]
        cells = list(u) + list(w)
        pos = len(u)
        st = q
        res = None
        N = len(cells)
        for n in range(1, maxn):
            tr = s.TT[(st, cells[pos])]
            if tr is None:
                break
            cells[pos] = tr[0]
            pos += tr[1]
            st = tr[2]
            if pos == N:
                if st == q and tuple(cells[len(w):]) == u:
                    res = (tuple(cells[:len(w)]), n)
                break
            if pos < 0:
                break
        s.cache[key] = res
        return res

    def one_left(s, q, u, w, maxn=2000):
        key = ('l', q, u, w)
        if key in s.cache:
            return s.cache[key]
        cells = list(w) + list(u)
        pos = len(w)
        st = q
        res = None
        N = len(cells)
        for n in range(1, maxn):
            tr = s.TT[(st, cells[pos])]
            if tr is None:
                break
            cells[pos] = tr[0]
            pos += tr[1]
            st = tr[2]
            if pos == 0 and st == q and tuple(cells[:len(u)]) == u:
                res = (tuple(cells[len(u):]), n)
                break
            if pos < 0 or pos >= N:
                break
        s.cache[key] = res
        return res


MAXC = 24


class Cfg:
    def __init__(s, m, L, st, R, steps=0):
        s.m = m
        s.L = L
        s.st = st
        s.R = R
        s.steps = steps
        s.ev = None   # 'L'/'R' when the head has just reached a fresh cell

    def __repr__(s):
        return ' '.join(map(str, s.L)) + ' %s> ' % 'ABCDEF'[s.st] + ' '.join(map(str, reversed(s.R)))


def _toplit(S, k):
    if len(S) < k:
        return None
    seg = S[len(S) - k:]
    for z in seg:
        if not isinstance(z, int):
            return None
    return seg


def try_cross(c):
    R = c.R
    L = c.L
    m = c.m
    top = R[-1]
    if isinstance(top, Rep) and not iszero(top.n):
        for lu in range(0, MAXC + 1):
            seg = _toplit(L, lu) if lu else []
            if seg is None:
                break
            u = tuple(seg)
            r = m.one_right(c.st, u, top.w)
            if r:
                v, s = r
                R.pop()
                if lu:
                    del L[len(L) - lu:]
                L.append(Rep(v, top.n))
                L.extend(u)
                c.steps = c.steps + scal(top.n, s)
                c.xn = top.n
                return True
    ltop = L[-1]
    if isinstance(ltop, Rep) and not iszero(ltop.n):
        for lu in range(1, MAXC + 1):
            seg = _toplit(R, lu)
            if seg is None:
                break
            u = tuple(reversed(seg))
            r = m.one_left(c.st, u, ltop.w)
            if r:
                v, s = r
                L.pop()
                del R[len(R) - lu:]
                R.append(Rep(v, ltop.n))
                R.extend(reversed(u))
                c.steps = c.steps + scal(ltop.n, s)
                c.xn = ltop.n
                return True
    return False


def try_rotate(c):
    L = c.L
    R = c.R
    for j in range(1, MAXC + 1):
        if len(L) > j and isinstance(L[-1 - j], Rep):
            x = _toplit(L, j)
            if x is None:
                break
            r = L[-1 - j]
            x = tuple(x)
            if j < len(r.w) and r.w[:j] == x and not iszero(r.n):
                save = L[-1 - j:]
                L[-1 - j:] = list(x) + [Rep(r.w[j:] + r.w[:j], r.n)]
                if try_cross(c):
                    return True
                L[-1 - j:] = save
        elif len(L) > j and not isinstance(L[-1 - j], int):
            break
    for j in range(1, MAXC + 1):
        if len(R) > j and isinstance(R[-1 - j], Rep):
            seg = _toplit(R, j)
            if seg is None:
                break
            x = tuple(reversed(seg))
            r = R[-1 - j]
            if j < len(r.w) and r.w[len(r.w) - j:] == x and not iszero(r.n):
                save = R[-1 - j:]
                R[-1 - j:] = list(reversed(x)) + [Rep(x + r.w[:len(r.w) - j], r.n)]
                if try_cross(c):
                    return True
                R[-1 - j:] = save
        elif len(R) > j and not isinstance(R[-1 - j], int):
            break
    return False


def unroll_right(c):
    R = c.R
    while True:
        t = R[-1]
        if t == BL and not isinstance(t, (int, Rep)):
            R.append(0)
            return
        if isinstance(t, Rep):
            if iszero(t.n):
                R.pop()
                continue
            if not ge1(t.n):
                raise NeedSplit(t)
            R.pop()
            if not iszero(t.n - 1):
                R.append(Rep(t.w, t.n - 1))
            R.extend(reversed(t.w))
            continue
        return


def unroll_left(c):
    L = c.L
    while True:
        t = L[-1]
        if t == BL and not isinstance(t, (int, Rep)):
            L.append(0)
            c.ev = 'L'
            return
        if isinstance(t, Rep):
            if iszero(t.n):
                L.pop()
                continue
            if not ge1(t.n):
                raise NeedSplit(t)
            L.pop()
            if not iszero(t.n - 1):
                L.append(Rep(t.w, t.n - 1))
            L.extend(t.w)
            continue
        return


def step(c):
    R = c.R
    L = c.L
    unroll_right(c)
    y = R[-1]
    tr = c.m.TT[(c.st, y)]
    if tr is None:
        raise Halted((c.st, y, c.steps))
    w, d, s = tr
    if d < 0:
        unroll_left(c)   # before any change, so that NeedSplit leaves the configuration as it was
    R.pop()
    if d > 0:
        L.append(w)
    else:
        R.append(w)
        R.append(L.pop())
    c.st = s
    c.steps = c.steps + 1


def _near(S):
    for k in range(1, min(MAXC, len(S) - 1) + 1):
        z = S[-1 - k]
        if isinstance(z, Rep):
            return True
        if not isinstance(z, int):
            return False
    return False


CROSS_EVENTS = [os.environ.get('ACCEL_X') == '1']   # also count the crossing of a long block as an event (for interior zig-zag phases)


def _xev(c):
    if CROSS_EVENTS[0] and not c.ev:
        n = c.xn
        if (n >= 8) if isinstance(n, int) else (not n.is_const() or n.k >= 8):
            c.ev = 'X'


def move(c):
    R = c.R
    L = c.L
    if isinstance(R[-1], Rep) or isinstance(L[-1], Rep):
        if try_cross(c):
            _xev(c)
            return
    if _near(L) or _near(R):
        if try_rotate(c):
            _xev(c)
            return
    step(c)


# ------------------------------------------------------------------ compression
MAXW = 12


def _compress_lits(lits):
    """literal list (tape order) -> tokens, greedy: at each position the word (length<=MAXW, >=3 copies) covering most"""
    out = []
    i = 0
    n = len(lits)
    while i < n:
        best = None
        for p in range(1, MAXW + 1):
            if i + 3 * p > n:
                break
            w = lits[i:i + p]
            k = 1
            while i + (k + 1) * p <= n and lits[i + k * p:i + (k + 1) * p] == w:
                k += 1
            if k >= 3 and (best is None or k * p > best[0] * best[1]):
                best = (k, p)
        if best:
            k, p = best
            out.append(Rep(lits[i:i + p], k))
            i += k * p
        else:
            out.append(lits[i])
            i += 1
    return out


def _merge(seq):
    changed = True
    while changed:
        changed = False
        out = []
        for z in seq:
            if isinstance(z, Rep) and out and isinstance(out[-1], Rep) and out[-1].w == z.w:
                out[-1] = Rep(z.w, out[-1].n + z.n)
                changed = True
                continue
            out.append(z)
        seq = out
        # Rep followed by literal copies
        out = []
        i = 0
        while i < len(seq):
            z = seq[i]
            if isinstance(z, Rep):
                p = len(z.w)
                n = z.n
                j = i + 1
                while j + p <= len(seq) and all(isinstance(seq[j + t], int) for t in range(p)) and \
                        tuple(seq[j:j + p]) == z.w:
                    n = n + 1
                    j += p
                    changed = True
                # literal copies before
                while len(out) >= p and all(isinstance(out[-p + t], int) for t in range(p)) and \
                        tuple(out[-p:]) == z.w:
                    del out[-p:]
                    n = n + 1
                    changed = True
                out.append(Rep(z.w, n))
                i = j
            else:
                out.append(z)
                i += 1
        seq = out
    return seq


def compress_seq(seq):
    out = []
    lit = []
    ex = []
    for z in seq:
        if isinstance(z, Rep):
            n = z.n if isinstance(z.n, int) else (z.n.k if z.n.is_const() else None)
            if n is not None and n < 3:
                ex.extend(z.w * n)
                continue
        ex.append(z)
    for z in ex:
        if isinstance(z, int):
            lit.append(z)
        else:
            if lit:
                out.extend(_compress_lits(tuple(lit)) if len(lit) >= 3 else lit)
                lit = []
            out.append(z)
    if lit:
        out.extend(_compress_lits(tuple(lit)) if len(lit) >= 3 else lit)
    return _merge(out)


def compress(c):
    c.L = compress_seq(c.L)
    c.R = list(reversed(compress_seq(list(reversed(c.R)))))


def shape(c):
    def sh(S):
        return tuple(('R', z.w) if isinstance(z, Rep) else z for z in S)
    return (c.st, c.ev, sh(c.L), sh(c.R))


def reps(c):
    return [z for z in c.L if isinstance(z, Rep)] + [z for z in reversed(c.R) if isinstance(z, Rep)]


def run_events(c, nev, maxmoves=10 ** 7):
    """run until nev events have happened (compressing at each); return number of moves"""
    k = 0
    mv = 0
    while k < nev:
        c.ev = None
        move(c)
        mv += 1
        if c.R[-1] == BL and not isinstance(c.R[-1], (int, Rep)):
            c.ev = 'R'
        if c.ev:
            compress(c)
            k += 1
        if mv > maxmoves:
            raise RuntimeError('too many moves')
    return mv


# ------------------------------------------------------------------ symbolic verification of a period
def symbolic_copy(c, T, delta):
    """copy of c with counts generalised: block i -> x_i + T_i if it changes or is large, else constant"""
    rs = reps(c)
    idx = {id(z): i for i, z in enumerate(rs)}
    Ts = []

    def gen(z):
        i = idx[id(z)]
        n = z.n
        if delta[i] != 0 or n >= 3 * T:
            t = min(T, n)
            Ts.append((i, t))
            return Rep(z.w, Lin('x%d' % i) + t)
        return Rep(z.w, Lin(n))
    L = [gen(z) if isinstance(z, Rep) else z for z in c.L]
    R = [gen(z) if isinstance(z, Rep) else z for z in c.R]
    s = Cfg(c.m, L, c.st, R, Lin(0))
    s.ev = c.ev
    return s, dict(Ts)


BOUND = 200
QUIET = 400


def advance(c):
    """one move; True when it ends at an event (the tape is then compressed)"""
    c.ev = None
    move(c)
    if not isinstance(c.R[-1], (int, Rep)):
        c.ev = 'R'
    if c.ev:
        compress(c)
        c.quiet = 0
        return True
    c.quiet = getattr(c, 'quiet', 0) + 1
    if c.quiet >= QUIET:      # a long stretch without events: re-compress (not an event)
        compress(c)
        c.quiet = 0
    return False


def _ckey(n):
    if isinstance(n, int):
        return n if n < BOUND else None
    if not n.is_const():
        return None
    return n.k if n.k < BOUND else None


def key_of(c, level):
    if level == 0:
        return shape(c)
    return (shape(c), tuple(_ckey(z.n) for z in reps(c)))


def symtm_str(c):
    """the configuration in bbtools.symtm notation"""
    def tok(z):
        if isinstance(z, Rep):
            return '(%s)^%s' % (''.join(map(str, z.w)), repr(Lin(z.n)))
        if isinstance(z, int):
            return str(z)
        return '0^inf'
    return ' '.join(tok(z) for z in c.L) + ' %s> ' % 'ABCDEF'[c.st] + ' '.join(tok(z) for z in reversed(c.R))


LAST = {}


def verify(c, level, delta, T, maxmoves=2 * 10 ** 6):
    """re-run the period symbolically from c generalised; it ends at the first recurrence of the key"""
    s, Ts = symbolic_copy(c, T, delta)
    LAST['start'] = symtm_str(s)
    k0 = key_of(s, level)
    start = [z.n for z in reps(s)]
    mv = 0
    while True:
        mv += 1
        if advance(s) and key_of(s, level) == k0:
            break
        if mv > maxmoves:
            return None
    LAST['end'] = symtm_str(s)
    end = [z.n for z in reps(s)]
    for i, (a, b) in enumerate(zip(start, end)):
        d = Lin(b) - Lin(a)
        if not d.is_const() or d.k != delta[i]:
            return None
    st = s.steps
    for v in st.c:
        if st.c[v] < 0:
            return None
    return Ts, st


class Sim:
    def __init__(s, M, log=None, levels=(1, 0)):
        s.m = Machine(M)
        s.c = Cfg(s.m, [BL], 0, [BL], 0)
        s.levels = levels
        s.hist = {lv: {} for lv in levels}
        s.rules = {lv: {} for lv in levels}
        s.nevents = 0
        s.log = log
        s.jumps = 0
        s.on_jump = None

    def counts(s):
        return [z.n for z in reps(s.c)]

    def nrules(s):
        return sum(len(r) for r in s.rules.values())

    def jump(s, rule):
        Ts, st, delta, cn0 = rule[:4]
        rs = reps(s.c)
        cn = [z.n for z in rs]
        for i, t in Ts.items():
            if cn[i] < t:
                return 0
        for i, n in enumerate(cn):
            if i not in Ts and n != cn0[i]:
                return 0
        k = None
        for i, d in enumerate(delta):
            if d < 0:
                kk = (cn[i] - Ts[i]) // (-d) + 1
                k = kk if k is None else min(k, kk)
        if k is None:
            raise RuntimeError('period with no shrinking block: the machine never halts from here')
        if k <= 1:
            return 0
        k -= 1   # keep one period for the concrete run (safety margin, still exact)
        tot = k * st.k
        for v, a in st.c.items():
            i = int(v[1:])
            x0 = cn[i] - Ts[i]
            tot += a * (k * x0 + delta[i] * k * (k - 1) // 2)
        for i, z in enumerate(rs):
            z.n = z.n + k * delta[i]
        s.c.steps += tot
        s.jumps += 1
        if s.on_jump:
            s.on_jump(rule, k)
        return k

    def try_level(s, lv, cn):
        c = s.c
        key = key_of(c, lv)
        hist = s.hist[lv]
        rule = s.rules[lv].get(key)
        if rule and s.jump(rule):
            hist.pop(key, None)
            return True
        h = hist.get(key)
        d = None
        if h is not None:
            pc, pd = h
            d = [a - b for a, b in zip(cn, pc)]
            if pd == d and any(d) and rule is None:
                res = None
                for T in (4, 16, 64):
                    try:
                        res = verify(c, lv, d, T)
                    except NeedSplit:
                        res = None
                    if res:
                        break
                if res:
                    Ts, st = res
                    rule = (Ts, st, d, list(cn), (LAST.get('start'), LAST.get('end')))
                    s.rules[lv][key] = rule
                    if s.log:
                        s.log('rule level %d delta=%s steps=%s T=%s' % (lv, d, st, Ts))
                    if s.jump(rule):
                        hist.pop(key, None)
                        return True
        hist[key] = (cn, d)
        if len(hist) > 200000:
            hist.clear()
        return False

    def run(s, maxsteps, on_event=None):
        c = s.c
        while c.steps < maxsteps:
            if not advance(c):
                continue
            s.nevents += 1
            if on_event:
                on_event(s)
            cn = s.counts()
            for lv in s.levels:
                if s.try_level(lv, cn):
                    break


def flatten(c):
    """(state, head offset, tape) with leading/trailing zeros trimmed (concrete counts only)"""
    left = []
    for z in c.L:
        if isinstance(z, Rep):
            left.extend(z.w * z.n)
        elif isinstance(z, int):
            left.append(z)
    right = []
    for z in reversed(c.R):
        if isinstance(z, Rep):
            right.extend(z.w * z.n)
        elif isinstance(z, int):
            right.append(z)
    if not isinstance(c.R[-1], (int, Rep)):
        right.append(0)
    cells = left + right
    p = len(left)
    a = 0
    while a < p and cells[a] == 0:
        a += 1
    b = len(cells) - 1
    while b > p and cells[b] == 0:
        b -= 1
    return 'ABCDEF'[c.st], p - a, ''.join(map(str, cells[a:b + 1]))


def main():
    M = sys.argv[1]
    mx = int(float(sys.argv[2]))
    S = Sim(M, log=lambda t: print(t, flush=True))

    def ev(s):
        if s.nevents % 1000 == 0:
            print(s.nevents, s.c.steps, s.jumps, s.c, flush=True)
    S.run(mx, ev)
    print('end', S.c.steps, S.c)


if __name__ == '__main__':
    main()
