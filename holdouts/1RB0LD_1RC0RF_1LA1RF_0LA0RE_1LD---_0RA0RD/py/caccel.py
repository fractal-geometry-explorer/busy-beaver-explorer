"""(24 November 2026) A copy of holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/caccel.py pointed at the digit model
of this folder (py/cdigits.py; CMACH=c2 or c1 in place of b1/b2).  The original text follows.

Counter macros for the digit model (py/cdigits.py) of 1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA--- and its twin (16 November 2026).

A copy of holdouts/1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD/py/accel.py (the algorithm of
holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/macro4.py), pointed at this machine's digit model
(py/cdigits.py): the tape read mirrored, runs of blocks 1000, walls Z, O, T (ternary digits 0, 1, 2) and others,
carry digit T.  The start is a sample of the direct run from blank tape (cdigits.direct_samples).  It numbers the
places from the head's end; py/tacc.py, which numbers them from the far end, is the one used for the long runs.

  * one sweep is one bounce of the head at the left end (a symbolic run of the machine, symtm.py);
  * Inc(k) is many sweeps at once: Inc(0) is one sweep, Inc(k) repeats Inc(k-1) until a carry reaches place k,
    derived once per key (window shape with big runs as variables), so applying it is exactly the sweeps it
    stands for, steps included;
  * Cycles: when the same macros repeat with the runs moving by the same amounts, K rounds are done at once,
    only while every run stays in the class (constant or above its threshold) that the macros were derived on.

    python3 py/caccel.py test START_STEPS|CKPT.pkl SWEEPS [b2]   # macros against plain cdigits.py sweeps
    python3 py/caccel.py run START_STEPS SECONDS [CKPT.pkl] [b2] # (START ignored when CKPT exists)
"""
import os
import pickle
import sys
import time

import importlib.util  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
DG = SPEC = None
CARRY = ZERO = None




def use(which):
    global DG, SPEC, CARRY, ZERO
    os.environ['CMACH'] = which
    path = os.path.join(HERE, 'cdigits.py')
    spec = importlib.util.spec_from_file_location('cdigits_' + which, path)
    DG = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(DG)
    SPEC = DG.SPEC
    CARRY, ZERO = ('T',), 'Z'


class Fail(Exception):
    pass


class Aff:
    """k + sum c_v * v, every variable v >= 0."""
    __slots__ = ('k', 'c')

    def __init__(self, k=0, c=None):
        self.k = k
        self.c = {v: a for v, a in (c or {}).items() if a}

    @staticmethod
    def of(x):
        return x if isinstance(x, Aff) else Aff(x)

    def __add__(self, o):
        o = Aff.of(o)
        c = dict(self.c)
        for v, a in o.c.items():
            c[v] = c.get(v, 0) + a
        return Aff(self.k + o.k, c)
    __radd__ = __add__

    def __sub__(self, o):
        return self + Aff.of(o) * (-1)

    def __rsub__(self, o):
        return Aff.of(o) - self

    def __mul__(self, a):
        assert not isinstance(a, Aff)
        return Aff(self.k * a, {v: a * b for v, b in self.c.items()})
    __rmul__ = __mul__

    def const(self):
        return not self.c

    def lo(self):
        return None if any(a < 0 for a in self.c.values()) else self.k

    def half(self, base):
        """(self - base) / 2, exactly."""
        if (self.k - base) % 2 or any(a % 2 for a in self.c.values()):
            raise Fail('half')
        return Aff((self.k - base) // 2, {v: a // 2 for v, a in self.c.items()})

    def parity(self):
        if any(a % 2 for a in self.c.values()):
            raise Fail('parity')
        return self.k % 2

    def __bool__(self):
        if self.const():
            return self.k != 0
        lo = self.lo()
        if lo is not None and lo > 0:
            return True
        raise Fail('bool')

    def __eq__(self, o):
        if isinstance(o, (tuple, list, str)) or o is None:
            return False
        d = self - Aff.of(o)
        if d.const():
            return d.k == 0
        lo = d.lo()
        if lo is not None and lo > 0:
            return False
        if all(a <= 0 for a in d.c.values()) and d.k < 0:
            return False
        raise Fail('eq')

    def __ne__(self, o):
        return not self.__eq__(o)

    def __hash__(self):
        raise TypeError

    def subs(self, env):
        return self.k + sum(a * env[v] for v, a in self.c.items())

    def __repr__(self):
        return 'Aff(%d,%s)' % (self.k, self.c)


def B(k, ib=0):
    """The threshold for a run of Inc(k) at the digit ib places from the bottom: the digits below place k cycle
    (their runs move by up to about 4^(k - ib)), the stop and the digits above it move by a few cells only."""
    return 8 + 4 ** (k - ib + 1) if ib < k else 16


BLAST = int(os.environ.get('BLAST', 16))       # the last run (it only grows)


def thresholds(k, nwin):
    return [B(k, nwin - 1 - i) for i in range(nwin)]


def cls(run, thr):
    """('c', value) or ('big', parity) at threshold thr."""
    if isinstance(run, Aff) and run.const():
        run = run.k
    if not isinstance(run, Aff):
        return ('c', run) if run < thr else ('big', run % 2 if SPEC.pairs else 0)
    lo = run.lo()
    if lo is None or lo < thr:
        raise Fail('cls')
    return ('big', run.parity() if SPEC.pairs else 0)


STEP = 2                                     # a big run is thr + parity + STEP*u (STEP = 1 without pairs)


def var_run(thr, par, name):
    return Aff(thr + par, {name: 2 if SPEC.pairs else 1})


def var_val(r, thr, par):
    if SPEC.pairs:
        return Aff.of(r).half(thr + par) if isinstance(r, Aff) else (r - thr - par) // 2
    return r - thr - par


# ------------------------------------------------------------------ the base sweep, on affine runs
def absrun(k, v):
    """digits.Spec.absrun for an affine run (pairs=True, big=6)."""
    c = cls(k, SPEC.big + 2)
    if c[0] == 'c':
        return (c[1], None), None
    if not SPEC.pairs:
        return (SPEC.big, v), (v, k - SPEC.big)
    base = SPEC.big + c[1]
    return (base, v), (v, Aff.of(k).half(base) if isinstance(k, Aff) else (k - base) // 2)


def sweep_sym(state, full):
    """digits.Spec.sweep with affine runs; `full`: the window is the whole tape (its left end is the tape's)."""
    s = SPEC
    ctx0, digits, last, end = state
    n = len(digits)
    j = 0
    while j < n and digits[n - 1 - j][0] in CARRY:
        j += 1
    w = min(n, j + 1)
    if j == n and not full:
        raise Fail('chain leaves the window')
    while True:
        vis = digits[n - w:]
        usepre = (w == n) and full
        env = {}
        rd = []
        for i, (sh, k) in enumerate(vis):
            (b, v), e = absrun(k, 'v%d' % i)
            rd.append((sh, b, v))
            if e:
                env[e[0]] = e[1]
        (lb, lv), e = absrun(last, 'z')
        if e:
            env[e[0]] = e[1]
        key = (usepre, tuple((sh, b if v is None else ('big', b)) for sh, b, v in rd), (lb if lv is None else ('big', lb)), end)
        if key in s.memo:
            res = s.memo[key]
            s.stats['hit'] += 1
        else:
            s.stats['sym'] += 1
            c = s.build(not usepre, rd, (lb, lv), end)
            try:
                c = DG.symtm.run(s.m, c, s.sample, max_moves=50000, rotate=True)
                vs = [v for _, _, v in rd if v] + ([lv] if lv else [])
                it = s.interpret(c, vs)
                res = ('ok', it) if it else ('unparsed', c)
            except DG.symtm.TouchContext:
                res = ('touch',)
            except DG.symtm.Halted as ex:
                res = ('halt', str(ex))
            except DG.symtm.NeedSplit as ex:
                res = ('split', str(ex))
            except RuntimeError as ex:
                res = ('limit', str(ex))
            s.memo[key] = res
        if res[0] in ('touch', 'unparsed') and w < n:
            w += 1
            continue
        if res[0] in ('touch', 'unparsed') and not full:
            raise Fail('window')
        if res[0] != 'ok':
            raise Fail('rule ' + res[0])
        nctx, ndigs, nlast, nend, steps = res[1]

        def ev(l):
            return l[0] + sum(a * env[v] for v, a in l[1].items())
        newd = s.canon_digits(digits[:n - w] + [(sh, ev(l)) for sh, l in ndigs])
        st = steps.k + sum(a * env.get(v, 0) for v, a in steps.c.items())
        return (ctx0 and nctx, newd, ev(nlast), nend), st


# ------------------------------------------------------------------ keys and macros
MEMO = {}
STATS = {'derived': 0, 'failed': 0, 'applied': 0}


def chain(digits):
    """The number of carry digits at the bottom (the stop of the next sweep is at this index from the bottom)."""
    n = len(digits)
    j = 0
    while j < n and digits[n - 1 - j][0] in CARRY:
        j += 1
    return j


def window_key(state, k, full_outer=True):
    """(key, start index of the window) for Inc(k) on `state`, or raises Fail.  The window: from one digit above
    the stop of the carry that ends Inc(k) (the first non-carry digit at index >= k from the bottom) down."""
    ctx, digits, last, end = state
    n = len(digits)
    if k > n - 1:
        raise Fail('k')
    sidx = k
    while sidx < n and digits[n - 1 - sidx][0] in CARRY:
        sidx += 1
    if sidx >= n:
        raise Fail('no stop')
    start = max(n - 1 - sidx - 1, 0)
    full = start == 0 and full_outer
    win = digits[start:]
    th = thresholds(k, len(win))
    kk = (k, full, ctx, end, tuple((sh, cls(r, t)) for (sh, r), t in zip(win, th)), cls(last, BLAST))
    return kk, start


REPMAX = 8


def same(a, b):
    if a[0] != b[0]:
        return False
    x, y = a[1], b[1]
    if isinstance(x, Aff) or isinstance(y, Aff):
        d = Aff.of(x) - Aff.of(y)
        return d.const() and d.k == 0
    return x == y


def reach_of(before, after):
    """The index from the bottom of the highest digit of `before` that the sweep changed (digits above it are
    untouched: the common prefix from the top)."""
    p = 0
    while p < len(before) and p < len(after) and same(before[p], after[p]):
        p += 1
    return len(before) - 1 - p


def derive(key):
    """The macro for `key`: ((ctx, window, last, end), steps, sweeps, reach) with Aff in the key's variables, or
    None.  Inc(0) is one sweep (reach: the index from the bottom of the highest digit it changes, at least its
    stop); Inc(k) repeats Inc(k-1) until a sweep reaches index >= k."""
    k, full, ctx, end, win, lastc = key
    th = thresholds(k, len(win))
    digs = []
    for i, (sh, c) in enumerate(win):
        digs.append((sh, c[1] if c[0] == 'c' else var_run(th[i], c[1], 'u%d' % i)))
    last = lastc[1] if lastc[0] == 'c' else var_run(BLAST, lastc[1], 'z')
    state = (ctx, digs, last, end)
    try:
        if k == 0:
            st, steps = sweep_sym(state, full)
            reach = max(reach_of(digs, st[1]), chain(digs))
            nsw = 1
        else:
            st, steps, nsw = state, Aff(0), 0
            for _ in range(REPMAX):
                st, s1, n1, reach = apply_sym(st, k - 1, full)
                steps = steps + s1
                nsw += n1
                if reach >= k:
                    break
            else:
                return None
    except (Fail, AssertionError):
        return None
    return st, Aff.of(steps), nsw, reach


MEMO_MAX = int(os.environ.get('MEMO_MAX', 40000))
SPEC_MEMO_MAX = int(os.environ.get('SPEC_MEMO_MAX', 40000))                        # the window rules of digits.py: forgotten too (derived again when needed)


def get_macro(key):
    if key not in MEMO:
        if len(MEMO) > MEMO_MAX:                 # memory: forget all macros (they are derived again when needed)
            MEMO.clear()
        if len(SPEC.memo) > SPEC_MEMO_MAX:
            SPEC.memo.clear()
            STATS['cleared'] = STATS.get('cleared', 0) + 1
        m = derive(key)
        MEMO[key] = m
        STATS['derived' if m else 'failed'] += 1
    return MEMO[key]


def env_of(key, state, start):
    """Values of the key's variables for (part of) a state."""
    k, full, ctx, end, win, lastc = key
    th = thresholds(k, len(win))
    env = {}
    digits = state[1][start:]
    for i, ((sh, c), (_, r)) in enumerate(zip(win, digits)):
        if c[0] == 'big':
            env['u%d' % i] = var_val(r, th[i], c[1])
    if lastc[0] == 'big':
        env['z'] = var_val(state[2], BLAST, lastc[1])
    return env


def subst(x, env):
    """x (int or Aff in macro variables) with env (ints or Aff)."""
    if not isinstance(x, Aff):
        return x
    out = x.k
    for v, a in x.c.items():
        out = out + env[v] * a if isinstance(env[v], Aff) else out + a * env[v]
    return out


def apply_macro(m, key, state, start):
    (octx, odig, olast, oend), steps, nsw, reach = m
    env = env_of(key, state, start)
    ctx, digits, last, end = state
    nd = SPEC.canon_digits(digits[:start] + [(sh, subst(r, env)) for sh, r in odig])
    return (octx, nd, subst(olast, env), oend), subst(steps, env), nsw, reach


def apply_sym(state, k, full):
    """Inc(k) on a symbolic window state (inside a derivation)."""
    key, start = window_key(state, k, full)
    m = get_macro(key)
    if m is None:
        raise Fail('no inner macro')
    return apply_macro(m, key, state, start)


def apply_conc(state, k):
    """Inc(k) on a concrete state, or None."""
    try:
        key, start = window_key(state, k)
    except Fail:
        return None
    m = get_macro(key)
    if m is None:
        return None
    STATS['applied'] += 1
    try:
        return apply_macro(m, key, state, start) + ((key, LEVEL[0]),)
    except (Fail, AssertionError):
        return None


KMAX = 64
CAPK = None                                   # test: cut the cycle skips to at most CAPK rounds
LASTKEY = [None]
LEVEL = [0]                                   # the reach of the last carry (the driver's precondition for Inc(k))


def advance(state):
    """(state, steps, sweeps) by the largest macro that applies, or one plain sweep."""
    t = min(LEVEL[0], KMAX, len(state[1]) - 1)
    for k in range(t, 0, -1):
        r = apply_conc(state, k)
        if r is not None:
            LEVEL[0] = r[3]
            LASTKEY[0] = r[4]
            return r[0], r[1], r[2]
    LASTKEY[0] = None
    j = chain(state[1])
    r = SPEC.sweep(state, carry=CARRY)
    if r[0] != 'ok':
        return ('STOP', r), None, None
    LEVEL[0] = max(j, reach_of(state[1], r[1][1]))
    return r[1], r[2], 1


# ------------------------------------------------------------------ cycles of macros
def in_region(key, state, start):
    """Is `state` in the region of `key` (the classes of the key hold)?"""
    k, full, ctx, end, win, lastc = key
    digits = state[1][start:]
    if len(digits) != len(win):
        return False
    th = thresholds(k, len(win))
    for (sh, c), (sh2, r), t in zip(win, digits, th):
        if sh != sh2 or cls(r, t) != c:
            return False
    return cls(state[2], BLAST) == lastc


class Cycles:
    """Landing points of macros.  When the last p macros (p <= PMAX) have the same keys (and the same driver
    levels) as the p before, and the state moved by the same D in both rounds (runs only), the round is an affine
    map (a composition of the same macros), and it moves every state by D on the region where all p keys hold.
    That region is convex and the states S + jD are on a line, so if the round's p intermediate states are in their
    regions for the first and for the K-th round, they are for all rounds in between: K rounds are done at once.
    The steps of a round are affine in its state, hence affine in j: their sum is exact."""
    PMAX = 6

    def __init__(self):
        self.h = []                 # (key and level, state before, steps, sweeps)
        self.skips = 0
        self.rounds = 0

    def add(self, keylev, before, steps, nsw):
        self.h.append((keylev, before, steps, nsw))
        if len(self.h) > 2 * self.PMAX + 1:
            self.h.pop(0)

    def clear(self):
        self.h = []

    def runs(self, st):
        return [r for _, r in st[1]] + [st[2]]

    def shape(self, st):
        return (st[0], tuple(sh for sh, _ in st[1]), st[3])

    def try_skip(self, cur, capk=None):
        h = self.h
        for p in range(1, self.PMAX + 1):
            if len(h) < 2 * p:
                break
            A, Bv = h[-2 * p:-p], h[-p:]
            if any(x[0] is None for x in A + Bv) or [x[0] for x in A] != [x[0] for x in Bv]:
                continue
            Sa, Sb, Sc = A[0][1], Bv[0][1], cur
            if not (self.shape(Sa) == self.shape(Sb) == self.shape(Sc)):
                continue
            ra, rb, rc = self.runs(Sa), self.runs(Sb), self.runs(Sc)
            D = [y - x for x, y in zip(rb, rc)]
            if D != [y - x for x, y in zip(ra, rb)] or not any(D):
                continue
            # every intermediate state moved by D as well (then each partial composition fixes D)
            if any(self.shape(x[1]) != self.shape(y[1]) or
                   [v - u for u, v in zip(self.runs(x[1]), self.runs(y[1]))] != D for x, y in zip(A, Bv)):
                continue
            # K: every intermediate state of the next rounds stays in its region
            K = 1 << 62
            for (keylev, before, _, _) in Bv:
                key = keylev[0]
                k, full, ctx, end, win, lastc = key
                _, start = window_key(before, k)
                rs = self.runs(before)
                ws = list(range(start, len(before[1]))) + [len(before[1])]
                classes = [c for _, c in win] + [lastc]
                ths = thresholds(k, len(win)) + [BLAST]
                for idx, c, thr in zip(ws, classes, ths):
                    d = D[idx]
                    if c[0] == 'c':
                        if d != 0:
                            K = 0
                        continue
                    if d % 2 and SPEC.pairs:
                        K = 0
                        continue
                    if d < 0:
                        # before + (j+1) d >= thr + par for j = 0..K-1  (this round's state is j = -1)
                        K = min(K, (rs[idx] - thr - c[1]) // (-d))
            covered = set()
            for (keylev, before, _, _) in Bv:
                _, start = window_key(before, keylev[0][0])
                covered.update(range(start, len(before[1]) + 1))
            if any(d for i, d in enumerate(D) if i not in covered):
                continue                                 # runs outside every window cannot move
            if K < 2:
                continue
            if capk:
                K = min(K, capk)
            # check the regions at the last round explicitly (j = K-1, i.e. before + K*D)
            ok = True
            for (keylev, before, _, _) in Bv:
                key = keylev[0]
                bk = self.moved(before, D, K)
                kk, start = window_key(bk, key[0])
                if kk != key:
                    ok = False
                    break
            if not ok:
                continue
            sig_b = sum(x[2] for x in Bv)
            sig_a = sum(x[2] for x in A)
            ds = sig_b - sig_a
            steps = K * sig_b + ds * K * (K + 1) // 2
            nsw = K * sum(x[3] for x in Bv)
            self.skips += 1
            self.rounds += K
            self.h = []
            return self.moved(cur, D, K), steps, nsw
        return None

    def moved(self, st, D, K):
        digs = [(sh, r + K * d) for (sh, r), d in zip(st[1], D)]
        return (st[0], digs, st[2] + K * D[-1], st[3])


def register(st):
    """Walls named by AutoSpec (b<a>_<b>, one block 1^a 0^b) in a loaded state: register them again."""
    for sh, _ in st[1]:
        if sh not in SPEC.shapes and sh[0] == 'b':
            a, b = sh[1:].split('_')
            SPEC.shapes[sh] = [(int(a), int(b))]
    SPEC.order = sorted(SPEC.shapes.items(), key=lambda kv: -len(kv[1]))


def start_state(steps):
    last = None
    for step, cells in DG.direct_samples(int(float(steps))):
        last = (step, cells)
    a = SPEC.parse_cells(last[1])
    return (a[0], list(a[1]), a[2], a[3]), last[0]


def test(start_steps, sweeps):
    if start_steps.endswith('.pkl'):
        st, T, _ = pickle.load(open(start_steps, 'rb'))
        register(st)
    else:
        st, T = start_state(start_steps)
    ref, RT = st, T
    done = 0
    nref = 0
    checks = 0
    t0 = time.time()
    cyc = Cycles()
    while done < sweeps:
        st2, s2, n = advance(st)
        if s2 is None:
            print('STOP', st2)
            return False
        cyc.add(None if LASTKEY[0] is None else LASTKEY[0], st, s2, n)
        st, T, done = st2, T + s2, done + n
        r = cyc.try_skip(st, capk=CAPK)
        if r:
            st, T, done = r[0], T + r[1], done + r[2]
        while nref < done:
            r = SPEC.sweep(ref, carry=CARRY)
            assert r[0] == 'ok', r
            ref, RT, nref = r[1], RT + r[2], nref + 1
        if (ref[0], ref[1], ref[2], ref[3]) != (st[0], st[1], st[2], st[3]) or RT != T:
            print('MISMATCH after', done, 'sweeps', DG.show(st)[:300], '|', DG.show(ref)[:300], T, RT)
            return False
        checks += 1
    print('OK: %d landing points (%d sweeps) agree with plain sweeps, states and steps; macros %s; %d cycle skips (%d rounds); %.0f s' % (
        checks, done, STATS, cyc.skips, cyc.rounds, time.time() - t0))
    return True


def run(start_steps, seconds, ckpt=None):
    if ckpt and os.path.exists(ckpt):
        st, T, done = pickle.load(open(ckpt, 'rb'))
        register(st)
    else:
        st, T = start_state(start_steps)
        done = 0
    print('start', T, DG.show(st)[:400], flush=True)
    t0 = time.time()
    last = t0
    nd = len(st[1])
    cyc = Cycles()
    while time.time() - t0 < seconds:
        if len(SPEC.memo) > SPEC_MEMO_MAX:
            SPEC.memo.clear()
        st2, s2, n = advance(st)
        if s2 is None:
            print('STOP after', done, 'sweeps at step', T, st2, flush=True)
            break
        old = st
        cyc.add(LASTKEY[0], st, s2, n)
        st, T, done = st2, T + s2, done + n
        r = cyc.try_skip(st)
        if r:
            st, T, done = r[0], T + r[1], done + r[2]
        if len(st[1]) != nd or st[1][:1] != old[1][:1]:
            nd = len(st[1])
            print('%d sweeps, step %d (%.3e): %s' % (done, T, float(T), DG.show(st)[:400]), flush=True)
        if time.time() - last > 600:
            last = time.time()
            print('AT %d sweeps, step %d (%.3e) %s macros %s cycle skips %d' % (done, T, float(T), DG.show(st)[:400], STATS, cyc.skips), flush=True)
            if ckpt:
                pickle.dump((st, T, done), open(ckpt + '.tmp', 'wb'))
                os.replace(ckpt + '.tmp', ckpt)
    print('END %d sweeps, step %d (%.3e) %s macros %s' % (done, T, float(T), DG.show(st)[:600], STATS), flush=True)
    if ckpt:
        pickle.dump((st, T, done), open(ckpt + '.tmp', 'wb'))
        os.replace(ckpt + '.tmp', ckpt)


if __name__ == '__main__':
    a = sys.argv[2:]
    sys.setrecursionlimit(10000)
    use('c1' if 'c1' in a else 'c2')
    a = [x for x in a if x not in ('c1', 'c2')]
    if sys.argv[1] == 'test':
        if len(a) > 2:
            CAPK = int(a[2])
        sys.exit(0 if test(a[0], int(float(a[1]))) else 1)
    run(a[0], float(a[1]), a[2] if len(a) > 2 else None)
