"""An exact accelerator for the digit model (py/cdigits.py) of the draining ternary odometer pair
1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD (c2) and 1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB (c1) (24 November 2026).

State: cdigits.py's sample, (ctx, digits, last, end), digits = [(wall, run)] from the far end (index 0) to the head.

Two ingredients, both exact:

1. The counter rule (checked against symbolic sweeps by `test`).  Let the bottom block be the longest run of digits
   at the head's end whose walls are Z, O, T (digits 0, 1, 2; the head's end is the least significant) and whose
   runs are all >= THR.  A sweep inside the block is one ternary increment: the trailing T digits (the chain, places
   0..q-1) become Z and the stop digit at place q goes up by one.  Then
       stop on O: the stop digit's run loses 1;   stop on Z: the run of place q-1 gains 1 (the last run if q = 0);
       the last run L always gains 1;
       steps = 10 * (sum of the chain's runs) + 28 q + 10 L + 42      (L and the runs before the sweep).
   So the 3^p - 1 increments that take places 0..p-1 from all Z to all T are an affine map, a translation of the
   runs plus a step count affine in them (`inner(p)`), and any number of increments short of a carry out of the
   block is a composition of O(places) such maps (`advance`).  A macro step jumps to just before the carry out.

2. Cycles.  Everything else is one symbolic sweep (caccel.sweep_sym, a run of the machine).  A shape is the state with
   every run >= THR replaced by `big` (and exact below).  When the sequence of shapes of the macro steps repeats
   twice with period P, every step of the period is the same rule (a translation of the big runs, steps affine in
   them), so the state at phase t of period m is the state at phase t of period 0 plus m times its change over one
   period.  M periods are then done at once, M as large as keeps every big run >= THR at every phase, with the step
   count summed as an arithmetic series.

    python3 py/oacc.py test START_STEPS SWEEPS [c1]     jumps and cycles against plain sweeps, states and steps
    python3 py/oacc.py run START|STATE.txt SECONDS OUT.txt [c1]
"""
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import caccel as C  # noqa: E402

THR = int(os.environ.get('OTHR', 64))
PMAX = int(os.environ.get('OPMAX', 200000))       # longest period looked for, in macro steps
MAXM = int(os.environ['OMAXM']) if os.environ.get('OMAXM') else None  # at most this many periods per cycle jump (tests)
VAL = {'Z': 0, 'O': 1, 'T': 2}
WALL = 'ZOT'
STATS = {'sweeps': 0, 'jumps': 0, 'jumped_sweeps': 0, 'cycles': 0, 'cycle_sweeps': 0}


# ---------------------------------------------------------------- 1. the counter rule in closed form
class Tr:
    """runs (L, r_0 .. r_{D-1}) -> runs + d; steps = a + b . runs (runs at the start); n increments."""
    __slots__ = ('d', 'a', 'b', 'n')

    def __init__(self, d, a, b, n):
        self.d, self.a, self.b, self.n = d, a, b, n

    def then(self, o):
        m = max(len(self.d), len(o.d))
        d1 = self.d + [0] * (m - len(self.d))
        b1 = self.b + [0] * (m - len(self.b))
        d2 = o.d + [0] * (m - len(o.d))
        b2 = o.b + [0] * (m - len(o.b))
        return Tr([x + y for x, y in zip(d1, d2)], self.a + o.a + sum(x * y for x, y in zip(b2, d1)),
                  [x + y for x, y in zip(b1, b2)], self.n + o.n)


def single(q, dq):
    """One increment with stop at place q (digit dq in {0, 1}), chain places 0..q-1.  Vector index 0 is L, 1 + p is
    the run of place p."""
    m = q + 2
    d = [0] * m
    b = [0] * m
    b[0] = 10
    for p in range(q):
        b[1 + p] = 10
    d[0] += 1
    if dq == 1:
        d[1 + q] -= 1
    elif q >= 1:
        d[q] += 1
    else:
        d[0] += 1
    return Tr(d, 28 * q + 42, b, 1)


_INNER = {0: Tr([0], 0, [0], 0)}


def inner(p):
    """places 0..p-1 from all Z to all T: 3^p - 1 increments."""
    if p not in _INNER:
        x = inner(p - 1)
        _INNER[p] = x.then(single(p - 1, 0)).then(x).then(single(p - 1, 1)).then(x)
    return _INNER[p]


def advance(dig, K):
    """dig: digit values by place (0 = least significant), changed in place; K increments, none of which carries
    out of the block.  Returns the composed Tr."""
    tr = Tr([0], 0, [0], 0)
    D = len(dig)
    while K > 0:
        tz = 0
        while tz < D and dig[tz] == 0:
            tz += 1
        p = tz
        while p > 0 and 3 ** p - 1 > K:
            p -= 1
        if p > 0 and 3 ** p - 1 == K:
            tr = tr.then(inner(p))
            for i in range(p):
                dig[i] = 2
            return tr
        while p > 0 and 3 ** p > K:
            p -= 1
        tr = tr.then(inner(p))
        for i in range(p):
            dig[i] = 2
        q = 0
        while q < D and dig[q] == 2:
            q += 1
        if q >= D:
            raise RuntimeError('carry out of the block')
        tr = tr.then(single(q, dig[q]))
        for i in range(q):
            dig[i] = 0
        dig[q] += 1
        K -= 3 ** p
    return tr


def block(st):
    """(D, index of the block's top digit) of the bottom block (see the module text)."""
    digits = st[1]
    n = len(digits)
    D = 0
    while D < n - 1 and digits[n - 1 - D][0] in WALL and digits[n - 1 - D][1] >= THR:
        D += 1
    return D


def _try(digits, last, D, K):
    n = len(digits)
    dig = [VAL[digits[n - 1 - p][0]] for p in range(D)]
    tr = advance(dig, K)
    R = [last] + [digits[n - 1 - p][1] for p in range(D)]
    d = tr.d + [0] * (D + 1 - len(tr.d))
    b = tr.b + [0] * (D + 1 - len(tr.b))
    R2 = [x + y for x, y in zip(R, d)]
    return dig, R2, tr.a + sum(x * y for x, y in zip(b, R)), tr.n


def jump(st):
    """The macro step to just before the carry out of the bottom block ('j'), or, if a run of the block would fall
    below THR before that, the longest jump that keeps every run >= THR ('p'), or None.  Runs move by at most 1
    against their trend inside a jump, so a run >= THR at both ends stays >= THR - 1 in between.
    Returns (state, steps, sweeps, kind)."""
    ctx, digits, last, end = st
    if last < THR:
        return None
    D = block(st)
    if D < 1:
        return None
    n = len(digits)
    dig = [VAL[digits[n - 1 - p][0]] for p in range(D)]
    v = sum(x * 3 ** p for p, x in enumerate(dig))
    K = 3 ** D - 1 - v
    if K < 2:
        return None
    kind = 'j'
    dig2, R2, steps, nsw = _try(digits, last, D, K)
    if min(R2[1:]) < THR:
        kind = 'p'
        lo, hi = 0, K          # f(lo) ok, f(hi) not
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if min(_try(digits, last, D, mid)[1][1:]) >= THR:
                lo = mid
            else:
                hi = mid
        if lo < 2:
            return None
        dig2, R2, steps, nsw = _try(digits, last, D, lo)
    nd = list(digits[:n - D]) + [(WALL[dig2[p]], R2[1 + p]) for p in reversed(range(D))]
    return (ctx, nd, R2[0], end), steps, nsw, kind


def sweep(st):
    r = C.sweep_sym(st, True)
    return r[0], r[1]


def macro(st):
    """(state, steps, sweeps, kind)"""
    j = jump(st)
    if j:
        return j
    s2, s = sweep(st)
    return s2, s, 1, 's'


# ---------------------------------------------------------------- 2. cycles
def shape(st):
    ctx, digits, last, end = st
    return (ctx, end, tuple((w, r if r < THR else -1) for w, r in digits), last if last < THR else -1)


def runs(st):
    return [r for _, r in st[1]] + [st[2]]


class Engine:
    def __init__(self, st, T, sweeps):
        self.st, self.T, self.n = st, T, sweeps
        self.reset()

    def reset(self):
        self.hist = []          # (shape hash, state, steps, sweeps) before each macro step
        self.seen = {}

    def step(self):
        st = self.st
        h = hash(shape(st))
        if self.hist and self.hist[-1][4] == 'p':
            h = ('p', len(self.hist))          # no cycle runs through a partial jump
        self.hist.append([h, st, self.T, self.n, None])
        k = len(self.hist) - 1
        prev = self.seen.get(h)
        self.seen[h] = k
        if prev is not None and self.try_cycle(prev, k):
            return 'c'
        if len(self.hist) > 2 * PMAX + 2:
            self.reset()
        s2, s, nsw, kind = macro(st)
        self.hist[-1][4] = kind
        self.st, self.T, self.n = s2, self.T + s, self.n + nsw
        if kind in 'jp':
            STATS['jumps'] += 1
            STATS['jumped_sweeps'] += nsw
        else:
            STATS['sweeps'] += 1
        return kind

    def try_cycle(self, i, k):
        P = k - i
        if i - P < 0:
            return False
        H = self.hist
        if any(H[i - P + t][0] != H[i + t][0] for t in range(P + 1)):
            return False
        # two periods [i-P, i] and [i, k]; same shapes.  Per phase t, the change of every run over one period.
        lim = None
        for t in range(P):
            a, b = runs(H[i - P + t][1]), runs(H[i + t][1])
            if len(a) != len(b):
                return False
            for x, y in zip(a, b):
                dd = y - x
                if x < THR:
                    if dd:
                        return False
                    continue
                if dd < 0:
                    # phase t of period m (m = 0 is H[i+t]) has y + m*dd >= THR
                    mm = (y - THR) // (-dd)
                    lim = mm if lim is None else min(lim, mm)
        a, b = runs(H[i][1]), runs(H[k][1])
        if any(x < THR and x != y for x, y in zip(a, b)):
            return False
        # M more periods from H[k]: phase t of period j (j = 1..M, period 0 = [i,k]) is y + j*dd >= THR
        if lim is None:
            # no run of the period ever decreases: the period repeats for ever
            raise SystemExit('PERIOD WITHOUT END at %d sweeps, step %d: %s' % (self.n, self.T, C.DG.show(self.st)))
        M = lim - 1
        if MAXM is not None:
            M = min(M, MAXM)
        if M < 2:
            return False
        s0 = H[i][2] - H[i - P][2]
        s1 = H[k][2] - H[i][2] if k < len(H) else None
        s1 = self.T - H[i][2]
        n1 = self.n - H[i][3]
        n0 = H[i][3] - H[i - P][3]
        if n1 != n0:
            return False
        ds = s1 - s0
        # periods j = 1..M after the current one cost s1 + j*ds
        steps = M * s1 + ds * M * (M + 1) // 2
        ctx, digits, last, end = self.st
        d_runs = [y - x for x, y in zip(a, b)]
        cur = runs(self.st)
        new = [c + M * dd for c, dd in zip(cur, d_runs)]
        self.st = (ctx, [(w, r) for (w, _), r in zip(digits, new[:-1])], new[-1], end)
        self.T += steps
        self.n += M * n1
        STATS['cycles'] += 1
        STATS['cycle_sweeps'] += M * n1
        self.reset()
        return True


# ---------------------------------------------------------------- driver
def plain(st, T, nsw):
    for _ in range(nsw):
        st, s = sweep(st)
        T += s
    return st, T


def test(start, total):
    st, T = C.start_state(start)
    st0, T0 = st, T
    nj = 0
    e = Engine(st, T, 0)
    done = 0
    ok = True
    while done < total:
        st, T = e.st, e.T
        kind = e.step()
        nsw = e.n - done
        if kind in ('j', 'p', 'c'):
            ref, RT = plain(st, T, nsw)
            if ref != e.st or RT != e.T:
                print('MISMATCH', kind, nsw, C.DG.show(e.st)[:300], '|', C.DG.show(ref)[:300], e.T, RT)
                ok = False
                break
            nj += 1
        done = e.n
    print('%s: %d jumps/cycles checked against plain sweeps (%d sweeps from step %d), %s' % (
        'OK' if ok else 'FAIL', nj, done, T0, STATS))
    return ok


def load(path):
    """A state line `sweeps steps [r]W ... [last] END` as written by `run`."""
    import re
    w = open(path).read().split()
    toks = w[2:]
    digits = []
    for t in toks[:-2]:
        m = re.match(r'^\[(\d+)\](\w+)$', t)
        digits.append((m.group(2), int(m.group(1))))
    st = (False, digits, int(toks[-2][1:-1]), toks[-1])
    C.register(st)
    return int(w[0]), int(w[1]), st


def run(start, seconds, out, every=60):
    if os.path.exists(str(start)):
        n0, T, st = load(start)
    else:
        (st, T), n0 = C.start_state(start), 0
    e = Engine(st, T, n0)
    t0 = last = time.time()
    lastshape = None
    ev = open(os.environ['OEVENTS'], 'a') if os.environ.get('OEVENTS') else None
    while time.time() - t0 < seconds:
        kind = e.step()
        sh = (len(e.st[1]), tuple(w for w, r in e.st[1] if w not in WALL))
        if sh != lastshape:
            lastshape = sh
            if ev:
                ev.write('%d %d %s\n' % (e.n, e.T, C.DG.show(e.st)))
                ev.flush()
        if time.time() - last > every:
            last = time.time()
            print('AT %d sweeps, step %d (%.4e) %s %s' % (e.n, e.T, float(e.T), C.DG.show(e.st)[:500], STATS),
                  flush=True)
            with open(out, 'w') as f:
                f.write('%d %d %s\n' % (e.n, e.T, C.DG.show(e.st)))
    with open(out, 'w') as f:
        f.write('%d %d %s\n' % (e.n, e.T, C.DG.show(e.st)))
    print('END %d sweeps, step %d (%.4e) %s %s' % (e.n, e.T, float(e.T), C.DG.show(e.st), STATS), flush=True)


if __name__ == '__main__':
    a = sys.argv[2:]
    C.use('c1' if 'c1' in a else 'c2')
    a = [x for x in a if x not in ('c1', 'c2')]
    if sys.argv[1] == 'test':
        sys.exit(0 if test(a[0], int(float(a[1]))) else 1)
    run(a[0], float(a[1]), a[2])
