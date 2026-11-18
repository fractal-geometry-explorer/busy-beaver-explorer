"""A lean accelerator for the digit model of 1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA--- (b1) and of its twin
1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC--- (b2) (17 November 2026).

The state is the digit list of py/cdigits.py (the tape read mirrored at the left end: index 0 is the far end, the
original right end).  It is split in three parts:

  * the far zone, indices 0..h-1: index 0 and everything above the first irregular digit; it changes only when a
    carry reaches it, and those sweeps are always run exactly;
  * the counter U = indices h..N-1: walls Z, O, T (digits 0, 1, 2), every run >= BIGU (1);
  * N, a digit with a big run (`structure`), and the low system S below it (in the third regime the pair a, b and the
    gadget; after 2.58e54 steps a deeper nest of them), together with the wall of N.

Rules used (each one is checked, see `test` and the README):

  * a sweep whose carry chain passes the T digits q..s+1 and stops at s turns them into Z, raises digit s by one, and
    takes f(d_s) blocks from the run of s+1 (f(Z) = 1, f(O) = 2); a run in the chain costs 12 r + 16 steps, a stop
    on O costs 2 steps less than a stop on Z;
  * S evolves on its own: it sees of the rest only N's wall, while N's run stays big.  So S is periodic, and one
    period sends E carries out of N into U, adds a fixed amount to N's run (besides the f-losses at N's own
    carries), and costs steps that are affine in N's run.

A period of S is found by exact sweeps (cdigits.SPEC.sweep, a symbolic run of the machine) and Brent's cycle search
on S.  Every sweep whose window reaches N is run twice, the second time with N's run larger by one: both must give the
same tape apart from N's run, which also gives the coefficient of N's run in that sweep's step count.  T periods are then done at once in closed form: ternary addition of T*E at the bottom of
U, the f-losses in closed form, and the step sums as arithmetic series.  T is the largest number of periods for which
no carry leaves U, every run of U stays >= RMIN and N's run stays big; the event that blocks the next period is then
run exactly.

Cycle reuse (18 November 2026): a learned period keeps, for every phase, the hash of S's state and the base step
count so far, and at each recorded sweep a copy of S and N's wall.  When the next period is blocked, the part of it
before the blocking sweep is jumped in closed form too (`max_prefix`), the blocking sweep and the far-zone sweeps
after it run exactly, and S goes on with the same period rotated to its new phase (`rotate`), checked by the hash.
Learned periods are cached (`CACHE`, LCACHE entries), and while S settles after a collapse each sweep looks its state
up in the cache, so no cycle is learned twice.

    python3 py/lean.py test CKPT.pkl [b2]                      jumps of 1, 2, 3, 5, 13 periods against exact sweeps
    python3 py/lean.py verify CKPT.pkl|lineK FULLLOG [b2]      every line of a tacc.py FULLLOG, states and steps
    python3 py/lean.py run CKPT.pkl|STATE.txt SECONDS OUT.pkl [b2]   (STATELOG=FILE: one state line per jump)
"""
import os
import pickle
import sys
import time
from array import array

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'py'))
import caccel as C  # noqa: E402

BIG = int(os.environ.get('LBIG', 1000))     # N: the last digit with a run >= BIG
BIGPREF = int(os.environ.get('LBIGPREF', 10 ** 5))
BIGNB = int(os.environ.get('LBIGNB', 10 ** 4))
BIGU = int(os.environ.get('LBIGU', 1))   # U: walls Z/O/T with runs >= BIGU
RMIN = int(os.environ.get('LRMIN', 1))                                       # a jump keeps every run of U >= RMIN
DEBUG = os.environ.get('LDEBUG')
LEARN_MAX = int(float(os.environ.get('LEARN_MAX', 3e7)))
VAL = {'Z': 0, 'O': 1, 'T': 2}
WALL = 'ZOT'
F = (1, 2, 0)                                    # blocks taken from the topmost T of a chain, by the stop digit


def sweep(st):
    r = C.SPEC.sweep(st, carry=C.CARRY)
    if r[0] != 'ok':
        raise RuntimeError('sweep failed: %s' % (r[0],))
    return r[1], r[2]


# ---------------------------------------------------------------- closed forms for f-losses
def lf(d, e):
    """sum_{i<e} F[(d+i)%3]"""
    s = 3 * (e // 3)
    for i in range(e % 3):
        s += F[(d + i) % 3]
    return s


def eps(d, r):
    return lf(d, r) - r


def sum_lf(d, c):
    """sum_{e<c} lf(d, e)"""
    if c <= 0:
        return 0
    return c * (c - 1) // 2 + (c // 3) * sum(eps(d, r) for r in range(3)) + sum(eps(d, r) for r in range(c % 3))


def count_phase(d, n, ph):
    """#{i < n : (d+i)%3 == ph}"""
    k = (ph - d) % 3
    return 0 if n <= k else (n - k + 2) // 3


# ---------------------------------------------------------------- structure
def structure(st):
    """(h, N) or None.  N: the last digit with a run >= BIGPREF whose upper neighbour is a counter digit (wall Z/O/T)
    with a run >= BIGNB; failing that, the last digit with a run >= BIGPREF (if there is none: >= BIG) whose upper
    neighbour is a counter digit with run >= BIGU.  U = h..N-1, the longest stretch of counter digits (runs >= BIGU)
    above N, never including index 0 (the far end: a carry there is always run exactly)."""
    dig = st[1]

    def ok(N, nb):
        return N >= 2 and dig[N - 1][0] in WALL and dig[N - 1][1] >= nb

    cand = None
    for N in range(len(dig) - 1, 0, -1):
        if dig[N][1] >= BIGPREF and ok(N, BIGNB):
            cand = N
            break
    if cand is None:
        for big in (BIGPREF, BIG):
            for N in range(len(dig) - 1, -1, -1):
                if dig[N][1] >= big:
                    break
            else:
                continue
            if not ok(N, BIGU):
                return None
            cand = N
            break
    if cand is None:
        return None
    N = h = cand
    while h - 1 >= 1 and dig[h - 1][0] in WALL and dig[h - 1][1] >= BIGU:
        h -= 1
    return h, N


def skey(st, N):
    ctx, dig, last, end = st
    return (ctx, dig[N][0], tuple(dig[N + 1:]), last, end)


def u_chain_cost(dig, N, h):
    """steps of the part of a chain that leaves N upwards, and the stop index (12r+16 per T, -2 for a stop on O)"""
    q = N - 1
    c = 0
    while q >= h and dig[q][0] == 'T':
        c += 12 * dig[q][1] + 16
        q -= 1
    if q < h:
        return None, q
    return c + (-2 if dig[q][0] == 'O' else 0), q


class Period:
    pass


def sweep_w(st):
    """cdigits.SPEC.sweep, also returning the number of digits in the window of its symbolic run (the window
    grows from the carry chain and its stop digit while the run touches the rest of the tape)."""
    spec = C.SPEC
    ctx0, digits, last, end = st
    n = len(digits)
    j = C.chain(digits)
    w = min(n, j + 1)
    r = spec.sweep(st, carry=C.CARRY)
    if r[0] != 'ok':
        raise RuntimeError('sweep failed: %s' % (r[0],))
    while w < n:                # every rule on the way is in the memo now
        res = spec.memo.get(window_key_of(spec, st, w))
        if res is None or res[0] not in ('touch', 'unparsed'):
            break
        w += 1
    return r[1], r[2], w


def window_key_of(spec, st, w):
    """The memo key digits.Spec.sweep uses for a window of the last w digits."""
    ctx0, digits, last, end = st
    n = len(digits)
    vis = digits[n - w:]
    usepre = (w == n)
    rd = []
    for i, (sh, k) in enumerate(vis):
        (b, v), e = spec.absrun(k, 'v%d' % i)
        rd.append((sh, b, v))
    (lb, lv), e = spec.absrun(last, 'z')
    return (usepre, tuple((sh, b if v is None else ('big', b)) for sh, b, v in rd), (lb if lv is None else ('big', lb)),
            end)


CACHE = []          # periods learned so far (canonical frame), with an index hash of S's key -> phase
CACHE_MAX = int(os.environ.get('LCACHE', 8))


def cache_add(P):
    P.index = {x: i for i, x in enumerate(P.hs)}
    CACHE.append(P)
    del CACHE[:-CACHE_MAX]


def cache_find(st, s, hk=None):
    """a cached period that S is on now (rotated to the current phase), or None"""
    if hk is None:
        hk = hash(skey(st, s[1]))
    for P in reversed(CACHE):
        i = P.index.get(hk)
        if i is not None:
            Q = rotate(P, (i - P.off) % P.len)
            Q.h, Q.N = s
            return Q
    return None


def learn(st, T, maxsw=None, log=None):
    """Exact sweeps (the state advances) until the low system S repeats (Brent's cycle search on S).
    Returns (st, T, nsweeps, Period or None)."""
    maxsw = maxsw or LEARN_MAX
    s0 = structure(st)
    if s0 is None:              # no counter to jump: exact sweeps until there is one
        n = 0
        while n < maxsw and (n == 0 or structure(st) is None):
            st, s = sweep(st)
            T += s
            n += 1
        return st, T, n, None
    h, N = s0
    saved = skey(st, N)
    power = lam = 1
    rec = []                    # (emit, alpha, intr, i) of the sweeps since `saved`, for sweeps where one is nonzero
    base = 0
    hs = array('q', [hash(saved)])   # hash of S's key before each sweep of the period
    cb = [0]                         # base before each sweep of the period (can exceed 64 bits)
    for n in range(maxsw):
        dig = st[1]
        nd = len(dig)
        rN = dig[N][1]
        emit = dig[N][0] == 'T' and C.chain(dig) >= nd - N
        uc = None
        if emit:
            uc, stop = u_chain_cost(dig, N, h)
            if uc is None:          # the chain leaves U: far-zone event, run it and start again
                st2, s = sweep(st)
                return st2, T + s, n + 1, None
            dN_f = F[VAL[dig[N - 1][0]]]
        st2, s, w = sweep_w(st)
        if N >= nd - w - 1:         # N's run is in (or next to) the window: measure its coefficient
            alt = list(dig)
            alt[N] = (dig[N][0], rN + 1)
            st3, s3 = sweep((st[0], alt, st[2], st[3]))
            exp = list(st2[1])
            exp[N] = (exp[N][0], exp[N][1] + 1)
            if st3[0] != st2[0] or st3[1] != exp or st3[2:] != st2[2:]:
                raise RuntimeError('S depends on the run of N at step %d' % T)
            alpha = s3 - s
        else:
            alpha = 0
            if st2[1][:N + 1] != dig[:N + 1]:
                raise RuntimeError('a sweep outside its window changed the digits above S at step %d' % T)
        d_after = st2[1][N][1] - rN
        intr = d_after + (dN_f if emit else 0)
        base += s - alpha * rN - (uc if emit else 0)
        if emit or alpha or intr:
            rec.append((emit, alpha, intr, lam - 1, (st[0], dig[N][0], tuple(dig[N + 1:]), st[2], st[3])))
        cb.append(base)
        st, T = st2, T + s
        s1 = structure(st)
        if s1 is None or s1[1] != N:
            return st, T, n + 1, None
        k = skey(st, N)
        if CACHE:
            Q = cache_find(st, s1, hash(k))
            if Q is not None:
                return st, T, n + 1, Q
        if k == saved:
            P = Period()
            P.ev, P.base, P.len = rec, base, lam
            P.h, P.N = s1[0], N
            P.key = k
            P.hs, P.cb, P.off = hs, cb, 0
            cache_add(P)
            return st, T, n + 1, P
        if lam == power:            # Brent: move the saved point
            saved, power, lam, rec, base = k, power * 2, 0, [], 0
            hs, cb = array('q'), [0]
        hs.append(hash(k))
        lam += 1
    return st, T, maxsw, None


def summarize(P):
    E = sum(1 for e in P.ev if e[0])
    G = sum(e[2] for e in P.ev)
    rows = []          # (alpha, e_k, g_k) for sweeps with alpha != 0
    ek = gk = 0
    gmin = 0
    for e in P.ev:
        emit, alpha, intr = e[:3]
        if alpha:
            rows.append((alpha, ek, gk))
        if emit:
            ek += 1
        gk += intr
        gmin = min(gmin, gk)
    P.E, P.G, P.rows, P.gmin = E, G, rows, gmin
    return P


def u_add(dig, h, N, K):
    """K carries into N-1. Returns (new digits h..N-1, carry out of h, steps of the U chains)."""
    new = list(dig)
    n = K
    steps = 0
    for q in range(N - 1, h - 1, -1):
        w, r = dig[q]
        d = VAL[w]
        c = (d + n) // 3
        steps += -2 * count_phase(d, n, 1)
        if c:
            above = VAL[dig[q - 1][0]] if q - 1 >= 0 and dig[q - 1][0] in VAL else None
            if q == h:
                return None, c, None
            steps += 12 * (c * r - sum_lf(above, c)) + 16 * c
            r = r - lf(above, c)
        new[q] = (WALL[(d + n) % 3], r)
        n = c
        if n == 0:
            break
    return new, 0, steps


def jump_eval(st, P, T):
    """State and steps after T periods, or None if the jump is not allowed."""
    dig = st[1]
    h, N = P.h, P.N
    if any(dig[q][0] not in VAL for q in range(h, N)):
        return None
    K = T * P.E
    new, out, ust = u_add(dig, h, N, K)
    if new is None or out:
        return None
    for q in range(h, N):
        if new[q][1] < RMIN:
            return None
    d0 = VAL[dig[N - 1][0]]
    rN0 = dig[N][1]
    # N's run: rN0 + p*G + g_k - lf(d0, p*E + e_k)
    rN1 = rN0 + T * P.G - lf(d0, K)
    if rN0 + min(0, (T - 1) * P.G) + P.gmin - lf(d0, K) < BIG // 2:
        return None
    E = P.E
    stN = 0
    cnt = [(T + 2 - s) // 3 for s in range(3)]
    for alpha, ek, gk in P.rows:
        sL = E * T * (T - 1) // 2 + T * ek + sum(cnt[s] * eps(d0, (s * E + ek) % 3) for s in range(3))
        stN += alpha * (T * rN0 + P.G * T * (T - 1) // 2 + T * gk - sL)
    steps = T * P.base + stN + ust
    new[N] = (dig[N][0], rN1)
    return (st[0], new, st[2], st[3]), steps


def max_jump(st, P):
    if P.E == 0:
        return 0
    lo, hi = 0, 1
    while jump_eval(st, P, hi) is not None:
        lo, hi = hi, hi * 2
        if hi > 1 << 400:
            break
    while hi - lo > 1:
        m = (lo + hi) // 2
        if jump_eval(st, P, m) is not None:
            lo = m
        else:
            hi = m
    return lo


def far_view(st, k=4):
    return C.DG.show((st[0], st[1][:k], 0, ''))


def cb_rot(P, x):
    """base of the first x sweeps of P (in its rotated frame)"""
    L = P.len

    def cc(y):
        return P.cb[y] if y <= L else P.cb[L] + P.cb[y - L]
    return cc(P.off + x) - cc(P.off)


def rotate(P, j):
    """P started j sweeps later (S is autonomous, so the same cycle from another phase)."""
    L = P.len
    j %= L
    Q = Period()
    Q.len, Q.base, Q.hs, Q.cb = L, P.base, P.hs, P.cb
    Q.off = (P.off + j) % L
    ev = [(e, a, g, (i - j) % L, sn) for e, a, g, i, sn in P.ev]
    ev.sort(key=lambda r: r[3])
    Q.ev = ev
    Q.h, Q.N = P.h, P.N
    return summarize(Q)


def prefix(P, m):
    """the first sweeps of P, up to (not including) its m-th record, as a Period; and their number"""
    r = P.ev[m][3] if m < len(P.ev) else P.len
    Q = Period()
    Q.ev, Q.len, Q.base, Q.h, Q.N = P.ev[:m], r, cb_rot(P, r), P.h, P.N
    Q.snap = P.ev[m][4] if m < len(P.ev) else None
    return summarize(Q), r


def prefix_eval(st, Q):
    """jump_eval of a prefix: U and N as for a period, S as it is at the end of the prefix"""
    res = jump_eval(st, Q, 1)
    if res is None or Q.snap is None:
        return res
    ctx, wall, sdig, last, end = Q.snap
    dig = res[0][1][:Q.N + 1] + list(sdig)
    dig[Q.N] = (wall, dig[Q.N][1])
    return (ctx, dig, last, end), res[1]


def max_prefix(st, P, cap=None):
    """the longest prefix of P that can be jumped (validity is monotone in its length): (m, r, result)"""
    lo, hi = 0, len(P.ev)            # prefix(lo) allowed; m = len(ev) is a whole period, not tried here
    best = prefix_eval(st, prefix(P, 0)[0])
    while hi - lo > 1:
        mid = (lo + hi) // 2
        Q, r = prefix(P, mid)
        res = prefix_eval(st, Q) if cap is None or r <= cap else None
        if res is not None:
            lo, best = mid, res
        else:
            hi = mid
    Q, r = prefix(P, lo)
    if best is None or (cap is not None and r > cap):
        return 0, 0, None
    return lo, r, best


def advance(st, T, nsw, P=None, seconds=None, target=None, out=None, log=sys.stdout, every=120):
    """Run, jumping whole periods of S and, when the next period is blocked (a carry leaving U, mostly), the part of
    it up to the blocking sweep; that sweep and the far-zone sweeps after it run exactly, and S continues on its
    cycle from the new phase (checked by the hash of S's key at that phase), so the period is not learned again."""
    t0 = last = time.time()
    njump = 0
    nx = 1
    while (seconds is None or time.time() - t0 < seconds) and (target is None or nsw < target):
        if P is None and CACHE:
            s = structure(st)
            if s is not None:
                P = cache_find(st, s)
                if P is not None:
                    continue
        if P is None:
            st, T, n, P = learn(st, T, maxsw=None if target is None else max(1, target - nsw))
            nsw += n
            if P is None:
                if n >= 100000:
                    s = structure(st)
                    print('no period in %d sweeps at step %.6e, structure %s' % (n, float(T), s), file=log,
                          flush=True)
                continue
            summarize(P)
            print('period: %d sweeps, N=%d emits %d carries, gains %d blocks; S = %s' % (
                P.len, P.N, P.E, P.G, C.DG.show((False, st[1][P.N + 1:], st[2], st[3]))[:200]), file=log,
                flush=True)
            continue
        rem = None if target is None else target - nsw
        K = max_jump(st, P)
        if rem is not None:
            K = min(K, rem // P.len)
        if K >= 1:
            r = jump_eval(st, P, K)
            st, T, nsw = r[0], T + r[1], nsw + K * P.len
            njump += 1
            if K > 1000 or DEBUG:
                print('jump %d: %d periods of %d sweeps (E=%d, G=%d, h=%d, N=%d): step %d (%.6e)  %s ... %s' % (
                    njump, K, P.len, P.E, P.G, P.h, P.N, T, float(T), far_view(st, 6),
                    C.DG.show((False, st[1][P.N - 1:], st[2], st[3]))[:200]), file=log, flush=True)
                if out:
                    save(out, st, T, nsw)
                if os.environ.get('STATELOG'):
                    with open(os.environ['STATELOG'], 'a') as f:
                        f.write('%d %d %s\n' % (nsw, T, C.DG.show(st)))
        rem = None if target is None else target - nsw
        m, r, res = max_prefix(st, P, rem)
        if r > 0:
            st, T, nsw = res[0], T + res[1], nsw + r
        if K < 1 and r == 0:
            nx = min(2 * nx, 4096)
        else:
            nx = 1
        n = 0
        while n < nx and (target is None or nsw < target):
            st, s1 = sweep(st)
            T += s1
            nsw += 1
            n += 1
        s = structure(st)
        if s is None:
            P = None
            continue
        Q = rotate(P, r + n)
        if Q.hs[Q.off] != hash(skey(st, s[1])):
            if DEBUG:
                print('  S left its cycle at step %.6e' % float(T), file=log, flush=True)
            P = None
            continue
        Q.h, Q.N = s
        P = Q
        if time.time() - last > every and out:
            last = time.time()
            save(out, st, T, nsw)
    if out:
        save(out, st, T, nsw)
    return st, T, nsw, P


def run(st, T, nsw, seconds, out=None, log=sys.stdout, every=120):
    st, T, nsw, P = advance(st, T, nsw, None, seconds=seconds, out=out, log=log, every=every)
    return st, T, nsw


def save(path, st, T, nsw):
    pickle.dump((st, T, nsw), open(path + '.tmp', 'wb'))
    os.replace(path + '.tmp', path)


def load(path):
    st, T, nsw = pickle.load(open(path, 'rb'))
    C.register(st)
    return st, T, nsw


def test(st, T, Ts=(1, 2, 3, 5, 13)):
    for _ in range(50):
        st, T, n, P = learn(st, T)
        if P is not None:
            break
    assert P is not None, 'no period'
    summarize(P)
    print('period %d sweeps, E=%d G=%d h=%d N=%d, max jump %d' % (P.len, P.E, P.G, P.h, P.N, max_jump(st, P)))
    ok = True
    K = max_jump(st, P)
    if K < 400:
        Ts = sorted(set([t for t in Ts if t <= K] + [K]))
    for k in Ts:
        r = jump_eval(st, P, k)
        if r is None:
            print('T=%d not allowed' % k)
            continue
        x, s = st, 0
        for _ in range(k * P.len):
            x, s1 = sweep(x)
            s += s1
        good = x == r[0] and s == r[1]
        ok &= good
        print('T=%d (%d sweeps): %s  steps exact %d lean %d' % (k, k * P.len, 'OK' if good else 'MISMATCH', s, r[1]))
        if not good:
            for i, (u, v) in enumerate(zip(x[1], r[0][1])):
                if u != v:
                    print('  digit', i, 'exact', u, 'lean', v)
    return ok


def run_to(st, T, nsw, target, P=None):
    """Advance to exactly `target` sweeps.  P: a period learned earlier, valid at the current phase."""
    return advance(st, T, nsw, P, target=target, log=sys.stderr if DEBUG else open(os.devnull, 'w'))


def parse_shown(line):
    """A FULLLOG line `sweeps steps [r]W ... [last] END` back to (state, steps, sweeps)."""
    a = line.split()
    dig = []
    for tok in a[2:-2]:
        r, w = tok[1:].split(']')
        dig.append((w, int(r)))
    st = (False, dig, int(a[-2][1:-1]), a[-1])
    C.register(st)
    return st, int(a[1]), int(a[0])


def verify(st, T, nsw, logfile, every=1):
    """Compare with the lines of a FULLLOG of tacc.py: `sweeps steps digits...`, each at its sweep count."""
    P = None
    n = bad = 0
    t0 = time.time()
    for i, line in enumerate(open(logfile)):
        if i % every:
            continue
        a = line.split(' ', 2)
        tgt, steps, shown = int(a[0]), int(a[1]), a[2].strip()
        if tgt < nsw:
            continue
        st, T, nsw, P = run_to(st, T, nsw, tgt, P)
        n += 1
        good = T == steps and C.DG.show(st) == shown
        if not good:
            bad += 1
            print('MISMATCH at sweep', tgt, T, steps, C.DG.show(st)[:300], '|', shown[:300], flush=True)
        if n % 20 == 0 or os.environ.get('VERBOSE'):
            print('%d lines compared, %d mismatches, at step %.3e, %.0f s' % (n, bad, float(T), time.time() - t0),
                  flush=True)
    print('verify: %d lines of %s compared, %d mismatches, %.0f s' % (n, logfile, bad, time.time() - t0))
    return bad == 0


if __name__ == '__main__':
    a = sys.argv[2:]
    C.use('b2' if 'b2' in a else 'b1')
    a = [x for x in a if x not in ('b1', 'b2')]
    if sys.argv[1] == 'test':
        st, T, nsw = load(a[0])
        Ts = tuple(int(x) for x in os.environ.get('TESTS', '1,2,3,5,13').split(','))
        sys.exit(0 if test(st, T, Ts) else 1)
    if sys.argv[1] == 'verify':
        if a[0].endswith('.pkl'):
            st, T, nsw = load(a[0])
        elif a[0].startswith('line'):
            st, T, nsw = parse_shown(open(a[1]).readlines()[int(a[0][4:])])
        else:
            st, T = C.start_state(a[0])
            nsw = 0
        sys.exit(0 if verify(st, T, nsw, a[1], int(a[2]) if len(a) > 2 else 1) else 1)
    if sys.argv[1] == 'run':
        if a[0].endswith('.txt'):        # a state line `sweeps steps digits...` (data/b1_lean_last.txt)
            st, T, nsw = parse_shown(open(a[0]).readline())
        else:
            st, T, nsw = load(a[0])
        st, T, nsw = run(st, T, nsw, float(a[1]), a[2])
        print('END step %d (%.6e), %d sweeps: %s' % (T, float(T), nsw, C.DG.show(st)))
