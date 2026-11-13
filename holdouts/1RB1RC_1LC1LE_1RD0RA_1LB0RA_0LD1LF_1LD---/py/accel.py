"""An exact accelerated run of the counter-list rule (counters.py) of 1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---.

Between events the order of the visits depends only on the parities of the counters and on the separators: position
k is examined (reached by the leftward carry) at the times of an eventually arithmetic set, with period 2^(m-1-k) once
its separator is 0, and at each examination it stops (an even counter or a separator 1) or passes the carry on.  From
these sets every counter's decrement times are known in closed form, so the next event is found without running the
visits one by one: the carry passing the first counter (a front rebuild), a counter reaching 0, or a zero counter
being targeted (a slot, merge or prefix rebuild).  The event visit itself is done by counters.step, exactly, and the
schedules are recomputed.  Visits are counted exactly; steps are not tracked (each visit costs at least 6 times the
last counter, so 10^N visits are more than 10^N steps).

usage:
  python3 accel.py check VISITS          compare with counters.step, one visit at a time, at 31 sample visits
  python3 accel.py far DIGITS SECONDS [events]   run to 10^DIGITS visits; a summary (and every slot event)
"""

import sys, time, random
from counters import step, Unknown, LAST

class TS:
    """times: explicit sorted list F, then a, a+p, a+2p, ... (p None: no AP)"""
    __slots__ = ('F', 'a', 'p')
    def __init__(s, F, a=None, p=None):
        s.F = F; s.a = a; s.p = p
    def it(s):
        for x in s.F: yield x
        if s.p is not None:
            t = s.a
            while True:
                yield t; t += s.p
    def count_lt(s, T):
        n = 0
        for x in s.F:
            if x < T: n += 1
            else: return n
        if s.p is None or T <= s.a: return n
        return n + (T - s.a + s.p - 1) // s.p
    def kth(s, k):   # 1-indexed
        if k <= len(s.F): return s.F[k - 1]
        if s.p is None: return None
        return s.a + (k - len(s.F) - 1) * s.p
    def first(s):
        return s.kth(1)

def merge(A, B):
    """union of two disjoint TS with equal AP period (or one without AP)"""
    if A.p is None and B.p is None:
        return TS(sorted(A.F + B.F))
    if A.p is None or B.p is None:
        X, Y = (A, B) if B.p is None else (B, A)  # X has AP
        # put Y's F explicit; must be before X's AP start? just expand X until past Y.F
        F = list(X.F); a = X.a
        lim = max(Y.F) if Y.F else -1
        while a <= lim: F.append(a); a += X.p
        return TS(sorted(F + Y.F), a, X.p)
    assert A.p == B.p
    p = A.p
    # combined AP period p with 2 elements per period -> represent as AP of period p/2 if evenly spaced
    FA, aA = list(A.F), A.a; FB, bB = list(B.F), B.a
    # expand both so that starts are within one period of each other
    st = max(aA, bB)
    while aA < st: FA.append(aA); aA += p
    while bB < st: FB.append(bB); bB += p
    lo, hi = min(aA, bB), max(aA, bB)
    if p % 2 == 0 and hi - lo == p // 2:
        return TS(sorted(FA + FB), lo, p // 2)
    raise ValueError('cannot merge')

def schedules(cs, ss):
    """for the current state: exam sets, dec sets per counter, overflow time"""
    m = len(cs)
    exam = TS([], 0, 1)
    decs = [None] * m
    decR = TS([])           # decrements of c_k coming from stops at k+1
    sep_first = [None] * m  # time of first exam of k (sep s_{k-1} consumed then)
    for k in range(m - 1, 0, -1):
        sep = ss[k - 1]
        own = []
        stopL, passL = [], []
        # iterate exam times
        itE = exam.it(); 
        nexp = len(exam.F) + 6
        decs_k_R = decR
        cnt = 0; first = None
        hist = []
        p_out = None
        # values: parity at time t = (c_k - #dec before t + (3t if last)) mod 2
        for t in itE:
            if first is None: first = t
            nd = decs_k_R.count_lt(t) + sum(1 for x in own if x < t)
            val = cs[k] - nd + (3 * t if k == m - 1 else 0)
            if sep == '1':
                sep = '0'
                if val % 2 == 0: own.append(t); hist.append('O')
                else: stopL.append(t); hist.append('S')
            elif val % 2 == 0:
                stopL.append(t); hist.append('S')
            else:
                passL.append(t); hist.append('P')
            cnt += 1
            # steady when beyond explicit parts
            beyond = (exam.p is not None and t >= exam.a + 2 * exam.p and
                      (decR.p is None or t >= decR.a + 2 * decR.p) and t > (decR.F[-1] if decR.F else -1) and
                      (decR.p is None and exam.p == 1 and k == m - 1 or decR.p == exam.p))
            if exam.p is None and t is not None and cnt > len(exam.F) - 1 and cnt >= len(exam.F):
                pass
            if beyond and len(hist) >= 4 and hist[-1] != hist[-2] and hist[-2] != hist[-3] and hist[-3] != hist[-4] and 'O' not in hist[-4:]:
                p_out = 2 * exam.p
                break
            if exam.p is None and cnt >= len(exam.F):
                break
        sep_first[k] = first
        # build TS for stops/passes
        if p_out is not None:
            # last two of each list: the AP continues
            sA = stopL[-1] + p_out; pA = passL[-1] + p_out
            stopTS = TS(stopL, sA, p_out); passTS = TS(passL, pA, p_out)
        else:
            stopTS = TS(stopL); passTS = TS(passL)
        decs[k] = merge(decR, TS(own)) if own else decR
        decR = stopTS
        exam = passTS
    decs[0] = decR
    overflow = exam.first()
    return decs, overflow, sep_first

def advance(cs, ss, T, decs):
    m = len(cs)
    cs2 = [cs[k] - decs[k].count_lt(T) for k in range(m)]
    cs2[-1] += 3 * T
    return cs2

def run(cs, ss, maxv, verbose=False, check=None):
    v = 0
    log = []
    while v < maxv:
        decs, over, sf = schedules(cs, ss)
        m = len(cs)
        T = over if over is not None else 10 ** 9999
        why = 'over'
        for k in range(m - 1):
            if cs[k] >= 1:
                z = decs[k].kth(cs[k])
                if z is not None and z < T: T = z; why = 'zero%d' % k
            zt = decs[k].kth(cs[k] + 1)
            if zt is not None and zt < T: T = zt; why = 'ztarget%d' % k
        if v + T >= maxv:
            T = maxv - v
            cs = advance(cs, ss, T, decs)
            ss = [('0' if (sf[k + 1] is not None and sf[k + 1] < T) else s) for k, s in enumerate(ss)]
            v += T
            break
        cs = advance(cs, ss, T, decs)
        ss = [('0' if (sf[k + 1] is not None and sf[k + 1] < T) else s) for k, s in enumerate(ss)]
        v += T
        # execute the event visit exactly
        cs, ss, st, kind = step(cs, ss)
        v += 1
        if kind != 'ordinary':
            log.append((v, kind, dict(LAST) if kind in ('slot', 'merge') else None, len(cs)))
            if verbose: print(v, kind, LAST.get('x') if kind in ('slot','merge') else '', len(cs), cs[:6], flush=True)
        if check is not None: check(v, cs, ss)
    return cs, ss, v, log


def far(digits, secs, dump=False):
    maxv = 10 ** digits
    cs, ss = [2, 2], ['0']; v = 1
    t0 = time.time(); n_ev = 0; slots = []; nxt = 10
    try:
        while v < maxv and time.time() - t0 < secs:
            decs, over, sf = schedules(cs, ss)
            m = len(cs); T = over
            for k in range(m - 1):
                if cs[k] >= 1:
                    z = decs[k].kth(cs[k])
                    if z is not None and z < T: T = z
                zt = decs[k].kth(cs[k] + 1)
                if zt is not None and zt < T: T = zt
            cs = advance(cs, ss, T, decs)
            ss = [('0' if (sf[k + 1] is not None and sf[k + 1] < T) else s) for k, s in enumerate(ss)]
            v += T
            cs, ss, st, kind = step(cs, ss); v += 1; n_ev += 1
            if kind in ('slot', 'merge'):
                slots.append((v, kind, LAST.get('x'), LAST.get('j'), len(cs)))
                if dump: print('EVENT %d %s x=%s j=%s m=%d' % (v.bit_length(), kind, LAST.get('x'), LAST.get('j'), len(cs)), flush=True)
            while v >= nxt:
                print('visits >= 10^%d: m=%d, %d events, %d slot/merge, %.0fs' % (len(str(nxt)) - 1, len(cs), n_ev,
                      len(slots), time.time() - t0), flush=True)
                nxt *= 10
    except Unknown as u:
        print('OUTSIDE THE RULE at visit ~2^%d' % v.bit_length(), u)
    print('visits ~2^%d (~10^%d), m=%d, %d events, %.1fs' % (v.bit_length(), len(str(v)) - 1, len(cs), n_ev, time.time() - t0))
    xs = [(x, v_, j, m) for (v_, k, x, j, m) in slots if j > 1]
    print('slot/merge rebuilds: %d (%d with the counter x left of the slot not the first counter)' % (len(slots), len(xs)))
    print('smallest x (not the first counter): %d;  sum of 1/x: %.3f' % (min(x for x, *_ in xs if x), sum(1 / x for x, *_ in xs if x)))
    for x, v_, j, m in sorted(xs)[:12]:
        print('  x=%d at visit ~2^%d (slot at index %d of %d counters)' % (x, v_.bit_length(), j, m))
    print('first counters now:', cs[:8])


def check(N):
    cs, ss = [2, 2], ['0']; v = 1
    want = sorted(random.Random(2).sample(range(2, N), 30)) + [N]
    snap = {}; W = set(want)
    while v < N:
        cs, ss, st, kind = step(cs, ss); v += 1
        if v in W: snap[v] = (list(cs), list(ss))
    ok = sum(run([2, 2], ['0'], w - 1)[:2] == snap[w] for w in want)
    print('%d of %d sample visits up to %d agree with counters.step' % (ok, len(want), N))


if __name__ == '__main__':
    if sys.argv[1] == 'check':
        check(int(float(sys.argv[2])))
    else:
        far(int(sys.argv[2]), float(sys.argv[3]), len(sys.argv) > 4)
