"""Counter macros indexed from the FAR end, for the digit model py/cdigits.py of 1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---
(b1) and of its twin 1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC--- (b2) (16 November 2026).

py/caccel.py (the algorithm of holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/macro4.py) numbers the places of
the counter from the head's end.  Here the head's end is not stable: next to the generator the number of small
digits changes from one sweep to the next, so "place k from the bottom" means different digits at different times
and the macros are hardly reused.  This file numbers the places from the far end (index 0 = the digit farthest
from the head), which only changes at a birth.  Everything else is the same algorithm:

  * Inc(L), for a place L (from the far end): repeat Inc(L+1) until a carry reaches place L or a place farther
    out; Inc(L) for the place of the last digit or beyond is one sweep of cdigits.py (a symbolic run of the machine);
  * a macro is derived once per key: the window from one digit beyond the stop of the carry that ends it, down to
    the head; for every run its class (its exact value below a threshold, else 'big', a variable >= threshold);
    the threshold of a run that lies d places nearer the head than L is 8 + 4^(d+1) (it moves while the digits near
    the head cycle), 16 otherwise.  A macro is derived by running its inner macros on the symbolic window; every
    class must be decided for all values of the variables, or there is no macro for that key;
  * applying a macro to a state of its key is exactly the sweeps it stands for, steps included (`test` checks this
    against plain sweeps);
  * Cycles: when the same macros repeat with the runs moving by the same amounts, K rounds at once (caccel.Cycles).

    python3 py/tacc.py test START_STEPS|CKPT.pkl SWEEPS [b2]
    python3 py/tacc.py run START_STEPS SECONDS [CKPT.pkl] [b2]
"""
import os
import pickle
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'py'))
import caccel as C  # noqa: E402

Fail, Aff, cls, BLAST = C.Fail, C.Aff, C.cls, C.BLAST
BASE = int(os.environ.get('TBASE', 4))
REPMAX = int(os.environ.get('REPMAX', 16))
MEMO = {}
STATS = {'derived': 0, 'failed': 0, 'applied': 0}


def thr_t(lev, nwin):
    return [8 + BASE ** (i - lev + 1) if i > lev else 16 for i in range(nwin)]


def stop_of(digits, L):
    t = L
    while t >= 0 and digits[t][0] in C.CARRY:
        t -= 1
    return t


def window_key(state, L, full_outer=True):
    ctx, digits, last, end = state
    n = len(digits)
    if L > n - 1 or L < 0:
        raise Fail('L')
    t = stop_of(digits, L)
    if t < 0:
        raise Fail('no stop')
    start = max(t - 1, 0)
    full = start == 0 and full_outer
    win = digits[start:]
    lev = L - start
    th = thr_t(lev, len(win))
    kk = (lev, full, ctx, end, tuple((sh, cls(r, t_)) for (sh, r), t_ in zip(win, th)), cls(last, BLAST))
    return kk, start


def reach_top(before, after):
    p = 0
    while p < len(before) and p < len(after) and C.same(before[p], after[p]):
        p += 1
    return p


def one_sweep_sym(state, full):
    st, steps = C.sweep_sym(state, full)
    j = C.chain(state[1])
    reach = min(reach_top(state[1], st[1]), len(state[1]) - 1 - j)
    return st, Aff.of(steps), 1, reach


def derive(key):
    lev, full, ctx, end, win, lastc = key
    th = thr_t(lev, len(win))
    digs = []
    for i, (sh, c) in enumerate(win):
        digs.append((sh, c[1] if c[0] == 'c' else C.var_run(th[i], c[1], 'u%d' % i)))
    last = lastc[1] if lastc[0] == 'c' else C.var_run(BLAST, lastc[1], 'z')
    st = (ctx, digs, last, end)
    steps, nsw = Aff(0), 0
    try:
        for _ in range(REPMAX):
            st, s1, n1, reach = inc_sym(st, lev + 1, full)
            steps = steps + s1
            nsw += n1
            if reach <= lev:
                break
        else:
            return None
    except (Fail, AssertionError):
        return None
    return st, steps, nsw, reach


def get_macro(key):
    if key not in MEMO:
        if len(MEMO) > C.MEMO_MAX:              # memory: forget the older half (derived again when needed)
            for k in list(MEMO)[:len(MEMO) // 2]:
                del MEMO[k]
        if len(C.SPEC.memo) > C.SPEC_MEMO_MAX:
            for k in list(C.SPEC.memo)[:len(C.SPEC.memo) // 2]:
                del C.SPEC.memo[k]
        m = derive(key)
        MEMO[key] = m
        STATS['derived' if m else 'failed'] += 1
    return MEMO[key]


def env_of(key, state, start):
    lev, full, ctx, end, win, lastc = key
    th = thr_t(lev, len(win))
    env = {}
    for i, ((sh, c), (_, r)) in enumerate(zip(win, state[1][start:])):
        if c[0] == 'big':
            env['u%d' % i] = C.var_val(r, th[i], c[1])
    if lastc[0] == 'big':
        env['z'] = C.var_val(state[2], BLAST, lastc[1])
    return env


def apply_macro(m, key, state, start):
    (octx, odig, olast, oend), steps, nsw, reach = m
    env = env_of(key, state, start)
    ctx, digits, last, end = state
    nd = C.SPEC.canon_digits(digits[:start] + [(sh, C.subst(r, env)) for sh, r in odig])
    return (octx, nd, C.subst(olast, env), oend), C.subst(steps, env), nsw, reach + start


def inc_sym(state, L, full):
    """Inc(L) on a symbolic state (window coordinates): one sweep when L is beyond the last digit."""
    if L > len(state[1]) - 1:
        return one_sweep_sym(state, full)
    key, start = window_key(state, L, full)
    m = get_macro(key)
    if m is None:
        raise Fail('no inner macro')
    return apply_macro(m, key, state, start)


LEVEL = [0]
LASTKEY = [None]


def advance(state):
    n = len(state[1])
    for L in range(max(LEVEL[0], 0), n):
        try:
            key, start = window_key(state, L)
        except Fail:
            continue
        m = get_macro(key)
        if m is None:
            continue
        try:
            r = apply_macro(m, key, state, start)
        except (Fail, AssertionError):
            continue
        STATS['applied'] += 1
        LEVEL[0] = r[3]
        LASTKEY[0] = (key, L)
        return r[0], r[1], r[2]
    LASTKEY[0] = None
    j = C.chain(state[1])
    r = C.SPEC.sweep(state, carry=C.CARRY)
    if r[0] != 'ok':
        return ('STOP', r), None, None
    LEVEL[0] = min(reach_top(state[1], r[1][1]), n - 1 - j)
    return r[1], r[2], 1


class Cycles(C.Cycles):
    """caccel.Cycles with keys (key, L) of this file."""

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
            if any(self.shape(x[1]) != self.shape(y[1]) or
                   [v - u for u, v in zip(self.runs(x[1]), self.runs(y[1]))] != D for x, y in zip(A, Bv)):
                continue
            K = 1 << 62
            covered = set()
            for (keylev, before, _, _) in Bv:
                key, L = keylev
                lev, full, ctx, end, win, lastc = key
                _, start = window_key(before, L)
                rs = self.runs(before)
                ws = list(range(start, len(before[1]))) + [len(before[1])]
                covered.update(ws)
                classes = [c for _, c in win] + [lastc]
                ths = thr_t(lev, len(win)) + [BLAST]
                for idx, c, thr in zip(ws, classes, ths):
                    d = D[idx]
                    if c[0] == 'c':
                        if d != 0:
                            K = 0
                        continue
                    if d < 0:
                        K = min(K, (rs[idx] - thr - c[1]) // (-d))
            if any(d for i, d in enumerate(D) if i not in covered):
                continue
            if K < 2:
                continue
            if capk:
                K = min(K, capk)
            ok = True
            for (keylev, before, _, _) in Bv:
                key, L = keylev
                bk = self.moved(before, D, K)
                kk, start = window_key(bk, L)
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


def load(start):
    if str(start).endswith('.pkl'):
        st, T, done = pickle.load(open(start, 'rb'))
        C.register(st)
        return st, T, done
    st, T = C.start_state(start)
    return st, T, 0


def test(start, sweeps, capk=None):
    st, T, _ = load(start)
    ref, RT = st, T
    done = nref = checks = 0
    t0 = time.time()
    cyc = Cycles()
    while done < sweeps:
        st2, s2, n = advance(st)
        if s2 is None:
            print('STOP', st2)
            return False
        cyc.add(LASTKEY[0], st, s2, n)
        st, T, done = st2, T + s2, done + n
        r = cyc.try_skip(st, capk=capk)
        if r:
            st, T, done = r[0], T + r[1], done + r[2]
        while nref < done:
            r = C.SPEC.sweep(ref, carry=C.CARRY)
            assert r[0] == 'ok', r
            ref, RT, nref = r[1], RT + r[2], nref + 1
        if tuple(ref) != tuple(st) or RT != T:
            print('MISMATCH after', done, 'sweeps', C.DG.show(st)[:300], '|', C.DG.show(ref)[:300], T, RT)
            return False
        checks += 1
    print('OK: %d landing points (%d sweeps) agree with plain sweeps, states and steps; macros %s; %d cycle skips '
          '(%d rounds); %.0f s' % (checks, done, STATS, cyc.skips, cyc.rounds, time.time() - t0))
    return True


def run(start, seconds, ckpt=None, every=600):
    if ckpt and os.path.exists(ckpt):
        st, T, done = load(ckpt)
    else:
        st, T, done = load(start)
    print('start', T, C.DG.show(st)[:400], flush=True)
    t0 = last = time.time()
    nd = len(st[1])
    cyc = Cycles()
    full = open(os.environ['FULLLOG'], 'a') if os.environ.get('FULLLOG') else None
    while time.time() - t0 < seconds:
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
            print('%d sweeps, step %d (%.3e): %s' % (done, T, float(T), C.DG.show(st)[:400]), flush=True)
            if full:
                full.write('%d %d %s\n' % (done, T, C.DG.show(st)))
                full.flush()
        if time.time() - last > every:
            last = time.time()
            print('AT %d sweeps, step %d (%.3e) %s macros %s cycle skips %d' % (done, T, float(T), C.DG.show(st)[:400],
                                                                             STATS, cyc.skips), flush=True)
            if ckpt:
                pickle.dump((st, T, done), open(ckpt + '.tmp', 'wb'))
                os.replace(ckpt + '.tmp', ckpt)
    print('END %d sweeps, step %d (%.3e) %s macros %s' % (done, T, float(T), C.DG.show(st)[:600], STATS), flush=True)
    if ckpt:
        pickle.dump((st, T, done), open(ckpt + '.tmp', 'wb'))
        os.replace(ckpt + '.tmp', ckpt)
    return st, T, done


if __name__ == '__main__':
    sys.setrecursionlimit(20000)
    a = sys.argv[2:]
    C.use('b2' if 'b2' in a else 'b1')
    a = [x for x in a if x not in ('b1', 'b2')]
    if sys.argv[1] == 'test':
        sys.exit(0 if test(a[0], int(float(a[1])), int(a[2]) if len(a) > 2 else None) else 1)
    run(a[0], float(a[1]), a[2] if len(a) > 2 else None, float(os.environ.get('EVERY', 600)))
