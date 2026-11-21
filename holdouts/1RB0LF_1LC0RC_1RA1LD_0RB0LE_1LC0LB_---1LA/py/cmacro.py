"""Condition macros for the digit models of the R04 counters (21 November 2026, group C).

A layer over a machine's `macro4.py` / `accel.py` (same digit model, same base sweep `sweep_sym`, which is
digits.py's Spec.sweep on affine runs).  The difference to macro4 is the macro key:

  * macro4 keys every run of the window by a threshold 8 + 4^(k-i+1): a run below it enters the key as its exact
    value, so near-critical runs (the timers) make a new key at every visit;
  * here a run is exact only below CUT = 8 (the cut-off of the digits.py window rules themselves) and otherwise
    'big' with its parity: run = CUT + par + 2u (u >= 0; without pairs run = CUT + u).  While a macro is derived,
    every comparison that the sweeps make on a symbolic run (is it >= CUT, is it nonzero) is *assumed* in the
    generic direction and recorded as a linear condition on the key's variables, and the conditions of inner
    macros are carried over by substitution.  A macro is applied only when all its conditions hold for the actual
    numbers; otherwise the driver falls back to a lower level (and finally to a plain digits.py sweep).

So an applied macro is exactly the composition of digits.py sweeps it was derived from (every sweep there was run
with each of its runs on the same side of every comparison), steps included.  Keys no longer depend on the run
sizes, so the macro for a carry cascade of k digits is derived once and reused at every period.

Cycle skips: when the last p applications (p <= PMAX) repeat with equal keys and every macro in them is a pure
translation of the runs, the round moves the state by a constant D.  All conditions are linear in the state, so the
largest K for which every condition of every macro of the round holds at round 0 and at round K-1 holds for all
rounds in between; the K rounds are applied at once (steps: sum of an affine function of j).

    python3 cmacro.py MODULE test START|CKPT.pkl SWEEPS [opt]      # against plain digits.py sweeps
    python3 cmacro.py MODULE run CKPT_IN.pkl SECONDS CKPT_OUT.pkl [opt]
MODULE: path of the machine's macro4.py / accel.py; opt: 'twin' (macro4) or 'B' (accel of 99198).
"""
import importlib.util
import os
import pickle
import sys
import time

M = None          # the macro4-like module
SPEC = None
Aff = None
Fail = None
CUT = 8

CTX = []          # stack of condition sets (dict linear-part -> Aff), the innermost derivation last


class Unsure(Exception):
    pass


def load(path, opt):
    global M, SPEC, Aff, Fail, CUT
    spec = importlib.util.spec_from_file_location('mac_' + str(abs(hash(path))), path)
    M = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(M)
    M.use(opt)
    SPEC = M.SPEC
    Aff = M.Aff
    Fail = M.Fail
    CUT = SPEC.big + 2
    patch()


def assume(e):
    """record e >= 0 (e: Aff or int) in the innermost derivation; Fail if it is decidably false"""
    if not isinstance(e, Aff):
        if e < 0:
            raise Fail('false')
        return
    if e.const():
        if e.k < 0:
            raise Fail('false')
        return
    lo = e.lo()
    if lo is not None and lo >= 0:
        return
    if not CTX:
        raise Fail('assume outside derivation')
    if all(a <= 0 for a in e.c.values()) and e.k < 0:
        raise Fail('false')
    d = CTX[-1]
    k = tuple(sorted(e.c.items()))
    o = d.get(k)
    if o is None or e.k < o.k:
        d[k] = e


def patch():
    """Replace the run classes of the module by condition classes."""
    def cls(run, thr=None):
        if isinstance(run, Aff) and run.const():
            run = run.k
        if not isinstance(run, Aff):
            return ('c', run) if run < CUT else ('big', run % 2 if SPEC.pairs else 0)
        assume(run - CUT)
        return ('big', run.parity() if SPEC.pairs else 0)
    M.cls = cls

    def boolf(self):
        if self.const():
            return self.k != 0
        lo = self.lo()
        if lo is not None and lo > 0:
            return True
        assume(self - 1)
        return True
    Aff.__bool__ = boolf


def var_run(par, name):
    return Aff(CUT + par, {name: 2 if SPEC.pairs else 1})


def var_val(r, par):
    if SPEC.pairs:
        return Aff.of(r).half(CUT + par) if isinstance(r, Aff) else (r - CUT - par) // 2
    return r - CUT - par


def window_key(state, k, full_outer=True):
    ctx, digits, last, end = state
    n = len(digits)
    if k > n - 1:
        raise Fail('k')
    sidx = k
    while sidx < n and digits[n - 1 - sidx][0] in M.CARRY:
        sidx += 1
    if sidx >= n:
        raise Fail('no stop')
    start = max(n - 1 - sidx - 1, 0)
    full = start == 0 and full_outer
    win = digits[start:]
    kk = (k, full, ctx, end, tuple((sh, M.cls(r)) for sh, r in win), M.cls(last))
    return kk, start


MEMO = {}
STATS = {'derived': 0, 'failed': 0, 'applied': 0, 'condfail': 0}
REPMAX = 8


def derive(key):
    k, full, ctx, end, win, lastc = key
    digs = []
    for i, (sh, c) in enumerate(win):
        digs.append((sh, c[1] if c[0] == 'c' else var_run(c[1], 'u%d' % i)))
    last = lastc[1] if lastc[0] == 'c' else var_run(lastc[1], 'z')
    state = (ctx, digs, last, end)
    CTX.append({})
    try:
        if k == 0:
            st, steps = M.sweep_sym(state, full)
            reach = max(M.reach_of(digs, st[1]), M.chain(digs))
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
        conds = list(CTX[-1].values())
    except (Fail, AssertionError):
        return None
    finally:
        CTX.pop()
    # translation: same number of digits, every out run = its in run + constant (needed for cycle skips)
    trans = len(st[1]) == len(digs) and all(
        (Aff.of(b[1]) - Aff.of(a[1])).const() for a, b in zip(digs, st[1])) and \
        (Aff.of(st[2]) - Aff.of(last)).const() and st[0] == ctx and st[3] == end
    return st, Aff.of(steps), nsw, reach, conds, trans


MEMO_MAX = int(os.environ.get('MEMO_MAX', 200000))


def get_macro(key):
    m = MEMO.get(key, 0)
    if m == 0:
        if len(MEMO) > MEMO_MAX:
            MEMO.clear()
            STATS['cleared'] = STATS.get('cleared', 0) + 1
        m = derive(key)
        MEMO[key] = m
        STATS['derived' if m else 'failed'] += 1
    return m


def env_of(key, state, start):
    k, full, ctx, end, win, lastc = key
    env = {}
    digits = state[1][start:]
    for i, ((sh, c), (_, r)) in enumerate(zip(win, digits)):
        if c[0] == 'big':
            env['u%d' % i] = var_val(r, c[1])
    if lastc[0] == 'big':
        env['z'] = var_val(state[2], lastc[1])
    return env


subst = None


def apply_macro(m, key, state, start, symbolic):
    (octx, odig, olast, oend), steps, nsw, reach, conds, trans = m
    env = env_of(key, state, start)
    for c in conds:
        v = M.subst(c, env)
        if symbolic:
            assume(v)
        elif v < 0:
            return None
    ctx, digits, last, end = state
    nd = SPEC.canon_digits(digits[:start] + [(sh, M.subst(r, env)) for sh, r in odig])
    return (octx, nd, M.subst(olast, env), oend), M.subst(steps, env), nsw, reach


def apply_sym(state, k, full):
    key, start = window_key(state, k, full)
    m = get_macro(key)
    if m is None:
        raise Fail('no inner macro')
    return apply_macro(m, key, state, start, True)


def apply_conc(state, k):
    try:
        key, start = window_key(state, k)
    except Fail:
        return None
    m = get_macro(key)
    if m is None:
        return None
    try:
        r = apply_macro(m, key, state, start, False)
    except (Fail, AssertionError):
        return None
    if r is None:
        STATS['condfail'] += 1
        return None
    STATS['applied'] += 1
    return r + (key, start, m)


KMAX = int(os.environ.get('KMAX', 100000))
LEVEL = [0]
LAST = [None]


def advance(state):
    t = min(LEVEL[0], KMAX, len(state[1]) - 1)
    for k in range(t, 0, -1):
        r = apply_conc(state, k)
        if r is not None:
            LEVEL[0] = r[3]
            LAST[0] = (r[4], r[5], r[6])
            return r[0], r[1], r[2]
    LAST[0] = None
    j = M.chain(state[1])
    r = SPEC.sweep(state, carry=M.CARRY)
    if r[0] != 'ok':
        return ('STOP', r), None, None
    LEVEL[0] = max(j, M.reach_of(state[1], r[1][1]))
    return r[1], r[2], 1


# ------------------------------------------------------------------ cycle skips
class Cycles:
    PMAX = 8

    def __init__(self):
        self.h = []          # (key, start, macro, before, steps, nsw, level_after)
        self.skips = 0
        self.rounds = 0

    def add(self, last, before, steps, nsw):
        if last is None:
            self.h = []
            return
        self.h.append((last[0], last[1], last[2], before, steps, nsw, LEVEL[0]))
        if len(self.h) > 2 * self.PMAX:
            del self.h[0]

    def try_skip(self, cur, capk=None):
        h = self.h
        for p in range(1, self.PMAX + 1):
            if len(h) < 2 * p:
                break
            A, Bv = h[-2 * p:-p], h[-p:]
            if any(a[0] != b[0] or a[1] != b[1] or a[6] != b[6] for a, b in zip(A, Bv)):
                continue
            if not all(b[2][5] for b in Bv):
                continue
            s0, s1 = A[0][3], Bv[0][3]
            if len(s0[1]) != len(s1[1]) or len(cur[1]) != len(s1[1]):
                continue
            D = [r1 - r0 for (_, r0), (_, r1) in zip(s0[1], s1[1])] + [s1[2] - s0[2]]
            D2 = [r1 - r0 for (_, r0), (_, r1) in zip(s1[1], cur[1])] + [cur[2] - s1[2]]
            if D != D2 or not any(D):
                continue
            # K further rounds from cur: before macro i at round j is Bv[i].before + (j+1) D
            K = None
            for (key, start, m, before, _, _, _) in Bv:
                lin = []
                e0 = self._env(key, before, start, D, 1)
                e1 = self._env(key, before, start, D, 2)
                if e0 is None or e1 is None:
                    K = 0
                    break
                for c in m[4]:
                    lin.append((M.subst(c, e0), M.subst(c, e1)))
                for v in e0:                      # the key's big runs: u >= 0
                    lin.append((e0[v], e1[v]))
                for a, b in lin:
                    if a < 0:
                        K = 0
                        break
                    d = b - a
                    if d < 0:
                        kk = a // (-d) + 1
                        K = kk if K is None else min(K, kk)
                if K == 0:
                    break
            if K is None or K < 2:
                continue
            if capk:
                K = min(K, capk)
            # explicit check at the last round (j = K-1)
            ok = True
            for (key, start, m, before, _, _, _) in Bv:
                bk = self.moved(before, D, K)
                try:
                    kk, st2 = window_key(bk, key[0])
                except Fail:
                    ok = False
                    break
                if kk != key or st2 != start:
                    ok = False
                    break
                env = env_of(key, bk, start)
                if any(M.subst(c, env) < 0 for c in m[4]):
                    ok = False
                    break
            if not ok:
                continue
            sig_b = sum(x[4] for x in Bv)
            sig_a = sum(x[4] for x in A)
            ds = sig_b - sig_a
            steps = K * sig_b + ds * K * (K + 1) // 2
            nsw = K * sum(x[5] for x in Bv)
            self.skips += 1
            self.rounds += K
            self.h = []
            return self.moved(cur, D, K), steps, nsw
        return None

    def _env(self, key, before, start, D, j):
        try:
            return env_of(key, self.moved(before, D, j), start)
        except (Fail, AssertionError):
            return None

    def moved(self, st, D, K):
        digs = [(sh, r + K * d) for (sh, r), d in zip(st[1], D)]
        return (st[0], digs, st[2] + K * D[-1], st[3])


# ------------------------------------------------------------------ drivers
def load_state(src):
    if isinstance(src, str) and src.endswith('.pkl'):
        st, T, done = pickle.load(open(src, 'rb'))
    else:
        st, T = M.start_state(int(float(src)))
        done = 0
    if hasattr(M, 'register'):
        M.register(st)
    return st, T, done


def test(src, sweeps, capk=None):
    st, T, _ = load_state(src)
    ref, RT = st, T
    done = nref = checks = 0
    t0 = time.time()
    cyc = Cycles()
    while done < sweeps:
        st2, s2, n = advance(st)
        if s2 is None:
            print('STOP', st2)
            return False
        cyc.add(LAST[0], st, s2, n)
        st, T, done = st2, T + s2, done + n
        r = cyc.try_skip(st, capk=capk)
        if r:
            st, T, done = r[0], T + r[1], done + r[2]
        while nref < done:
            r = SPEC.sweep(ref, carry=M.CARRY)
            assert r[0] == 'ok', r
            ref, RT, nref = r[1], RT + r[2], nref + 1
        if (ref[0], ref[1], ref[2], ref[3]) != (st[0], st[1], st[2], st[3]) or RT != T:
            print('MISMATCH after', done, 'sweeps', M.DG.show(st)[:300], '|', M.DG.show(ref)[:300], T, RT)
            return False
        checks += 1
    print('OK: %d landing points (%d sweeps) agree with plain digits.py sweeps, states and steps; %s; %d cycle '
          'skips (%d rounds); %.0f s' % (checks, done, STATS, cyc.skips, cyc.rounds, time.time() - t0))
    return True


def sci(T):
    s = str(T)
    return '%s.%se%d' % (s[0], s[1:4], len(s) - 1)


def run(src, seconds, out, every=300):
    st, T, done = load_state(src)
    print('start', sci(T), M.DG.show(st)[:300], flush=True)
    t0 = last = time.time()
    cyc = Cycles()
    nd = len(st[1])
    while time.time() - t0 < seconds:
        st2, s2, n = advance(st)
        if s2 is None:
            print('STOP after', done, 'sweeps at step', T, st2, flush=True)
            break
        old = st
        cyc.add(LAST[0], st, s2, n)
        st, T, done = st2, T + s2, done + n
        r = cyc.try_skip(st)
        if r:
            st, T, done = r[0], T + r[1], done + r[2]
        if len(st[1]) != nd or st[1][:2] != old[1][:2]:
            nd = len(st[1])
            print('%.0fs step %s nd %d: %s' % (time.time() - t0, sci(T), nd, M.DG.show(st)[:240]), flush=True)
        if time.time() - last > every:
            last = time.time()
            print('AT %.0fs step %s sweeps %s nd %d %s skips %d' % (time.time() - t0, sci(T), sci(done), len(st[1]),
                                                                  STATS, cyc.skips), flush=True)
            pickle.dump((st, T, done), open(out + '.tmp', 'wb'))
            os.replace(out + '.tmp', out)
    print('END step %d (%s) sweeps %d %s' % (T, sci(T), done, M.DG.show(st)[:2000]), flush=True)
    print('STATS', STATS, 'skips', cyc.skips, flush=True)
    pickle.dump((st, T, done), open(out + '.tmp', 'wb'))
    os.replace(out + '.tmp', out)


if __name__ == '__main__':
    if hasattr(sys, 'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    sys.setrecursionlimit(100000)
    a = sys.argv[1:]
    load(a[0], a[-1] if a[-1] in ('twin', 'B', 'A', 'main') else ('main' if 'macro4' in a[0] else 'A'))
    a = [x for x in a if x not in ('twin', 'B', 'A', 'main')]
    if a[1] == 'test':
        sys.exit(0 if test(a[2], int(float(a[3])), int(a[4]) if len(a) > 4 else None) else 1)
    run(a[2], float(a[3]), a[4])
