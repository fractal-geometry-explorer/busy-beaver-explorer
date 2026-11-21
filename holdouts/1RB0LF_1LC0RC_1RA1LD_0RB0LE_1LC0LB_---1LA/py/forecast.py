"""Top-part forecast for the R04 digit models (21 November 2026, group C).

The digit models (each machine's py/digits.py, run by macro4.py / accel.py) are lists of digits (run, wall), top
first; the counter is incremented at the bottom and a carry reaches digit i only when every digit below it is the
carry wall.  The *top part* (the first P digits) therefore sees only one kind of input from below: a carry that
arrives (and, at an overflow, passes through).  Its sequence of states at its own events does not depend on what
the lower part looks like, only on the fact that carries keep arriving.  The lower part decides only *when*.

So the top part can be followed alone: keep the first P digits of an exact state and replace the rest by Q zero
digits with runs 10^60 (the *reduced model*), then run the reduced tape with the exact condition-macro engine
`cmacro.py`.  At every overflow of the reduced tape the top part is read off; while no top run is near exhaustion
one overflow cycle of the top part is a translation (every run moves by a constant D_i, the same rules in the same
order), so K cycles are done in one step: top += K*D, with K chosen so that every decreasing run stays above
64|D_i| + 64.  Near an exhaustion the cycles are run one by one (the timer events).  The reduced lower part is
trimmed to Q+3 digits at each overflow (only the top part is read).

Validity: the top part [0, P-2] of the forecast agrees with the real run (as a sequence of top states, one per
overflow cycle) until the first real run at index >= P-1 is exhausted: a merge at index j changes only digits
j-1 and j.  The real run at index P-1 loses about 4^(P-1) per cycle (less after every merge above it), so the
horizon is at least run(P-1) / 4^(P-1) cycles; `horizon` prints it.  The forecast is not a bound on steps: the
number of steps per cycle depends on the lower part and is not computed.

    python3 forecast.py MACHINE test [SECONDS]                       # (a) cmacro vs plain digits.py sweeps;
                                                                     #     (SECONDS: 60 for M1, else 300)
                                                                     # (b) reduced vs exact top sequence
    python3 forecast.py MACHINE validate PKL P Q PC SECONDS           # (b) from a saved exact state
    python3 forecast.py MACHINE horizon PKL P
    python3 forecast.py MACHINE run PKL P Q CYCLES SECONDS [OUT.pkl]  # the forecast
PKL may be 'saved' (the machine's py/state_*.json, the start state of the 21 November forecast).
MACHINE: one of CONFIGS (full TNF names); omitted, this folder's machine.  The other machines' py/forecast.py
call this file with their own name.
"""
import json
import os
import pickle
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cmacro as C  # noqa: E402

H = os.path.join(HERE, '..', '..')
M1 = '1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA'
def _p(m, f):
    return os.path.join(H, m, 'py', f)


M2 = '1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---'
M3 = '1RB---_1RC1RF_1LD1RA_1LB0LE_1LF1LF_0RB0LD'
M4 = '1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE'
M5 = '1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA0LB_---1LD'
CONFIGS = {
    # machine: (macro module, option, zero wall, test start steps, saved state, (P, PC) for the reduction check,
    #           P of the forecast run)
    M1: (_p(M1, 'macro4.py'), 'main', 'W0', 3e7, _p(M1, 'state_4.79e63.json'), (16, 7), 42),
    M2: (_p(M1, 'macro4.py'), 'twin', 'S0', 3e7, _p(M2, 'state_2.88e90.json'), (19, 8), 19),
    M3: (_p(M3, 'accel.py'), 'A', 'P', 1e7, _p(M3, 'state_1.58e90.json'), (36, 8), 36),
    M4: (_p(M4, 'accel.py'), 'A', 'W0', 1e7, _p(M4, 'state_A_5.71e90.json'), (40, 8), 40),
    # the twin: 1RB1LE_..._---1LE started in state B (lean/Twin.lean of the twin)
    M5: (_p(M4, 'accel.py'), 'B', 'W0', 1e7, _p(M5, 'state_B_3.10e89.json'), (40, 8), 40),
}
TESTSTATE = {M1: _p(M1, 'state_3.55e38.json')}     # at 4.79e63 top events are too rare for a short test
BIG = 10 ** 60


def show(top, n=12):
    return ' '.join('[%d]%s' % (k, s) for s, k in top[:n])


def diff(a, b):
    if len(a) != len(b) or any(x[0] != y[0] for x, y in zip(a, b)):
        return None
    return [y[1] - x[1] for x, y in zip(a, b)]


def reduced(st, P, Q, zero):
    par = 1 if C.SPEC.pairs else 0
    return (st[0], list(st[1][:P]) + [(zero, BIG + par + 2 * i * 10 ** 20) for i in range(Q)], BIG + par, st[3])


REF = [None]


def next_overflow(st, maxsec):
    """advance until the digit count goes up with the top wall REF (one overflow cycle)"""
    cyc = C.Cycles()
    C.LEVEL[0] = 0
    t0 = time.time()
    while True:
        st2, s2, n = C.advance(st)
        if s2 is None:
            return ('STOP', st2)
        C.Cycles.add(cyc, C.LAST[0], st, s2, n)
        grew = len(st2[1]) > len(st[1])
        st = st2
        r = cyc.try_skip(st)
        if r:
            st = r[0]
        if grew and (REF[0] is None or st[1][0][0] == REF[0]):
            return st
        if time.time() - t0 > maxsec:
            return ('TIMEOUT', st)


def forecast(st, P, Q, zero, cycles, seconds, log=print):
    cur = next_overflow(reduced(st, P, Q, zero), 900)
    if cur[0] in ('STOP', 'TIMEOUT'):
        log(cur[0], str(cur[1])[:1500])
        return [('STOP', 1)], cur, 1
    REF[0] = cur[1][0][0]
    log('first overflow; snapshot top wall %s: %s' % (REF[0], show(cur[1], 8)))
    ncyc, events, t0 = 1, [], time.time()

    def trim(s):
        d = s[1]
        if len(d) > P + Q + 3:
            d = d[:P] + d[len(d) - (Q + 3):]
        return (s[0], d, s[2], s[3])
    while ncyc < cycles and time.time() - t0 < seconds:
        a = cur
        b = next_overflow(trim(a), 900)
        c = b if b[0] in ('STOP', 'TIMEOUT') else next_overflow(trim(b), 900)
        if b[0] in ('STOP', 'TIMEOUT') or c[0] in ('STOP', 'TIMEOUT'):
            x = b if b[0] in ('STOP', 'TIMEOUT') else c
            log('%s near cycle %d: %s' % (x[0], ncyc + 1, str(x[1])[:1500]))
            events.append(('STOP', ncyc + 1, str(x[1])[:1500]))
            return events, a, ncyc
        ta, tb, tc = a[1][:P], b[1][:P], c[1][:P]
        D1, D2 = diff(ta, tb), diff(tb, tc)
        if D1 is None or D2 is None or D1 != D2:
            # not a translation: a timer event (or a missed snapshot); run on cycle by cycle
            log('EV cycle %d: %s\n   -> %s\n   -> %s' % (ncyc, show(ta), show(tb), show(tc)))
            events.append((ncyc, show(ta, 16), show(tb, 16), show(tc, 16)))
            cur, ncyc = c, ncyc + 2
            continue
        K = None
        for (sh, v), d in zip(tc, D2):
            if d < 0:
                k = (v - 64 * (-d) - 64) // (-d)
                K = k if K is None else min(K, k)
        if K is None:
            log('no top run decreases:', show(tc))
            return events, c, ncyc + 2
        K = max(0, min(K, cycles - ncyc - 2))
        top = [(sh, r + K * d) for (sh, r), d in zip(tc, D2)]
        cur = (c[0], top + list(c[1][P:]), c[2], c[3])
        ncyc += 2 + K
        if K:
            log('cycle %d (+%d jumped) %.0fs: %s D=%s' % (ncyc, K, time.time() - t0, show(top, 8), D2[:8]))
    return events, cur, ncyc


def topseq(st, PC, seconds, maxn=10 ** 9):
    """the top-PC tuples of an exact digit-model run, sampled whenever the first two digits change"""
    out = []
    t0 = time.time()
    cyc = C.Cycles()
    C.LEVEL[0] = 0
    cur = tuple(st[1][:PC])
    out.append(cur)
    while time.time() - t0 < seconds and len(out) < maxn:
        st2, s2, n = C.advance(st)
        if s2 is None:
            print('STOP', str(st2)[:300])
            break
        C.Cycles.add(cyc, C.LAST[0], st, s2, n)
        st = st2
        r = cyc.try_skip(st)
        if r:
            st = r[0]
        t = tuple(st[1][:PC])
        if t[:2] != cur[:2]:
            cur = t
            out.append(t)
    return out


def validate(st, P, Q, PC, zero, seconds):
    a = topseq(st, PC, seconds)
    b = topseq(reduced(st, P, Q, zero), PC, 3 * seconds, maxn=len(a))
    n = min(len(a), len(b))
    bad = [i for i in range(n) if a[i] != b[i]]
    print('top-%d sequence: exact run %d events, reduced model %d, compared %d, mismatches %d %s' % (
        PC, len(a), len(b), n, len(bad), bad[:3]))
    print('  last compared:', show(a[n - 1], 8))
    return n > 1 and not bad


def horizon(st, P):
    d = st[1]
    for i in range(max(1, P - 3), min(len(d), P + 3)):
        print('index %d: run %d, run/4^i = %.4g cycles' % (i, d[i][1], d[i][1] / 4 ** i))


def load_state(src):
    """a .pkl (state, steps, sweeps), a .json saved state (py/state_*.json), or a start step count (direct run)"""
    src = str(src)
    if src.endswith('.pkl'):
        st, T, _ = pickle.load(open(src, 'rb'))
    elif src.endswith('.json'):
        d = json.load(open(src))
        st = (d['ctx'], [(w, int(r)) for w, r in d['digits']], int(d['last']), d['end'])
        T = int(d['steps'])
    else:
        st, T = C.M.start_state(int(float(src)))
    if hasattr(C.M, 'register'):
        C.M.register(st)
    return st, T


def main(argv):
    if hasattr(sys, 'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    sys.setrecursionlimit(100000)
    if argv and argv[0] not in CONFIGS:
        argv = [M1] + list(argv)
    m, cmd = argv[0], argv[1]
    mod, opt, zero, start, saved, (vp, vpc), fp = CONFIGS[m]
    C.load(mod, opt)
    if cmd == 'test':
        # (a) the condition macros against plain digits.py sweeps; (b) the reduction on the saved state: the top
        # vpc digits of an exact run and of the reduced model (top vp digits kept) at every top event
        sec = float(argv[2]) if len(argv) > 2 else (60 if m == M1 else 300)
        ok = C.test(start, 2e5)
        st, T = load_state(TESTSTATE.get(m, saved))
        ok = validate(st, vp, 3, vpc, zero, sec) and ok
        print('TEST', 'OK' if ok else 'FAILED')
        return 0 if ok else 1
    if len(argv) > 2 and argv[2] == 'saved':
        argv = list(argv)
        argv[2] = saved
    st, T = load_state(argv[2])
    if cmd == 'validate':
        P, Q, PC, sec = int(argv[3]), int(argv[4]), int(argv[5]), float(argv[6])
        return 0 if validate(st, P, Q, PC, zero, sec) else 1
    if cmd == 'horizon':
        horizon(st, int(argv[3]))
        return 0
    if cmd == 'run':
        P, Q, cyc, sec = int(argv[3]), int(argv[4]), int(float(argv[5])), float(argv[6])
        print('start: step %.4e, %d digits: %s' % (T, len(st[1]), show(st[1], P)), flush=True)
        ev, cur, n = forecast(st, P, Q, zero, cyc, sec, log=lambda *a: print(*a, flush=True))
        print('END after %d overflow cycles: %s' % (n, show(cur[1], P)))
        print('events (non-translation cycles): %d; stops: %d' % (len(ev), sum(1 for e in ev if e[0] == 'STOP')))
        if len(argv) > 7:
            pickle.dump((ev, cur, n), open(argv[7], 'wb'))
        return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
