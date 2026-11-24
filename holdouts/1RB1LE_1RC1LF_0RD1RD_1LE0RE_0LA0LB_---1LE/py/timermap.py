"""Timer-map tools for 1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE (24 November 2026).

All three commands use the exact condition-macro engine of
holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/cmacro.py on this machine's digit model (py/accel.py),
through that folder's forecast.py.

  python3 py/timermap.py exact STATE.pkl|STATE.json A|B CYCLES OUT.pkl
      the full exact state (no reduction), one overflow snapshot at a time; at every canonical snapshot
      W0 W0 ([T k] W2 [0] W0)... prints the timers that did not move by the timer map (-3 for k = 1,
      -2*4^(k-1) below)
  python3 py/timermap.py runout MACHINE R CYCLES
      the saved state with the top timer set to R words, forecast through its run-out (R mod 3 picks the case)
  python3 py/timermap.py compare SECONDS PC
      the reduction check at overflow level: the canonical top-PC snapshots of an exact run (SECONDS) and of the
      reduced model (P = 40, 3*SECONDS), from the saved 5.71e90 state, compared in order
  python3 py/timermap.py cont MACHINE IN.pkl CYCLES SECONDS OUT.pkl
      continue a forecast run from its pickle (events, state, cycles), as written by forecast.py run
MACHINE: this machine (start A) or its twin 1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA0LB_---1LD (this machine from state B).
"""
import os
import pickle
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA', 'py'))
import forecast as FC  # noqa: E402
import cmacro as C  # noqa: E402

M4 = '1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE'


def dec(k):
    return 3 if k == 1 else 2 * 4 ** (k - 1)


def canon(d):
    return (d[0] == ('W0', 0) and d[1] == ('W0', 0) and all(d[i][0] == 'W2' for i in range(2, len(d), 2))
            and all(d[i] == ('W0', 0) for i in range(3, len(d), 2)))


def timers(d):
    return [d[i][1] for i in range(2, len(d), 2)]


def log(*a):
    print(*[str(x)[:600] for x in a], flush=True)


def exact(src, opt, ncyc, out):
    C.load(FC.CONFIGS[M4][0], opt)
    st, _ = FC.load_state(src)
    FC.REF[0] = 'W0'
    prev = timers(st[1]) if canon(st[1]) else None
    t0 = time.time()
    for _ in range(ncyc):
        st = FC.next_overflow(st, 36000)
        if st[0] in ('STOP', 'TIMEOUT'):
            log(st[0], st[1])
            return 1
        d = st[1]
        if not canon(d):
            log('snapshot (not canonical), %d digits' % len(d))
            continue
        T = timers(d)
        if prev is not None:
            ch = [(k + 1, prev[k] if k < len(prev) else None, T[k] if k < len(T) else None)
                  for k in range(max(len(T), len(prev)))
                  if k >= len(T) or k >= len(prev) or T[k] != prev[k] - dec(k + 1)]
            log('canonical, %d timers, %.0fs; timers off the map: %d %s' % (len(T), time.time() - t0, len(ch), ch[:6]))
        prev = T
    pickle.dump((st, 0, 0), open(out, 'wb'))
    return 0


def runout(m, r, ncyc):
    mod, opt, zero, _, saved, _, _ = FC.CONFIGS[m]
    C.load(mod, opt)
    st, _ = FC.load_state(saved)
    d = list(st[1])
    log('top timer', d[2], '->', r)
    d[2] = (d[2][0], r)
    ev, cur, n = FC.forecast((st[0], d, st[2], st[3]), 40, 3, zero, ncyc, 900, log=log)
    log('END', n, FC.show(cur[1], 12) if not isinstance(cur[0], str) else cur)
    log('stops', [e for e in ev if e[0] == 'STOP'])
    return 0


def cont(m, src, ncyc, sec, out):
    mod, opt, zero, _, _, _, _ = FC.CONFIGS[m]
    C.load(mod, opt)
    ev, cur, n = pickle.load(open(src, 'rb'))
    if hasattr(C.M, 'register'):
        C.M.register(cur)
    log('continuing from cycle', n, FC.show(cur[1], 8))
    ev2, cur2, n2 = FC.forecast(cur, 40, 3, zero, ncyc, sec, log=log)
    log('END total cycles %d: %s' % (n + n2, FC.show(cur2[1], 40)))
    log('stops', sum(1 for e in ev2 if e[0] == 'STOP'))
    pickle.dump((ev2, cur2, n + n2), open(out, 'wb'))
    return 0


def compare(sec, pc):
    mod, opt, zero, _, saved, _, _ = FC.CONFIGS[M4]
    C.load(mod, opt)
    st, _ = FC.load_state(saved)
    a = FC.topseq(st, pc, sec)
    b = FC.topseq(FC.reduced(st, 40, 3, zero), pc, 3 * sec)

    def red(s):
        o = []
        for t in s:
            if canon(t) and (not o or o[-1] != t):
                o.append(t)
        return o
    A, B = red(a), red(b)
    n = min(len(A), len(B))
    bad = [i for i in range(n) if A[i] != B[i]]
    log('canonical top-%d snapshots: exact %d, reduced %d, compared %d, mismatches %d %s' % (
        pc, len(A), len(B), n, len(bad), bad[:5]))
    if n:
        log('last compared:', FC.show(A[n - 1], pc))
    return 0 if n and not bad else 1


if __name__ == '__main__':
    sys.set_int_max_str_digits(0)
    sys.setrecursionlimit(100000)
    a = sys.argv[1:]
    if a[0] == 'exact':
        sys.exit(exact(a[1], a[2], int(a[3]), a[4]))
    if a[0] == 'runout':
        sys.exit(runout(a[1], int(a[2]), int(a[3])))
    if a[0] == 'compare':
        sys.exit(compare(float(a[1]), int(a[2])))
    if a[0] == 'cont':
        sys.exit(cont(a[1], a[2], int(float(a[3])), float(a[4]), a[5]))
    print(__doc__)
