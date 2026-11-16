#!/usr/bin/env python3
"""Follow the event list of b1 = 1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA--- (or of its twin b2 =
1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---) through many collapses.

Between collapses the list follows the general law of py/lawev.py (birth, drain, drain), which is applied in closed
form with Python integers.  When the law would make a count negative (a collapse), the stretch is not assumed: it is
simulated exactly by c/msimev.c on reduced configurations (the m segments next to the right end, the end counter and
a generator 2*3^(m+4)-28 that belongs with m segments, as in py/bcollapse.py), for three values of m, from the last
P event before the collapse until the reduced runs are back on the law for at least 7 events.  The three outcomes T_m
are spliced into the full list:
  * the common suffix of the T_m (everything that comes from kept segments) is taken as it is;
  * the entries in front of it that change with m (the generator and the segments born during the collapse) are
    fitted as A*3^m + B on two values of m, checked on the third, and evaluated at the real number of segments;
  * the segments that were not kept are drained by E events at their new places, E read off the extra kept segments
    of the larger runs (and checked on both).
What this rests on (trusted, not proved): the law between collapses; that the right end of the tape does not depend on
what lies further left (right-anchoring, checked here at every collapse by the agreement of the three reduced runs
on the common suffix); and the fitted form of the newborn segments (checked on the third run).  Step counts of the
full run are not computed exactly: the generation index is exact, the step estimate is 9-fold growth per generation
fitted on the exact regime-1 values (heuristic).

usage: python3 track.py [b1|b2] [max_generations] [log file]
"""
import json, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from lawev import MACH, birth, drain, NEXT, run_events, config, rle_config

TMP = os.environ.get('TRACK_TMP', '/tmp')


def law_step(L, kind):
    nk, f = NEXT[kind]
    return f(L), nk


def law_regime1(c0, n):
    """P_n of bmap.py"""
    g = 2 * 3 ** (n + 5) - 28
    ys = [3 ** (j + 2) * (17 - n + j) - 27 for j in range(n, -1, -1)]
    return [g] + ys + [c0 - 2 * n]


def runs_of_P(L):
    """the P configuration of list L as (run of 1s, multiplicity) pairs"""
    g, ys, c = L[0], L[1:-1], L[-1]
    runs = [(2, 1), (3, 16), (5, 1), (3, 1), (5, 1), (3, g)]
    for y in ys:
        runs += [(5, 1), (3, y)]
    runs += [(5, 1), (3, c), (1, 1)]
    return [r for r in runs if r[1] > 0]


def reduced_run(mach, L, m, maxsteps, seconds, log):
    """reduced P configuration with the m rightmost segments of L; returns the event list (with the start as event 0)
    up to the resumption of the law, and whether it halted"""
    xs = L[1:-1][-m:]
    S = [2 * 3 ** (m + 4) - 28] + xs + [L[-1]]
    cfg = rle_config(runs_of_P(S), os.path.join(TMP, 'track_%d_%d.rle' % (os.getpid(), m)))
    evs = [(0, 'D', 'P', S)]
    fail = None
    ok_since = None
    end = None
    for e in run_events(mach, cfg, maxsteps, seconds):
        if e[0] == 'END':
            end = e[1]
            break
        steps, st, kind, X = e
        prev = evs[-1]
        good = False
        if kind is not None and prev[2] is not None:
            nx, nk = law_step(prev[3], prev[2])
            good = (nk == kind and nx == X)
        evs.append(e)
        if not good:
            if fail is None:
                fail = len(evs) - 1
            ok_since = None
        elif fail is not None:
            if ok_since is None:
                ok_since = len(evs) - 2       # the first event of the resumed run
            if len(evs) - 1 - ok_since >= 7:
                break
    halted = end is not None and end.startswith('HALT')
    return evs, fail, ok_since, halted, end


def fit_left(vals, ms):
    """v = A*3^m + B on the first two, checked on the third: returns (A, B) as fractions or None"""
    from fractions import Fraction
    (v0, v1, v2), (m0, m1, m2) = vals, ms
    A = Fraction(v1 - v0, 3 ** m1 - 3 ** m0)
    B = v0 - A * 3 ** m0
    if A * 3 ** m2 + B != v2:
        return None
    return A, B


def collapse(mach, Lc, s_real, log, m0, maxsteps='1e30', seconds=3000):
    """Lc: the real list at the last P before the collapse.  Returns (T_real, kind, info) or raises."""
    ms = [m0, m0 + 1, m0 + 2]
    outs = []
    for m in ms:
        t0 = time.time()
        evs, fail, res, halted, end = reduced_run(mach, Lc, m, maxsteps, seconds, log)
        log('  reduced m=%d: %d events, law fails at event %s, resumes at event %s, %.0fs%s' % (
            m, len(evs), fail, res, time.time() - t0, ' HALT ' + end if halted else ''))
        if halted:
            return None, None, {'halt': end, 'm': m, 'events': [(e[0], e[2], e[3]) for e in evs]}
        if fail is None or res is None:
            raise RuntimeError('reduced run m=%d did not resume (%s)' % (m, end))
        outs.append((evs, fail, res))
    # visible law events before the failure must be the same number in all runs
    kv = [o[1] - 1 for o in outs]
    if len(set(kv)) != 1:
        raise RuntimeError('different numbers of law events before the collapse: %s' % kv)
    kv = kv[0]
    T = [o[0][o[2]] for o in outs]
    kinds = set(t[2] for t in T)
    if len(kinds) != 1:
        raise RuntimeError('different kinds at resumption')
    kind = T[0][2]
    Ts = [t[3] for t in T]
    # common suffix
    k = 0
    while k < min(map(len, Ts)) and len(set(t[-1 - k] for t in Ts)) == 1:
        k += 1
    sigma = Ts[0][len(Ts[0]) - k:]
    ell = len(Ts[0]) - k
    for i, m in enumerate(ms):
        if len(Ts[i]) != ell + (m - m0) + k:
            raise RuntimeError('shapes of the reduced outcomes do not line up: %s' % [len(t) for t in Ts])
    # the list just before the collapse, real and reduced, after the kv visible events
    pre_real, kk = list(Lc), 'P'
    for _ in range(kv):
        pre_real, kk = law_step(pre_real, kk)
    pre_red = []
    for i, m in enumerate(ms):
        X, kx = outs[i][0][0][3], 'P'
        for _ in range(kv):
            X, kx = law_step(X, kx)
        pre_red.append(X)
    # the number of kept segments is m in each reduced run; in pre lists the kept x's are the last m+1 entries
    # before c... count the entries of pre_red that come from kept segments: the last m segments + c
    # E from the extra kept segments
    Es = []
    for i in (1, 2):
        m = ms[i]
        for t in range(1, ms[i] - m0 + 1):
            # extra kept segment: in pre_red[i] it is the (m0 + t)-th segment from the right
            x = pre_red[i][-1 - (m0 + t)]
            d = Ts[i][ell + (ms[i] - m0) - t]
            j = k + t - 2                          # segments to its right in T (c excluded)
            if (x - d) % 3 ** (j + 1):
                raise RuntimeError('extra segment not drained by whole events')
            Es.append((x - d) // 3 ** (j + 1))
    if len(set(Es)) != 1:
        raise RuntimeError('drained by different numbers of events: %s' % Es)
    E = Es[0]
    # left entries
    left = []
    for p in range(ell):
        f = fit_left([Ts[i][p] for i in range(3)], ms)
        if f is None:
            raise RuntimeError('newborn entry %d does not fit A*3^m+B: %s' % (p, [Ts[i][p] for i in range(3)]))
        A, B = f
        # the reduced runs had m segments; the real run has s_real (the same position in the real list)
        v = A * 3 ** s_real + B
        if v.denominator != 1:
            raise RuntimeError('non-integer newborn')
        left.append(int(v))
    # middle: real segments that were not kept
    nkept = m0
    real_x = pre_real[1:-1]
    nb_pre = len(pre_real) - len(Lc)          # births among the visible events
    mid_src = real_x[nb_pre:len(real_x) - nkept] if nkept else real_x[nb_pre:]
    # left part of pre_real (births) are fitted with the newborns
    mids = []
    nmid = len(mid_src)
    for i, x in enumerate(mid_src):
        j = (nmid - 1 - i) + k - 1
        mids.append(x - E * 3 ** (j + 1))
    Treal = left + mids + sigma
    info = {'kv': kv, 'E': E, 'ell': ell, 'suffix': k, 'kind': kind, 'm': ms,
            'reduced': [[(e[0], e[2], e[3]) for e in o[0][:o[2] + 8]] for o in outs]}
    if min(Treal) < 0:
        raise RuntimeError('negative entry after splice')
    return Treal, kind, info


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else 'b1'
    maxgen = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    logf = sys.argv[3] if len(sys.argv) > 3 else None
    mach, c0 = MACH[name]
    out = open(logf, 'a') if logf else None

    def log(s):
        print(s, flush=True)
        if out:
            out.write(s + '\n'); out.flush()
    n = 13
    L, kind = law_regime1(c0, n), 'P'
    ev = 3 * (n + 1)          # events since P_-1
    gen = n
    log('%s: start at P_%d (regime 1 of bmap.py), %d entries' % (name, n, len(L)))
    collapses = []
    while gen < maxgen:
        # law forward until an entry would go negative
        hist = [(L, kind, ev)]
        while True:
            nx, nk = law_step(L, kind)
            if min(nx) < 0:
                break
            L, kind = nx, nk
            ev += 1
            if kind == 'P':
                gen += 1
            hist.append((L, kind, ev))
            if gen >= maxgen:
                break
        if gen >= maxgen:
            break
        # the last P event before the failure
        while hist[-1][1] != 'P':
            hist.pop()
        Lc, _, evc = hist[-1]
        gen_c = gen - (0 if kind == 'P' else 0)
        # which entry fails, and how many entries to its right are involved
        nx, nk = law_step(L, kind)
        bad = [i for i, v in enumerate(nx) if v < 0]
        idx = bad[0]
        right = len(nx) - 1 - idx         # entries right of the failing one (c included)
        m0 = max(4, right + 3)
        log('collapse ahead: at event %d (%s->%s) entry %d of %d goes negative (%s); last P at event %d; list end %s'
            % (ev + 1, kind, nk, idx, len(nx), nx[idx], evc, Lc[-8:]))
        if Lc[0] != 2 * 3 ** (len(Lc) - 2 + 4) - 28:
            log('  generator not canonical at the last P: %d' % Lc[0])
        if m0 > 10:
            log('  a collapse with %d entries on its right (a middle collapse): the reduced runs would need %d '
                'kept segments, beyond reach of c/msimev.c; stopping here' % (right, m0))
            collapses.append({'stopped': 'middle collapse', 'event': ev + 1, 'index': idx, 'right': right,
                              'list_P': [str(x) for x in Lc]})
            break
        Treal, tk, info = collapse(mach, Lc, len(Lc) - 2, log, m0)
        if Treal is None:
            log('HALT in reduced run: %s' % info['halt'])
            collapses.append({'halt': info})
            break
        evT = evc + info['kv'] + info['E']   # events counted on the right end
        log('  spliced: kind %s, E=%d hidden events, %d newborn entries, common suffix %d; list end %s; %d entries'
            % (tk, info['E'], info['ell'], info['suffix'], Treal[-8:], len(Treal)))
        collapses.append({'event_P': evc, 'list_P_end': Lc[-10:], 'after_kind': tk, 'after_end': Treal[-10:],
                          'E': info['E'], 'kv': info['kv'], 'nentries': len(Treal)})
        L, kind, ev = Treal, tk, evT
        gen = evc // 3 - 1 + (evT - evc) // 3
    log('stopped at generation about %d, event %d, %d entries; list end %s' % (gen, ev, len(L), L[-10:]))
    if out:
        json.dump({'collapses': collapses, 'final': {'event': ev, 'kind': kind, 'list': [str(x) for x in L]}},
                  open(logf + '.json', 'w'), indent=1)


if __name__ == '__main__':
    main()
