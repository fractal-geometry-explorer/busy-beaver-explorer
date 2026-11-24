"""Drive the macro: jump (odometer, many trips) when it applies, otherwise one exact trip (l1.trip)."""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from l1 import trip, fold
from macro import jump


def parse_line(line):
    """an R line of c/rtrips.c -> (step, state, toks) folded"""
    p = line.split()
    st = 'ABCDEF'.index(p[2]); t = p[5:]
    toks = [(('' if x == '-' else x) if i % 2 == 0 else int(x)) for i, x in enumerate(t)]
    toks = fold(toks); toks[0] = toks[0].lstrip('0')
    return int(p[1]), st, toks


# the first R-instant from blank tape (c/rtrips.c): step 592, state D, tape 00 a^5 1010 a^5 110
START = (592, 3, fold(['', 5, '1010', 5, '110']))


def run(s, toks, steps, maxsteps, maxtime=1e18, log=None):
    """Run until steps >= maxsteps or maxtime seconds.  log(steps, state, toks, trips) after every trip that visits
    the left end (the configuration at the next R-instant).  Returns (state, toks, steps, trips, n_trip, n_jump) or
    ('HALT', steps, toks)."""
    trips = 0; t0 = time.time(); n1 = 0; n2 = 0
    while steps < maxsteps and time.time() - t0 < maxtime:
        m, new, st = jump(s, toks)
        if m:
            toks = new; steps += st; trips += m; n2 += 1
            continue
        r = trip(s, toks)
        if r[0] == 'HALT':
            return ('HALT', steps + r[1], toks)
        s, toks, st, lv = r; steps += st; trips += 1; n1 += 1
        if lv and log:
            log(steps, s, toks, trips)
    return s, toks, steps, trips, n1, n2
