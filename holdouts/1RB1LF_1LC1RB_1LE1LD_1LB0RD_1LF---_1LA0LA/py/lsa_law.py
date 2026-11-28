"""Law phases: an eater whose super-cycle block is not regular, but whose cost per unit of fuel repeats exactly.

After phase 28,829 from visit 10^3200 the eater 3 4 0^1 4 3 0^3 10 3 4 0^3 (10)^1 (43400010)^1.8e9 has a super-cycle of
33,549 hits (9 units of fuel), but the block it leaves ends in a lone 0^6, which is not a level, at every hit of the
cycle.  Measured hit by hit (geng.hpow on the eater region followed by an opaque rest), the top hits between
successive units of fuel repeat with period 18 units, each period 2^24 times the one before, the rest gets 33 hits a
period, and the word after a period is a new 141-token block followed by the word before it, unchanged but for the
fuel.  The hits into that word after K periods cost 2^(24K) top hits each.  That is the phase law of G (run_to_event,
unwind) with a = 2^24, b = 0, P = the top hits of one period.

detect() measures this on the region, checks it over CHECK periods exactly, and returns the super-cycle in the form of
lsa_phase's (with 'law' set), or ('align', h) when the law holds from h hits on, or None.  It is an observed law, checked
on every use, not a symbolic proof like lsa_eater.supercycle.
"""
import time
import geng
from geng import build, to_tokens, hpow

PMAXL = 40          # longest period (units of fuel)
NDEC = 130          # most units of fuel measured
CHECK = 3           # periods checked exactly
BUDGET = 1800       # seconds for one detection
STAT = {'law': 0, 'align': 0, 'fail': 0}


def _fuel(toks, w):
    for x in toks:
        if type(x) is tuple and x[0] == 'P' and x[2] == w:
            return x[1]
    return None


def _ocount(toks):
    x = toks[-1]
    return x[1] if type(x) is tuple and x[0] == 'O' else None


def measure(E, fi, t0):
    """yields (units of fuel used, cumulative region hits, rest hits so far, tokens) at each fuel decrement"""
    w = E[fi][2]
    T = build(list(E), (('O', 0), None))
    f0 = E[fi][1]
    f = f0; tot = 0
    yield (0, 0, 0, to_tokens(T))
    n = 0
    while n < NDEC and time.time() - t0 < BUDGET:
        lo, hi = 0, 1
        while True:
            U, d = hpow(hi, T)
            if d is not True:
                return
            if _fuel(to_tokens(U), w) < f:
                break
            lo, hi = hi, hi * 2
            if hi > 1 << 400:
                return
        while hi - lo > 1:
            mid = (lo + hi) // 2
            U, d = hpow(mid, T)
            if _fuel(to_tokens(U), w) < f:
                hi = mid
            else:
                lo = mid
        T, d = hpow(hi, T)
        tot += hi
        tk = to_tokens(T)
        f = _fuel(tk, w)
        if f is None:
            return
        n += 1
        yield (f0 - f, tot, _ocount(tk), tk)


def detect(E, fi):
    try:
        return _detect(list(E), fi)
    except (geng.Opaque, geng.Budget, geng.Event, RecursionError):
        STAT['fail'] += 1
        return None


def _detect(E, fi):
    t0 = time.time()
    units = {}
    for u, hh, o, tk in measure(E, fi, t0):
        units[u] = (hh, o, tk)
        r = _find(E, fi, units, u)
        if r is not None:
            return r
    STAT['fail'] += 1
    return None


def _find(E, fi, units, last):
    """a law whose last checked unit is `last` (the unit just measured), or None"""
    us = sorted(units)
    for p in range(1, PMAXL + 1):
        k0 = last - p * CHECK
        if k0 < 0:
            break
        if any((k0 + n * p) not in units for n in range(CHECK + 1)):
            continue
        H = [units[k0 + n * p][0] for n in range(CHECK + 1)]
        O = [units[k0 + n * p][1] for n in range(CHECK + 1)]
        S = [H[n + 1] - H[n] for n in range(CHECK)]
        if S[0] <= 0 or S[1] % S[0]:
            continue
        a = S[1] // S[0]
        if a < 2 or a & (a - 1):
            continue
        if any(S[n + 1] != a * S[n] for n in range(CHECK - 1)):
            continue
        c = O[1] - O[0]
        if any(O[n + 1] - O[n] != c for n in range(CHECK)):
            continue
        # every single step inside the checked periods scales too
        bad = False
        for u in us:
            if k0 < u <= last - p and u - 1 in units and u + p in units and u + p - 1 in units:
                if units[u + p][0] - units[u + p - 1][0] != a * (units[u][0] - units[u - 1][0]):
                    bad = True; break
        if bad:
            continue
        # the word after a period: a block, then the word before it, unchanged but for the fuel
        good = True
        for n in range(CHECK):
            A = units[k0 + n * p][2][:-1]
            B = units[k0 + (n + 1) * p][2][:-1]
            if len(B) < len(A):
                good = False; break
            for x, y in zip(B[len(B) - len(A):], A):
                if x != y and not (type(x) is tuple and x[0] == 'P' and type(y) is tuple and y[0] == 'P'
                                   and x[2] == y[2] == E[fi][2] and y[1] - x[1] == p):
                    good = False; break
            if not good:
                break
        if not good:
            continue
        # the earliest unit from which the law holds: step back while the single steps still scale
        k1 = k0
        while k1 - 1 in units and k1 + p - 1 in units and k1 + p in units and \
                units[k1 + p][0] - units[k1 + p - 1][0] == a * (units[k1][0] - units[k1 - 1][0]):
            k1 -= 1
        if k1 == 0 and p not in units:
            k1 = min(u for u in units if u > 0)
        if k1 > 0:
            STAT['align'] += 1
            return ('align', units[k1][0], k1)
        STAT['law'] += 1
        return dict(P=S[0] if k0 == 0 else (units[p][0] - units[0][0]), dm=p, c=c, blk=('LAW', a, p, c), a=a,
                    law=True, mmin=p + 1, cost=(0, 0))
    return None


def pass_positions(sc, E, fi):
    """region hits (1..P) of the first period at which the rest gets its hits"""
    T = build(list(E), (('O', 0), None))
    pos = []
    o0 = 0
    for k in range(1, sc['c'] + 1):
        lo, hi = 0, sc['P']
        while hi - lo > 1:
            mid = (lo + hi) // 2
            U, d = hpow(mid, T)
            if _ocount(to_tokens(U)) >= k:
                hi = mid
            else:
                lo = mid
        pos.append(hi)
    return pos
