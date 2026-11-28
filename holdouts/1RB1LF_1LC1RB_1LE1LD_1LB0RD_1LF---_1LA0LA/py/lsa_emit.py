"""Emitter jumps: an eater that leaves a frozen word behind it at every cycle, taken K cycles at once.

Below phase 37,593 from visit 10^3200 the rest of machine 2's word starts with an eater whose every cycle of 11
hits uses 6 units of its (100)^a fuel, gives the rest below it 2 hits, and leaves one more copy of the frozen word
u = 43104030001040001010 in front of it: e0 u^n e1 (100)^a Y -> e0 u^(n+1) e1 (100)^(a-6) h^2(Y).  The ladder cuts
the copies of u into levels that pass every hit, so the eater got all 10^12 hits one at a time.

jump(q, T) runs the eater region (the head of T up to and a little past its fuel) on an opaque rest, one hit at a
time, and looks for a period p after which the digits before the first large run have one more copy of a word u
inserted at a fixed place, the large runs have changed by fixed amounts, and the rest has had c more hits.  It
checks this over CHECK periods, that u is frozen (geng.frozen_cost: h(u X) = u h(X) for every X), that the same
hits happen with every large run made smaller (so the eater uses the runs only as being large) and with more
copies of u in place.  Then it takes K periods at once: u^n becomes a run token (u)^(n+K), the large runs move K
times their change, and the rest gets its c K hits from the caller's power function.  An observed law, checked on
every use, like lsa_law; the frozen word and the opaque rest are exact.
"""
import geng
from geng import build, to_tokens, tok_digits, from_digits

NHITS = 700         # single hits measured
PMAX = 300          # longest period (hits)
CHECK = 4           # periods checked
BIG = 50            # a run longer than this counts as large
SHIFT = 7777        # the large runs are made this much smaller in the check
EXTRA = 2           # more copies of u in the check
SAFE = 10 ** 4      # a large run that falls must stay above this
STAT = {'jump': 0, 'fail': 0, 'neg': 0}
NEG = set()


def _big(x):
    return type(x) is tuple and x[0] in ('P', 'R', 'Z') and type(x[1]) is int and x[1] > BIG


def _form(tk):
    """(digits before the first large run, the tokens from it on with the large counts cut out, the counts,
    the opaque rest's hit count)"""
    j = next((i for i, x in enumerate(tk) if _big(x)), None)
    if j is None or tk[-1][0] != 'O':
        return None
    D = tok_digits(tk[:j], 10 ** 6)
    if D is None:
        return None
    rest = tk[j:-1]
    sig = tuple((x[0], '#') + tuple(x[2:]) if _big(x) else x for x in rest)
    cnt = tuple(x[1] for x in rest if _big(x))
    return tuple(D), sig, cnt, tk[-1][1]


def _run(E, n):
    W = build(list(E), (('O', 0), None))
    out = []
    c0 = geng.C[0]
    try:
        for k in range(n + 1):
            f = _form(to_tokens(W))
            if f is None:
                return out
            out.append((f, geng.C[0] - c0))
            if k < n:
                W = geng.h(W)
    except (geng.Opaque, geng.Budget, geng.Event, RecursionError):
        pass
    finally:
        geng.C[0] = c0
    return out


def _insertion(a, b):
    """(i, u) if b = a[:i] + u + a[i:] (the longest common prefix), else None"""
    if len(b) <= len(a):
        return None
    i = 0
    while i < len(a) and a[i] == b[i]:
        i += 1
    u = b[i:i + len(b) - len(a)]
    if b[i + len(u):] != a[i:]:
        return None
    return i, u


def _find(H):
    n = len(H)
    for p in range(1, PMAX + 1):
        for k0 in range(0, n - CHECK * p):
            f0 = H[k0][0]
            f1 = H[k0 + p][0]
            if f1[1] != f0[1]:
                continue
            ins = _insertion(f0[0], f1[0])
            if ins is None:
                continue
            i, u = ins
            dc = tuple(y - x for x, y in zip(f0[2], f1[2]))
            do = f1[3] - f0[3]
            good = True
            for j in range(CHECK + 1):
                fj = H[k0 + j * p][0]
                if fj[1] != f0[1] or fj[0] != f0[0][:i] + u * j + f0[0][i:] or \
                        any(c != c0 + j * d for c, c0, d in zip(fj[2], f0[2], dc)) or fj[3] != f0[3] + j * do:
                    good = False
                    break
            if not good:
                continue
            # the cost of a period grows by the same amount each period (the hits cross one more u)
            cs = [H[k0 + (j + 1) * p][1] - H[k0 + j * p][1] for j in range(CHECK)]
            if any(cs[j + 1] - cs[j] != cs[1] - cs[0] for j in range(CHECK - 1)):
                continue
            return k0, p, i, u, dc, do, cs[0], cs[1] - cs[0]
    return None


def _variant(E, H, k0, p, i, u, shift, extra):
    """E with its large runs made `shift` smaller and `extra` more copies of u at hit k0's insertion point is not
    known in token form, so the check is run from the start: the large runs of E made smaller give the same hits"""
    E2 = [(x[0], x[1] - shift) + tuple(x[2:]) if _big(x) else x for x in E]
    H2 = _run(E2, len(H) - 1)
    if len(H2) != len(H):
        return False
    for (f, c), (f2, c2) in zip(H, H2):
        if f[0] != f2[0] or f[1] != f2[1] or f[3] != f2[3] or \
                any(x - y != shift for x, y in zip(f[2], f2[2])):
            return False
    return True


def jump(q, T, power):
    """(word, hits used) after taking whole periods of an emitter at the head of T, at most q hits, or None.
    power(n, X) gives the rest X its n hits: (word, True) or (word, done) on an event"""
    pt = []
    X = T
    while X is not None and len(pt) < 96:
        pt.append(X[0]); X = X[1]
    fi = next((i for i, x in enumerate(pt) if _big(x) and x[0] == 'P'), None)
    if fi is None:
        return None
    for extra in range(0, 41):
        if fi + 1 + extra > len(pt):
            break
        E = pt[:fi + 1 + extra]
        key = tuple(('*',) + tuple(x[2:]) if _big(x) else x for x in E)
        if key in NEG:
            STAT['neg'] += 1
            continue
        H = _run(E, NHITS)
        if len(H) <= NHITS:
            NEG.add(key)          # the eater read into the rest: take in more of it
            continue
        r = _find(H)
        if r is None:
            NEG.add(key)
            STAT['fail'] += 1
            return None
        k0, p, i, u, dc, do, c1, dcost = r
        if geng.frozen_cost(tuple(u)) is None or not _variant(E, H, k0, p, i, u, SHIFT, 0):
            NEG.add(key)
            STAT['fail'] += 1
            return None
        # the number of copies of u does not matter either: put EXTRA more in front of the insertion point at hit
        # k0 and run CHECK periods from there
        f0 = H[k0][0]
        Rtoks = _tokens(f0, E, k0, H)
        if Rtoks is None:
            STAT['fail'] += 1
            return None
        D0 = f0[0]
        Dx = D0[:i] + u * EXTRA + D0[i:]
        Hx = _run(to_tokens(from_digits(list(Dx))) + Rtoks, CHECK * p)
        if len(Hx) != CHECK * p + 1:
            STAT['fail'] += 1
            return None
        for j in range(CHECK + 1):
            fj = H[k0 + j * p][0]; fx = Hx[j * p][0]
            if fx[0] != fj[0][:i] + u * EXTRA + fj[0][i:] or fx[1] != fj[1] or fx[2] != fj[2] or \
                    fx[3] - Hx[0][0][3] != fj[3] - f0[3]:
                STAT['fail'] += 1
                return None
        # how many periods: within q, and every falling large run stays large
        K = (q - k0) // p
        for c, d in zip(f0[2], dc):
            if d < 0:
                K = min(K, (c - SAFE) // (-d))
        if K < 2:
            return None
        # the word: k0 single hits, then K periods
        cnt = [c + K * d for c, d in zip(f0[2], dc)]
        toks = to_tokens(from_digits(list(D0[:i]))) + [('P', K, tuple(u))] + to_tokens(from_digits(list(D0[i:])))
        it = iter(cnt)
        for x in f0[1]:
            if type(x) is tuple and len(x) > 1 and x[1] == '#':
                toks.append((x[0], next(it)) + tuple(x[2:]))
            else:
                toks.append(x)
        nrest = f0[3] + K * do
        geng.C[0] = geng.C[0] + H[k0][1] + K * c1 + dcost * K * (K - 1) // 2
        Y, done = power(nrest, _after(T, len(E)))
        if done is not True:
            return None
        STAT['jump'] += 1
        return build(toks, Y), k0 + K * p
    return None


def _after(T, n):
    for _ in range(n):
        T = T[1]
    return T


def _tokens(f0, E, k0, H):
    """the tokens from the first large run on (opaque rest left out) at hit k0"""
    W = build(list(E), (('O', 0), None))
    c0 = geng.C[0]
    try:
        for _ in range(k0):
            W = geng.h(W)
    finally:
        geng.C[0] = c0
    tk = to_tokens(W)
    j = next(i for i, x in enumerate(tk) if _big(x))
    return tk[j:-1]
