"""The gap counter of lean/Counter.lean, in Python.

A state is the list of gaps of the configuration `0^inf 1 1 1 C> 0 0 1 [0^g 1]... 0^inf` (`cfg` in Counter.lean).

    python3 py/model.py check DUMP     compare the model with the machine (DUMP from c/gapdump)
    python3 py/model.py run K          K bounces from [1,1,1,1,0] (step 71), printing every 10^4th
    python3 py/model.py far SECONDS    accelerated run (whole counts of bounces at once), for SECONDS

`bounce_lean` is a line-by-line transcription of `scanM`/`stopM`/`retStep`/`finish` on flat lists; `bounce` is the
same map on run-length lists `[[gap, count], ...]`, which is what the checks and runs use.
"""
import sys
import time

START = [1, 1, 1, 1, 0]


# --- the Lean definitions, on flat lists ---------------------------------------------------------------------

def stop_lean(G):
    if len(G) >= 2 and G[0] == 1: return ('N', [G[1] + 2] + G[2:])
    if G[:2] == [2, 1]: return ('N', [3, 0] + G[2:])
    if G == [2]: return ('N', [5, 1, 0])
    if len(G) >= 2 and G[0] == 0 and G[1] >= 2: return ('N', [1, 0, G[1] - 2] + G[2:])
    if G == [0]: return ('N', [1, 0])
    if len(G) >= 3 and G[:2] == [4, 1] and G[2] >= 2: return ('N', [1, 1, 1, 1, 0, G[2] - 2] + G[3:])
    if G and G[0] >= 7: return ('P', [1, 0, G[0] - 6] + G[1:])
    if G == [4]: return ('P', [1, 1, 1, 1, 0])
    if G == [6]: return ('P', [1, 0, 0])
    if G == [2, 0]: return ('P', [3, 0])
    if G[:3] == [0, 0, 0]: return 'halt'
    if G[:2] == [4, 0]: return 'halt'
    return None


def scan_lean(G):
    ts = []
    while True:
        if G[:1] == [3]: ts.append('blk'); G = G[1:]
        elif G[:1] == [5]: ts.append('five'); G = G[1:]
        elif G[:2] == [0, 1]: ts.append('merge'); G = G[2:]
        elif G[:4] == [0, 0, 3, 3]: ts.append('zz'); G = G[4:]
        elif G[:2] == [2, 3]: ts.append('t23'); G = G[2:]
        else:
            s = stop_lean(G)
            return None if s is None else (ts, s)


RET = {('blk', 'N'): ('N', [3]), ('five', 'N'): ('N', [1, 1, 1]), ('merge', 'N'): ('P', []),
       ('zz', 'N'): ('P', [3, 0, 1]), ('blk', 'P'): ('P', [3]), ('five', 'P'): ('P', [1, 1, 1]),
       ('merge', 'P'): ('N', [1, 1, 1]), ('zz', 'P'): ('P', [5, 3]), ('t23', 'N'): ('N', [3, 0, 1]),
       ('t23', 'P'): ('N', [5, 3])}


def bounce_lean(G):
    r = scan_lean(G)
    if r is None: return 'stuck'
    ts, s = r
    if s == 'halt': return 'halt'
    m, H = s
    for t in reversed(ts):
        m, pre = RET[(t, m)]
        H = pre + H
    return ([3] if m == 'N' else [1, 1, 1]) + H


# --- the same map on run-length lists ------------------------------------------------------------------------

def norm(g):
    out = []
    for b, e in g:
        if e <= 0: continue
        if out and out[-1][0] == b: out[-1][1] += e
        else: out.append([b, e])
    return out


def bounce(g):
    """One bounce on a run-length list; returns the new list, 'halt' or 'stuck'."""
    g = [list(x) for x in g]
    i = 0                      # run index; g[:i] is passed
    toks = []                  # (token, count) in sweep order

    def gap(k):                # the k-th gap from position i (flat), or None
        j = i
        while j < len(g):
            if k < g[j][1]: return g[j][0]
            k -= g[j][1]; j += 1
        return None

    def take(k):               # consume k flat gaps from position i
        nonlocal i
        while k:
            c = min(k, g[i][1]); g[i][1] -= c; k -= c
            if g[i][1] == 0: i += 1

    while True:
        a = gap(0)
        if a == 3: c = g[i][1]; toks.append(('blk', c)); take(c); continue
        if a == 5: c = g[i][1]; toks.append(('five', c)); take(c); continue
        b = gap(1)
        if a == 0 and b == 1: toks.append(('merge', 1)); take(2); continue
        if a == 0 and b == 0 and gap(2) == 3 and gap(3) == 3: toks.append(('zz', 1)); take(4); continue
        if a == 2 and b == 3: toks.append(('t23', 1)); take(2); continue
        c3 = gap(2)
        rest_empty = lambda k: gap(k) is None
        if a == 1 and b is not None: take(2); m, pre = 'N', [[b + 2, 1]]
        elif a == 2 and b == 1: take(2); m, pre = 'N', [[3, 1], [0, 1]]
        elif a == 2 and rest_empty(1): take(1); m, pre = 'N', [[5, 1], [1, 1], [0, 1]]
        elif a == 0 and b is not None and b >= 2: take(2); m, pre = 'N', [[1, 1], [0, 1], [b - 2, 1]]
        elif a == 0 and rest_empty(1): take(1); m, pre = 'N', [[1, 1], [0, 1]]
        elif a == 4 and b == 1 and c3 is not None and c3 >= 2: take(3); m, pre = 'N', [[1, 4], [0, 1], [c3 - 2, 1]]
        elif a >= 7: take(1); m, pre = 'P', [[1, 1], [0, 1], [a - 6, 1]]
        elif a == 4 and rest_empty(1): take(1); m, pre = 'P', [[1, 4], [0, 1]]
        elif a == 6 and rest_empty(1): take(1); m, pre = 'P', [[1, 1], [0, 2]]
        elif a == 2 and b == 0 and rest_empty(2): take(2); m, pre = 'P', [[3, 1], [0, 1]]
        elif a == 0 and b == 0 and c3 == 0: return 'halt'
        elif a == 4 and b == 0: return 'halt'
        else: return 'stuck'
        break
    H = pre + [x for x in g[i:] if x[1] > 0]
    out = []                   # built right to left: prefixes in reverse
    for t, c in reversed(toks):
        if t == 'blk': out.append([[3, c]])
        elif t == 'five': out.append([[1, 3 * c]])
        elif t == 'merge':
            if m == 'N': m = 'P'
            else: m = 'N'; out.append([[1, 3]])
        elif t == 'zz':
            if m == 'N': m = 'P'; out.append([[3, 1], [0, 1], [1, 1]])
            else: out.append([[5, 1], [3, 1]])
        elif t == 't23':
            out.append([[3, 1], [0, 1], [1, 1]] if m == 'N' else [[5, 1], [3, 1]]); m = 'N'
    pre2 = [[3, 1]] if m == 'N' else [[1, 3]]
    for p in reversed(out): pre2 += p
    return norm(pre2 + H)


def flat(g): return [b for b, e in g for _ in range(e)]


def parse_dump(line):
    f = line.split()
    g = [[int(x) for x in t.split('^')] for t in f[2:-1]]
    return int(f[0]), f[1] + f[-1], g


def check(fn):
    L = [parse_dump(l) for l in open(fn) if 'HALT' not in l]
    L = [x for x in L if x[0] >= 71]
    bad = 0; nl = 0
    for (s1, lt1, a), (s2, lt2, b) in zip(L, L[1:]):
        r = bounce(a)
        if lt1 != '2||0' or r != norm(b):
            bad += 1
            if bad < 5: print('MISMATCH at step', s1, a[:10], '->', b[:10], 'model', r if isinstance(r, str) else r[:10])
        if nl < 3000 and sum(e for _, e in a) < 3000:   # the flat transcription agrees
            nl += 1
            assert bounce_lean(flat(a)) == (r if isinstance(r, str) else flat(r)), s1
    print('bounces checked', len(L) - 1, 'mismatches', bad, 'flat cross-checks', nl, 'last step', L[-1][0])


# --- acceleration ---------------------------------------------------------------------------------------------

DIG = {(1, 3): 2, (1, 1): 1, (5, 1): 0}
SEP = {2: [1, 3], 1: [1, 1], 0: [5, 1]}


def jump(g):
    """Apply at once a run of bounces that all stop inside the leading ternary digits.

    The list starts 3^n0 [s1] 3^m1 [s2] 3^m2 ... with separators s = 1 1 1, 1, 5 (digits 2, 1, 0): one bounce is a
    ternary decrement (2 -> 1 moves a 3 into the block before, 1 -> 0 takes a 3 from the block after).  With value
    V = sum d_j 3^(j-1), each of the next V bounces stops inside these digits.  The largest W <= V is taken for which
    no block runs out (block_j minus the 3s it loses stays >= 1); returns (W, the list after W bounces)."""
    i = 0; n0 = 0
    if g and g[0][0] == 3: n0 = g[0][1]; i = 1
    ds, ms = [], []
    while i + 1 < len(g) and tuple(g[i]) in DIG and g[i + 1][0] == 3:
        ds.append(DIG[tuple(g[i])]); ms.append(g[i + 1][1]); i += 2
    rest = g[i:]
    k = len(ds)
    V = sum(d * 3 ** j for j, d in enumerate(ds))
    if V == 0: return 0, g

    def counts(W):
        c2, c1 = [], []
        for j in range(k):
            c = V // 3 ** j - (V - W) // 3 ** j
            full, r = divmod(c, 3)
            cnt = [full] * 3
            for t in range(r): cnt[(ds[j] - t) % 3] += 1
            c2.append(cnt[2]); c1.append(cnt[1])
        return c2, c1

    def ok(W):
        c2, c1 = counts(W)
        return all(ms[j] - c1[j] >= 1 for j in range(k))

    lo, hi = 0, V
    if not ok(V):
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if ok(mid): lo = mid
            else: hi = mid - 1
        W = lo
    else: W = V
    if W == 0: return 0, g
    c2, c1 = counts(W)
    nb = [n0 + W + c2[0]] + list(ms)
    for j in range(k):
        nb[j + 1] -= c1[j]
        if j + 1 < k: nb[j + 1] += c2[j + 1]
    R = V - W
    out = [[3, nb[0]]]
    for j in range(k):
        out += [SEP[(R // 3 ** j) % 3], [3, nb[j + 1]]]
    return W, norm(out + rest)


def skeleton(g): return tuple((b if b != 3 else 3, e if b != 3 else 0) for b, e in g)


def blocks(g): return [e for b, e in g if b == 3]


def setblocks(g, bl):
    it = iter(bl); return [[b, next(it) if b == 3 else e] for b, e in g]


def macro(g):
    """One jump and one single bounce: (bounces, new list or 'halt'/'stuck')."""
    D, g = jump(g)
    r = bounce(g)
    return D + 1, r


def far(seconds, report=10 ** 6):
    g, nb, nm, t0 = norm([[x, 1] for x in START]), 0, 0, time.time()
    hist = []                                   # (skeleton, blocks, nb) after each macro step
    ext = 0
    last = time.time()
    while time.time() - t0 < seconds:
        D, r = macro(g)
        if isinstance(r, str):
            print(r.upper(), 'after', nb + D, 'bounces', g[:20]); return
        nb += D; nm += 1; g = r
        hist.append((skeleton(g), blocks(g), nb)); hist = hist[-7:]
        # periodic extrapolation: the same skeleton every p macro steps with the same block changes
        for p in (1, 2, 3):
            if len(hist) < 2 * p + 1: continue
            (s0, b0, n0_), (s1, b1, n1_), (s2, b2, n2_) = hist[-1 - 2 * p], hist[-1 - p], hist[-1]
            if not (s0 == s1 == s2 and len(b0) == len(b1) == len(b2)): continue
            d1 = [y - x for x, y in zip(b0, b1)]; d2 = [y - x for x, y in zip(b1, b2)]
            if d1 != d2 or n1_ - n0_ != n2_ - n1_: continue
            T = min([(b - 2 * abs(d)) // -d for b, d in zip(b2, d1) if d < 0] or [10 ** 9])
            while T > 1:
                gT = setblocks(g, [b + T * d for b, d in zip(b2, d1)])
                # verify one period from the far end (the conditions are boxes in the block sizes)
                h, ok, nn = gT, True, 0
                for _ in range(p):
                    DD, h = macro(h)
                    nn += DD
                    if isinstance(h, str): ok = False; break
                if ok and skeleton(h) == s2 and [y - x for x, y in zip(blocks(gT), blocks(h))] == d1 and nn == n2_ - n1_:
                    g = gT; nb += T * (n2_ - n1_); ext += 1; hist = []
                    break
                T //= 2
            break
        if time.time() - last > 60:
            last = time.time()
            print('bounces ~10^%d' % (len(str(nb)) - 1), 'macro', nm, 'extrapolations', ext, 'list', len(g),
                  'n0 digits', len(str(blocks(g)[0])) if blocks(g) else 0, '%.0fs' % (time.time() - t0)); sys.stdout.flush()
    print('no halt or stuck: bounces ~10^%d' % (len(str(nb)) - 1), 'list', len(g), g[:6] + [['...']] + g[-6:])


def test_jump(K):
    """Jumps agree with single bounces."""
    g = norm([[x, 1] for x in START]); n = 0
    while n < K:
        D, h = jump(g)
        x = g
        for _ in range(D): x = bounce(x)
        assert x == h, (g, D)
        r = bounce(h); n += D + 1
        if isinstance(r, str): print(r); return
        g = r
    print('jumps agree with single bounces for', n, 'bounces')


def run(K):
    g = norm([[x, 1] for x in START])
    for k in range(K):
        r = bounce(g)
        if isinstance(r, str): print('bounce', k, r, g); return
        g = r
        if k % 10000 == 0: print(k, len(g), g[:12])
    print('after', K, 'bounces', g)


if __name__ == '__main__':
    if sys.argv[1] == 'check': check(sys.argv[2])
    elif sys.argv[1] == 'run': run(int(sys.argv[2]))
    elif sys.argv[1] == 'testjump': test_jump(int(sys.argv[2]))
    elif sys.argv[1] == 'far': far(float(sys.argv[2]))
