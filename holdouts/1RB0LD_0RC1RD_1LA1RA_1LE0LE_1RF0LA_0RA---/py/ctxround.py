"""Round maps "one big block between two context words", for any two-symbol machine (trust level: computation).

Sample the run at *events*: the head in state S reading symbol b with only 0s on the far side (side L: only 0s to
its left; side R: only 0s to its right, handled by mirroring the machine).  The tape from the head inwards is then
parsed as

    A U^m B            (U^m: the longest periodic run of the word; A, B: the context words)

and a *round* is the run from one event to the next.  For a large m the round is computed from six small
representatives m0 = Q j + r (j = k0..k0+4 and 2 k0 + 7; k0 grows with the contexts): if they all give the same
contexts A', U', B', a new count that is affine in j and a step count that is a polynomial of degree <= 3 in j,
the round of the class (A, U, B, m mod Q = r) is taken to be that affine map.  This is an extrapolation from six
values, not a proof.  Q is the smallest modulus in QLIST for which the six agree.

usage:  python3 ctxround.py MACHINE SIDE STATE SYM check STEPS    compare the class rounds with the direct run
        python3 ctxround.py MACHINE SIDE STATE SYM orbit ROUNDS   iterate from the first class round of the blank-tape run
        python3 ctxround.py MACHINE SIDE STATE SYM bfs N          expand N contexts breadth first, every remainder class;
                                                                  reports the classes that halt
        python3 ctxround.py MACHINE SIDE STATE SYM bfs N MAXLEN   the same, expanding only contexts of at most MAXLEN cells
                                                                  (default 300)
(SIDE STATE SYM name the event, e.g. L D 1.)
"""
import os, subprocess, sys, re
from collections import deque

HERE = os.path.dirname(os.path.abspath(__file__))
QLIST = (1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 1024)
PMAX = 12


_EXE = None


def build():
    """Compile ../c/ctxev.c into a temporary directory (once per process)."""
    global _EXE
    if _EXE is None:
        import tempfile
        _EXE = os.path.join(tempfile.mkdtemp(), 'ctxev')
        subprocess.check_call(['gcc', '-O2', '-o', _EXE, os.path.join(HERE, '..', 'c', 'ctxev.c')])
    return _EXE


def mirror(machine):
    return machine.replace('L', 'x').replace('R', 'L').replace('x', 'R')


def parse(word, pmax=PMAX, minrep=3):
    """word -> (A, U, m, B): the periodic run covering the most cells (period <= pmax, at least minrep copies)."""
    n = len(word)
    best = None
    for p in range(1, pmax + 1):
        i = 0
        while i + p < n:
            if word[i] != word[i + p]:
                i += 1
                continue
            j = i
            while j + p < n and word[j] == word[j + p]:
                j += 1
            run = j - i + p            # cells i .. i+run-1 are p-periodic
            cnt = run // p
            if cnt >= minrep and (best is None or cnt * p > best[0]):
                best = (cnt * p, p, i, cnt)
            i = j + 1
    if best is None:
        return None
    _, p, s, cnt = best
    return word[:s], word[s:s + p], cnt, word[s + p * cnt:]


class Engine:
    def __init__(self, machine, side, state, sym, cap=2 * 10 ** 9, scale=4, k0=12, exe=None):
        self.machine0, self.side, self.state, self.sym = machine, side, state, sym
        self.machine = machine if side == 'L' else mirror(machine)
        self.cap, self.scale, self.K0 = cap, scale, k0
        self.exe = exe or build()
        self.proc = None
        self.cache = {}
        self.lastQ = None
        self.nsim = 0

    def ev(self, word):
        if self.proc is None:
            self.proc = subprocess.Popen([self.exe, self.machine, self.state, str(self.sym), str(self.cap)],
                                         stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
        self.proc.stdin.write(word + '\n')
        self.proc.stdin.flush()
        self.nsim += 1
        f = self.proc.stdout.readline().split()
        if f[0] in ('HALT', 'CAP', 'OUT'):
            return (f[0], int(f[1]))
        return ('ok', int(f[0]), f[1] if len(f) > 1 else '')

    def blank_events(self, steps):
        out = subprocess.run([self.exe, self.machine, self.state, str(self.sym), '1', 'list', str(steps)],
                             capture_output=True, text=True).stdout.split('\n')
        evs = []
        for l in out:
            f = l.split()
            if not f:
                continue
            if f[0] in ('HALT', 'OUT'):
                evs.append((f[0], int(f[1])))
            else:
                evs.append((int(f[0]), f[1] if len(f) > 1 else ''))
        return evs

    def k0(self, A, U, B, Q):
        need = max(self.K0 * 2, (self.scale * (len(A) + len(B))) // len(U) + 4)
        return max(3, -(-need // Q))

    def rep(self, A, U, B, Q, r):
        """Round of the class (A, U, B, m = r mod Q): ('ok', a, b, k0, poly, A', U', B') meaning m = Q j + r (j >= k0)
        goes to m' = a (j - k0) + b; or ('HALT', poly) / ('INCONS', why) / ('CAP',)."""
        key = (A, U, B, Q, r)
        if key in self.cache:
            return self.cache[key]
        k0 = self.k0(A, U, B, Q)
        js = [k0, k0 + 1, k0 + 2, k0 + 3, k0 + 4, 2 * k0 + 7]
        res = []
        for j in js:
            o = self.ev(A + U * (Q * j + r) + B)
            res.append(o)
            if o[0] in ('CAP', 'OUT'):
                self.cache[key] = ('CAP',)
                return self.cache[key]
        kinds = {o[0] for o in res}
        ss = [o[1] for o in res]
        d = [ss[:5]]
        for _ in range(4):
            d.append([d[-1][i + 1] - d[-1][i] for i in range(len(d[-1]) - 1)])
        poly = (d[0][0], d[1][0], d[2][0], d[3][0])
        x = js[5] - k0
        pv = poly[0] + poly[1] * x + poly[2] * x * (x - 1) // 2 + poly[3] * x * (x - 1) * (x - 2) // 6
        polyok = d[4][0] == 0 and pv == ss[5]
        if kinds == {'HALT'}:
            self.cache[key] = ('HALT', poly if polyok else None, k0)
            return self.cache[key]
        if kinds != {'ok'}:
            self.cache[key] = ('INCONS', 'mixed halt')
            return self.cache[key]
        ps = [parse(o[2]) for o in res]
        if any(p is None for p in ps):
            self.cache[key] = ('INCONS', 'no block')
            return self.cache[key]
        if len({(p[0], p[1], p[3]) for p in ps}) != 1:
            self.cache[key] = ('INCONS', 'contexts')
            return self.cache[key]
        ms = [p[2] for p in ps]
        a = ms[1] - ms[0]
        if any(ms[i] != ms[0] + a * (js[i] - k0) for i in range(6)):
            self.cache[key] = ('INCONS', 'count')
            return self.cache[key]
        self.cache[key] = ('ok', a, ms[0], k0, poly if polyok else None, ps[0][0], ps[0][1], ps[0][3])
        return self.cache[key]

    def qorder(self):
        return ([self.lastQ] if self.lastQ else []) + [q for q in QLIST if q != self.lastQ]

    def rnd(self, A, U, m, B, qmax=1024):
        """One round from (A, U, m, B) with a big m.  -> ('ok', A', U', m', B', steps|None, Q) | ('HALT', steps|None, Q) | ('?', why)"""
        why = None
        for Q in self.qorder():
            if Q > qmax:
                continue
            k0 = self.k0(A, U, B, Q)
            j, r = divmod(m, Q)
            if j < 2 * k0 + 8:
                return ('small',)
            o = self.rep(A, U, B, Q, r)
            if o[0] == 'CAP':
                return ('?', 'cap')
            if o[0] == 'INCONS':
                why = o[1]
                continue
            x = j - o[-5] if o[0] == 'ok' else j - o[2]
            poly = o[4] if o[0] == 'ok' else o[1]
            steps = None if poly is None else poly[0] + poly[1] * x + poly[2] * x * (x - 1) // 2 + poly[3] * x * (x - 1) * (x - 2) // 6
            self.lastQ = Q
            if o[0] == 'HALT':
                return ('HALT', steps, Q)
            return ('ok', o[5], o[6], o[1] * x + o[2], o[7], steps, Q)
        return ('?', why)

    def direct(self, A, U, m, B):
        o = self.ev(A + U * m + B)
        if o[0] != 'ok':
            return o
        p = parse(o[2])
        if p is None:
            return ('raw', o[1], o[2])
        return ('ok', p[0], p[1], p[2], p[3], o[1])


def rle(w, pmax=8):
    out = []; i = 0; n = len(w)
    while i < n:
        best = (1, 1)
        for p in range(1, pmax + 1):
            if i + 2 * p > n:
                break
            k = 1
            while w[i + k * p:i + (k + 1) * p] == w[i:i + p]:
                k += 1
            if k >= 3 and k * p > best[0] * best[1]:
                best = (p, k)
        p, k = best
        if k >= 3:
            out.append('(%s)^%d' % (w[i:i + p], k) if p > 1 else '%s^%d' % (w[i], k)); i += p * k
        else:
            out.append(w[i]); i += 1
    s = ' '.join(out)
    return re.sub(r'(?<=[01]) (?=[01]( |$))', '', s)


def check(eng, steps, verbose=False, mmin=None):
    """Compare the map with every event of the direct run from blank tape.  Returns (n_events, n_rounds_checked,
    n_mismatch, n_unknown, last parsed event)."""
    evs = eng.blank_events(steps)
    nchk = bad = unk = 0
    last = None
    prev = None
    for e in evs:
        if e[0] in ('HALT', 'OUT'):
            return ('HALT', e)
        p = parse(e[1])
        if prev is not None and p is not None:
            A, U, m, B = prev[1]
            o = eng.rnd(A, U, m, B)
            if o[0] == 'ok':
                nchk += 1
                okk = (o[1], o[2], o[3], o[4]) == p and (o[5] is None or o[5] == e[0] - prev[0])
                if not okk:
                    bad += 1
                    if verbose:
                        print('MISMATCH at step', e[0], 'pred', rle(o[1]), o[2], o[3], rle(o[4]), o[5], 'real', rle(p[0]), p[1], p[2], rle(p[3]), e[0] - prev[0])
            elif o[0] == 'HALT':
                bad += 1
            elif o[0] == '?':
                unk += 1
                if verbose:
                    print('UNKNOWN at step', prev[0], o, rle(A), U, m, rle(B))
        prev = (e[0], p) if p is not None else None
        if p is not None:
            last = (e[0], p)
        if verbose and p is not None:
            print(e[0], rle(p[0]), '(%s)^%d' % (p[1], p[2]), rle(p[3]))
    return (len(evs), nchk, bad, unk, last)


def iterate(eng, start, N, t0=0, report=None, stop_ctx=None):
    """Iterate from start = (A, U, m, B).  Yields nothing; returns a dict of statistics."""
    A, U, m, B = start
    t = t0
    maxctx = 0
    known = True
    for i in range(N):
        o = eng.rnd(A, U, m, B)
        if o[0] == 'small':
            o2 = eng.direct(A, U, m, B)
            if o2[0] != 'ok':
                return dict(rounds=i, stop=o2, A=A, U=U, m=m, B=B, t=t, maxctx=maxctx)
            o = ('ok', o2[1], o2[2], o2[3], o2[4], o2[5], 0)
        if o[0] != 'ok':
            return dict(rounds=i, stop=o, A=A, U=U, m=m, B=B, t=t if known else None, maxctx=maxctx)
        _, A, U, m, B, s, Q = o
        if s is None:
            known = False
        else:
            t += s
        maxctx = max(maxctx, len(A) + len(B))
        if report and (i + 1) % report == 0:
            print('  round %d: m ~ 2^%d, ctx %d+%d cells, %d classes, %d sims' % (i + 1, m.bit_length(), len(A), len(B), len(eng.cache), eng.nsim), flush=True)
        if stop_ctx and len(A) + len(B) > stop_ctx:
            return dict(rounds=i + 1, stop=('ctx',), A=A, U=U, m=m, B=B, t=t if known else None, maxctx=maxctx)
    return dict(rounds=N, stop=None, A=A, U=U, m=m, B=B, t=t if known else None, maxctx=maxctx)


def start_of(eng, steps='3e9'):
    """The first event of the direct run from blank tape whose round is computed by classes: (step, (A, U, m, B)),
    the list of all parsed events, and the modulus most used along them."""
    evs = eng.blank_events(steps)
    if evs and evs[-1][0] in ('HALT', 'OUT'):
        raise RuntimeError('direct run: %s' % (evs[-1],))
    parsed = [(e[0], parse(e[1])) for e in evs]
    parsed = [(t, p) for t, p in parsed if p is not None]
    start = None
    for t, p in parsed:
        o = eng.rnd(*p)
        if start is None and o[0] == 'ok':
            start = (t, p)
    qs = {}
    for k, v in eng.cache.items():
        if v[0] == 'ok':
            qs[k[3]] = qs.get(k[3], 0) + 1
    return start, parsed, (max(qs, key=qs.get) if qs else None), sorted(qs)


def orbit(eng, start, t0, rounds=None, seconds=None):
    """Iterate the class map from start = (A, U, m, B) (direct simulation while m is small)."""
    import time
    A, U, m, B = start
    t = t0; known = True; n = 0; maxctx = 0; stop = None; ctxs = set(); T = time.time()
    while (rounds is None or n < rounds) and (seconds is None or time.time() - T < seconds):
        o = eng.rnd(A, U, m, B)
        if o[0] == 'small':
            o2 = eng.direct(A, U, m, B)
            if o2[0] != 'ok':
                stop = o2; break
            o = ('ok', o2[1], o2[2], o2[3], o2[4], o2[5], 0)
        if o[0] != 'ok':
            stop = o; break
        _, A, U, m, B, s, q = o
        n += 1
        if s is None: known = False
        elif known: t += s
        maxctx = max(maxctx, len(A) + len(B))
        if len(ctxs) < 500000: ctxs.add((A, U, B))
    return dict(rounds=n, stop=None if stop is None else [str(x)[:80] for x in stop], m_bits=m.bit_length(),
                m_digits=int(m.bit_length() * 0.30103), steps_log10=(int(t.bit_length() * 0.30103) if known else None),
                maxctx=maxctx, lastA=rle(A)[:200], lastU=U, lastB=rle(B)[:200], distinct_ctx=len(ctxs), classes=len(eng.cache),
                halt_ctx=((rle(A), U, rle(B)) if stop is not None and stop[0] == 'HALT' else None))


def bfs(eng, start_ctx, Q, N=None, maxlen=300, seconds=None, qcap=None):
    """Explore the contexts (A, U, B) breadth first with every residue of m mod Q (finer moduli where the classes
    mod Q disagree).  Contexts longer than maxlen cells are counted (dropped) but not expanded."""
    import time
    seen = {start_ctx: 0}
    par = {start_ctx: None}

    def path(c, QQ, r):
        out = ['%d mod %d' % (r, QQ)]
        while par[c] is not None:
            c, QQ, r = par[c]
            out.append('%d mod %d' % (r, QQ))
        return out[::-1]
    q = deque([start_ctx])
    halts, unknown = [], []
    n = dropped = 0; T = time.time(); qcap = qcap or Q * 16
    while q and (N is None or n < N) and (seconds is None or time.time() - T < seconds):
        c = q.popleft(); n += 1
        todo = [(Q, r) for r in range(Q)]
        while todo:
            QQ, r = todo.pop()
            o = eng.rep(c[0], c[1], c[2], QQ, r)
            if o[0] == 'HALT':
                halts.append((seen[c] + 1, rle(c[0])[:120], c[1], rle(c[2])[:120], QQ, r, path(c, QQ, r)))
            elif o[0] == 'ok':
                c2 = (o[5], o[6], o[7])
                if c2 not in seen:
                    if len(c2[0]) + len(c2[2]) <= maxlen:
                        seen[c2] = seen[c] + 1; par[c2] = (c, QQ, r); q.append(c2)
                    else:
                        dropped += 1
            elif o[0] == 'INCONS' and QQ * 2 <= qcap:
                todo.extend((QQ * 2, r + i * QQ) for i in range(2))
            else:
                unknown.append((seen[c] + 1, rle(c[0])[:120], c[1], rle(c[2])[:120], QQ, r, str(o)[:60]))
    halts.sort(key=lambda h: h[0])
    return dict(expanded=n, seen=len(seen), queue=len(q), dropped=dropped, closed=(not q and not dropped and not unknown),
                halting=len(halts), halting_examples=halts[:5], unknown=len(unknown), unknown_examples=unknown[:5],
                maxdepth=max(seen.values()))


if __name__ == '__main__':
    import json
    if len(sys.argv) < 6:
        print(__doc__); sys.exit(1)
    machine, side, state, sym, cmd = sys.argv[1:6]
    arg = sys.argv[6] if len(sys.argv) > 6 else None
    eng = Engine(machine, side, state, sym)
    if cmd == 'check':
        r = check(eng, arg or '3e9')
        print('events %d, rounds compared %d, mismatches %d, rounds the classes do not cover %d' % r[:4])
        sys.exit(1 if r[2] else 0)
    start, parsed, Q, qs = start_of(eng)
    if cmd == 'orbit':
        print(json.dumps(orbit(eng, start[1], start[0], rounds=int(float(arg or 10000)))))
    elif cmd == 'bfs':
        A, U, m, B = start[1]
        maxlen = int(sys.argv[7]) if len(sys.argv) > 7 else 300
        print(json.dumps(bfs(eng, (A, U, B), Q, N=int(float(arg or 1000)), maxlen=maxlen, qcap=max(Q * 16, max(qs) * 2))))
