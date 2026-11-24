"""cjump: an exact accelerated simulator for runs made of binary counters on either side of a hub.

Direct simulation, plus: at successive visits of the head to a hub turn (state S reading r at position P, the
head turning from left-moving to right-moving), the tape is read as   ... L-digits | hub | R-digits ...   with
digit blocks of fixed widths wL, wR next to the hub, each block one of two words p, q.  A model is learned from
observed hub events and accepted only if it predicts every observed event exactly (whole tape and step count).
Then whole stretches of counting are jumped: each event takes, on each side, the lowest digit equal to p to q and
the digits below it from q to p (a decrement of the number whose 1-digits are the p blocks).  A jump stops before a
borrow could reach the top parsed digit of a side (that digit may not belong to the counter); the next event is
simulated directly and checked against the model, and on any mismatch the model is dropped and relearned.
Step counts are exact Python integers: an event costs base + alpha*dL + beta*dR steps (dL, dR digits changed),
fitted exactly on the observed events.

Trust: trusted computation.  Exact as long as the counters keep their observed rule for the higher digits.

usage: python3 tools/py/bbtools/cjump.py MACHINE MAXSTEPS SECONDS [VERBOSE]     (MAXSTEPS 1e3000: no limit)
"""
import sys, time, itertools, ctypes, os, subprocess, tempfile, hashlib


def _load():
    """tools/c/cjrun.c, compiled on first use into the temporary directory (keyed by the source's hash)"""
    src = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'c', 'cjrun.c')
    h = hashlib.sha1(open(src, 'rb').read()).hexdigest()[:12]
    so = os.path.join(tempfile.gettempdir(), f'cjrun-{h}.so')
    if not os.path.exists(so):
        tmp = so + f'.{os.getpid()}'
        subprocess.run(['gcc', '-O2', '-shared', '-fPIC', '-o', tmp, src], check=True)
        os.replace(tmp, so)
    return ctypes.CDLL(so)


_lib = _load()
_lib.cj_run.restype = ctypes.c_int
_lib.cj_run.argtypes = [ctypes.c_void_p, ctypes.c_int64, ctypes.c_int64] + [ctypes.c_void_p] * 6 + [ctypes.c_void_p, ctypes.c_int64, ctypes.c_int64, ctypes.c_int, ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int64, ctypes.c_int64]
from fractions import Fraction
from collections import Counter
DEBUG = False

def parse_tm(s):
    T = {}
    for i, g in enumerate(s.split('_')):
        for r in (0, 1):
            t = g[3*r:3*r+3]
            T[(i, r)] = None if t[2] in '-Z' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return T

def popcount(x): return bin(x).count('1')


class Sim:
    def __init__(self, tm, n=1 << 14):
        self.tab = [None] * 16
        for (s, r), v in parse_tm(tm).items(): self.tab[2 * s + r] = v
        self.c = bytearray(n); self.off = n // 2
        ct = []
        for i in range(16):
            v = self.tab[i] if i < 12 else None
            ct += [v[0], v[1], v[2]] if v else [0, 0, -1]
        self._ctab = (ctypes.c_int * 48)(*ct)
        self.lo = 0; self.hi = 0; self.head = 0; self.state = 0; self.steps = 0; self.dir = 0; self.halted = False

    def grow(self):
        n = len(self.c); nc = bytearray(2 * n); nc[n // 2:n // 2 + n] = self.c; self.c = nc; self.off += n // 2

    def seg(self, a, b):
        while a + self.off < 0 or b + self.off > len(self.c): self.grow()
        return bytes(self.c[a + self.off:b + self.off])

    def setseg(self, a, data):
        while a + self.off < 0 or a + len(data) + self.off > len(self.c): self.grow()
        self.c[a + self.off:a + self.off + len(data)] = data

    def run(self, maxsteps, key=None, skip_first=False, turns=None):
        """Step until the step count reaches maxsteps, a halt, or (key given) the head is at a turn matching key
        (P, S, r): the configuration is then the one before the turning step.  turns: a Counter of all turns seen.
        Uses the C stepper cjrun.so."""
        P, S, R = key if key is not None else (-(1 << 62), -1, -1)
        first = ctypes.c_int(1 if skip_first else 0)
        while True:
            budget = maxsteps - self.steps
            if budget <= 0: return 'max'
            budget = min(budget, 1 << 62)
            c = self.c; N = len(c)
            buf = (ctypes.c_uint8 * N).from_buffer(c)
            h = ctypes.c_int64(self.head); st = ctypes.c_int(self.state); done = ctypes.c_int64(0)
            d = ctypes.c_int(self.dir); lo = ctypes.c_int64(self.lo); hi = ctypes.c_int64(self.hi)
            hist = None; hbase = 0; hlen = 0
            if turns is not None:
                hbase = self.lo - 64; hlen = self.hi - self.lo + 129
                hist = (ctypes.c_int64 * (hlen * 16))()
            ret = _lib.cj_run(buf, N, self.off, ctypes.byref(h), ctypes.byref(st), ctypes.byref(done), ctypes.byref(d),
                              ctypes.byref(lo), ctypes.byref(hi), self._ctab, budget, P, S, R, ctypes.byref(first),
                              hist, hbase, hlen)
            del buf
            self.head, self.state, self.dir, self.lo, self.hi = h.value, st.value, d.value, lo.value, hi.value
            self.steps += done.value
            if hist is not None:
                for j in range(hlen * 16):
                    if hist[j]: turns[(hbase + j // 16, (j % 16) // 2, j % 2)] += hist[j]
            if ret == 3:
                self.grow(); continue
            if ret == 2: self.halted = True; return 'halt'
            if ret == 1: return 'event'
            return 'max'


class Model:
    """key = (P, S, r).  Side models: (a, w, p, q) or None; L digits are blocks [a-(j+1)w, a-jw), R blocks
    [a+jw, a+(j+1)w), j = 0 the lowest digit.  cost = (base, alpha, beta)."""
    def __init__(self, key, L, R, cost, period=1):
        self.key, self.L, self.R, self.cost, self.period = key, L, R, cost, period
        self.sepL = (); self.sepR = (); self.sepcost = {}

    def parse(self, sim, side, full=False):
        """digits outward from the hub (the lowest digit has its own width and words); with full=True also
        (positions, separator crossed after each digit)"""
        m = self.L if side == 'L' else self.R
        a, w0, p0, q0, w, p, q = m
        seps = (self.sepL if side == 'L' else self.sepR) or ()
        digs = []; pos = []; sepafter = []
        x = a; j = 0
        while True:
            ww, pp, qq = (w0, p0, q0) if j == 0 else (w, p, q)
            if side == 'L':
                if x - ww < sim.lo - 1: break
                b = sim.seg(x - ww, x)
            else:
                if x + ww > sim.hi + 2: break
                b = sim.seg(x, x + ww)
            if b == pp: digs.append(1)
            elif b == qq: digs.append(0)
            else: break
            pos.append(x - ww if side == 'L' else x)
            x = x - ww if side == 'L' else x + ww
            j += 1
            hit = None
            for u in seps:
                n = len(u); mm = 0; y = x
                while True:
                    y2 = y - n if side == 'L' else y + n
                    if (sim.seg(y2, y) if side == 'L' else sim.seg(y, y2)) != u: break
                    y = y2; mm += 1
                    if side == 'L' and y - w < sim.lo - 1 or side == 'R' and y + w > sim.hi + 2: break
                    nb = sim.seg(y - w, y) if side == 'L' else sim.seg(y, y + w)
                    if nb in (p, q): hit = ((u, mm), y)
                if hit: break
            if hit: sepafter.append(hit[0]); x = hit[1]
            else: sepafter.append(None)
        self.stop = getattr(self, 'stop', {}); self.stop[side] = x
        if full: return digs, pos, sepafter
        return digs

    def write(self, sim, side, digs, pos):
        a, w0, p0, q0, w, p, q = self.L if side == 'L' else self.R
        for j, (x, dgt) in enumerate(zip(pos, digs)):
            if j == 0: sim.setseg(x, p0 if dgt else q0)
            else: sim.setseg(x, p if dgt else q)

    def cost_of(self, f):
        sol, null = self.coef
        tot = sum((sol.get(c, 0) * v for c, v in f.items()), Fraction(0))
        exact = all(sum((nv.get(c, 0) * v for c, v in f.items()), Fraction(0)) == 0 for nv in null)
        exact = exact and tot.denominator == 1
        return int(tot), exact

    def add_row(self, f, cost):
        self.rows.append((f, cost))
        if len(self.rows) > 400: self.rows = self.rows[-200:]
        coef, ident, cons = fit_cost(self.rows)
        if not cons: return False
        self.coef = coef
        return True

    def counters(self, sim):
        """the two counters as read now: per side (number of digits, value, digit indices followed by a separator)"""
        out = []
        for side in 'LR':
            digs, pos, sa = self.parse(sim, side, True)
            out.append(f"{side}: n={len(digs)} v={digits_value(digs)} seps={[j for j, x in enumerate(sa) if x]}")
        return '; '.join(out)

    def desc(self):
        f = lambda m: None if m is None else (m[0], m[1], ''.join(map(str, m[2])), ''.join(map(str, m[3])), m[4], ''.join(map(str, m[5])), ''.join(map(str, m[6])))
        g = lambda ss: [''.join(map(str, x)) for x in ss]
        h = lambda c: c if not isinstance(c, tuple) else (c[0], ''.join(map(str, c[1])))
        sol = {str(h(k)): str(v) for k, v in self.coef[0].items()} if getattr(self, 'coef', None) else {}
        return (f"key={self.key} period={self.period} L={f(self.L)} sepL={g(self.sepL)} R={f(self.R)} "
                f"sepR={g(self.sepR)} cost={sol} free={len(self.coef[1]) if getattr(self, 'coef', None) else '?'}")


def digits_value(digs): return sum(1 << j for j, d in enumerate(digs) if d)

def ctz1(v):  # digits changed by one decrement of v (v >= 1)
    return (v & -v).bit_length()


def features_k(model, parsed, k):
    """feature totals of k events from the parsed state: {'n':k, 'dL':..., 'dR':..., ('L',sep):crossings, ...}"""
    f = Counter(); f['n'] = k
    for side, (d, pos, sa) in parsed.items():
        v = digits_value(d); v2 = v - k
        f['d' + side] += 2 * k + popcount(v2) - popcount(v)
        for j, sw in enumerate(sa):
            if sw is None or j + 1 >= len(d): continue
            m = 1 << (j + 1)     # borrow from v' crosses the separator after digit j iff 2^(j+1) | v'
            c = v // m - v2 // m
            if c: f[(side, sw[0])] += c * sw[1]
    return f


def room(model, sim):
    """largest k such that k events change no top digit on either side"""
    ks = []; parsed = {}
    for side in ('L', 'R'):
        if (model.L if side == 'L' else model.R) is None: continue
        d, pos, sa = model.parse(sim, side, full=True)
        if not d: return 0, parsed
        parsed[side] = (d, pos, sa)
        ks.append(digits_value(d[:-1]))
    return min(ks), parsed


def apply_events(sim, model, k, parsed):
    f = features_k(model, parsed, k)
    for side, (d, pos, sa) in parsed.items():
        v2 = digits_value(d) - k
        model.write(sim, side, [(v2 >> j) & 1 for j in range(len(d))], pos)
    cost, exact = model.cost_of(f)
    sim.steps += cost
    return cost, exact


class Fake:
    """a tape view for parsing a stored snapshot"""
    def __init__(self, t, base, l, h):
        self.t, self.base, self.lo, self.hi = t, base, l, h
    def seg(self, a, b):
        out = bytearray()
        for x in range(a, b):
            i = x - self.base
            out.append(self.t[i] if 0 <= i < len(self.t) else 0)
        return bytes(out)
    def setseg(self, a, data):
        for i, x in enumerate(range(a, a + len(data))):
            self.t[x - self.base] = data[i]


def predict_one(m, tape, base, l, h):
    """apply one event to a snapshot; returns (new tape, features) or None if a top digit would change"""
    f = Fake(bytearray(tape), base, l + 4, h - 4)
    parsed = {}
    for side in ('L', 'R'):
        if (m.L if side == 'L' else m.R) is None: continue
        d, pos, sa = m.parse(f, side, full=True)
        if not d or digits_value(d[:-1]) == 0: return None
        parsed[side] = (d, pos, sa)
    feats = features_k(m, parsed, 1)
    for side, (d, pos, sa) in parsed.items():
        v2 = digits_value(d) - 1
        m.write(f, side, [(v2 >> j) & 1 for j in range(len(d))], pos)
    return bytes(f.t), feats


def fit_cost(rows):
    """rows: list of (features Counter, cost).  Exact rational solve; returns (sol dict with free variables 0,
    null-space basis (list of dicts), consistent)."""
    cols = sorted({c for f, _ in rows for c, v in f.items() if v}, key=str)
    A = [[Fraction(f.get(c, 0)) for c in cols] + [Fraction(y)] for f, y in rows]
    n = len(cols); r = 0; piv = []
    for c in range(n):
        pr = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if pr is None: continue
        A[r], A[pr] = A[pr], A[r]
        pv = A[r][c]; A[r] = [x / pv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                fct = A[i][c]; A[i] = [A[i][j] - fct * A[r][j] for j in range(n + 1)]
        piv.append(c); r += 1
    consistent = all(A[i][n] == 0 for i in range(r, len(A)))
    sol = {cols[c]: A[i][n] for i, c in enumerate(piv)}
    null = []
    for fc in range(n):
        if fc in piv: continue
        vec = {cols[fc]: Fraction(1)}
        for i, c in enumerate(piv): vec[cols[c]] = -A[i][fc]
        null.append(vec)
    return (sol, null), True, consistent


def primitive(wd):
    n = len(wd)
    for k in range(1, n + 1):
        if n % k == 0 and wd[:k] * (n // k) == wd: return wd[:k]
    return wd


def find_seps(tapes, ch, lo, side, x, w, p, q, maxsep=24):
    """trusted separator words walking outward from x (the outer edge of the digit block next to the lowest
    one) in the last snapshot: a separator is the non-digit stretch between digit runs, located with the cells
    that changed beyond it in the observed events (none of its own cells may change)."""
    t = tapes[-1]
    D = [i for i in range(w) if p[i] != q[i]]
    seps = []
    def blk(x0, x1): return t[x0 - lo:x1 - lo] if x0 >= lo and x1 - lo <= len(t) else None
    allc = sorted({z for c in ch for z in c}); allset = set(allc)
    while True:
        b = blk(x - w, x) if side == 'L' else blk(x, x + w)
        if b in (p, q):
            cells = range(x - w, x) if side == 'L' else range(x, x + w)
            changed = any(z in allset for z in cells)
            beyond = any((z < x - w) if side == 'L' else (z >= x + w) for z in allc)
            if changed or not beyond:
                x = x - w if side == 'L' else x + w; continue
        if side == 'L':
            beyond = [z for z in allc if z < x]
            if not beyond: break
            y = max(beyond) - max(D) + w
            if not (x - maxsep <= y < x) or blk(y - w, y) not in (p, q): break
            if any(y <= z < x for z in allc): break
            seps.append(blk(y, x)); x = y
        else:
            beyond = [z for z in allc if z >= x]
            if not beyond: break
            y = min(beyond) - min(D)
            if not (x < y <= x + maxsep) or blk(y, y + w) not in (p, q): break
            if any(x <= z < y for z in allc): break
            seps.append(blk(x, y)); x = y
    return seps


def learn(sim, key, nev=64, log=None):
    """simulate nev hub events at key and fit a model; returns Model or None (the sim is advanced)."""
    evs = []
    skip = (sim.head, sim.state) == (key[0], key[1])
    while len(evs) < nev:
        res = sim.run(sim.steps + 10 ** 7, key=key, skip_first=skip)
        skip = True
        if res != 'event': return None
        lo, hi = sim.lo - 4, sim.hi + 4
        evs.append((sim.steps, lo, hi, sim.seg(lo, hi)))
    P = key[0]
    good = []
    for per in (1, 2, 4):
        es = evs[::per]
        if len(es) < 12: break
        lo = min(e[1] for e in es); hi = max(e[2] for e in es)
        tapes = [bytes(l - lo) + t + bytes(hi - h) for st, l, h, t in es]
        chL = []; chR = []; ok = True
        for t0, t1 in zip(tapes, tapes[1:]):
            dif = [i + lo for i in range(len(t0)) if t0[i] != t1[i]]
            chL.append([x for x in dif if x < P]); chR.append([x for x in dif if x > P])
            if P in dif: ok = False
        if not ok: continue
        sides = {}
        for side, ch in (('L', chL), ('R', chR)):
            allc = [x for c in ch for x in c]
            if not allc: sides[side] = [None]; continue
            a = max(allc) + 1 if side == 'L' else min(allc)
            depth = lambda c: (a - min(c)) if side == 'L' else (max(c) + 1 - a)
            depths = sorted(set(depth(c) for c in ch if c))
            w0 = depths[0]
            cands = []
            if w0 > 12: sides[side] = cands; continue
            def blk(t, x0, x1): return t[x0 - lo:x1 - lo]
            if side == 'L': b0 = lambda t: blk(t, a - w0, a)
            else: b0 = lambda t: blk(t, a, a + w0)
            words0 = set(b0(t) for t in tapes)
            if len(words0) != 2: sides[side] = cands; continue
            low0 = set(range(a - w0, a)) if side == 'L' else set(range(a, a + w0))
            pq0 = None
            for x, y in itertools.permutations(sorted(words0)):
                if any(b0(tapes[i]) == x and b0(tapes[i + 1]) == y and set(c) <= low0 for i, c in enumerate(ch)):
                    pq0 = (x, y); break
            if pq0 is None: sides[side] = cands; continue
            for w in range(1, 9):
                if side == 'L': b1 = lambda t: blk(t, a - w0 - w, a - w0)
                else: b1 = lambda t: blk(t, a + w0, a + w0 + w)
                words = set(b1(t) for t in tapes)
                if len(words) != 2: continue
                low1 = set(range(a - w0 - w, a)) if side == 'L' else set(range(a, a + w0 + w))
                for x, y in itertools.permutations(sorted(words)):
                    if any(b1(tapes[i]) == x and b1(tapes[i + 1]) == y and set(c) <= low1 and
                           (side == 'L' and min(c) < a - w0 or side == 'R' and max(c) >= a + w0)
                           for i, c in enumerate(ch)):
                        trusted = []
                        x0 = a - w0 if side == 'L' else a + w0
                        for sw in find_seps(tapes, ch, lo, side, x0, w, x, y):
                            u = primitive(sw)
                            if u not in trusted: trusted.append(u)
                        cands.append(((a, w0, pq0[0], pq0[1], w, x, y), tuple(sorted(trusted, key=len, reverse=True))))
                        break
            sides[side] = cands
        for cL in sides['L']:
            for cR in sides['R']:
                if cL is None and cR is None: continue
                m = Model(key, cL[0] if cL else None, cR[0] if cR else None, None, per)
                m.sepL = cL[1] if cL else (); m.sepR = cR[1] if cR else ()
                rows = []; bad = False
                for i in range(len(tapes) - 1):
                    pr = predict_one(m, tapes[i], lo, es[i][1], es[i][2])
                    if pr is None: continue
                    if pr[0] != tapes[i + 1]:
                        bad = True
                        if DEBUG:
                            t0, t1, t2 = tapes[i], pr[0], tapes[i + 1]
                            dif = [j + lo for j in range(len(t1)) if t1[j] != t2[j]]
                            print('  mismatch at', dif[:10], 'P', P)
                            x0 = min(dif) - 12; x1 = max(dif) + 12
                            for t in (t0, t1, t2): print('   ', ''.join(map(str, t[x0 - lo:x1 - lo])))
                        break
                    rows.append((pr[1], es[i + 1][0] - es[i][0]))
                if DEBUG: print('cand', per, m.L, m.R, m.sepL, m.sepR, 'bad' if bad else len(rows))
                if bad or len(rows) < 8: continue
                coef, ident, cons = fit_cost(rows)
                if not cons: continue
                m.rows = rows; m.coef = coef
                f = Fake(bytearray(tapes[-1]), lo, es[-1][1] + 4, es[-1][2] - 4)
                rm, _ = room(m, f)
                score = (len(rows) * per, rm, -per)
                good.append((score, m))
    if good:
        good.sort(key=lambda x: x[0])
        m = good[-1][1]
        # the model was checked on every per-th event from the first: step on to the next such event, so that jumps
        # start in the phase the model was learned in
        for _ in range((-(len(evs) - 1)) % m.period):
            if sim.run(sim.steps + 10 ** 8, key=key, skip_first=True) != 'event': return None
        return m
    return None


def learn_sep_online(model, before, after, lo):
    """if this event's borrow crossed the stretch where a side's parse stops, unchanged, add it as a separator"""
    if after is None or len(before) != len(after): return
    f = Fake(bytearray(before), lo, lo + 4, lo + len(before) - 5)
    chg = [i + lo for i in range(len(before)) if before[i] != after[i]]
    for side in ('L', 'R'):
        m = model.L if side == 'L' else model.R
        if m is None: continue
        a, w0, p0, q0, w, p, q = m
        d, pos, sa = model.parse(f, side, full=True)
        x = model.stop[side]
        D = [i for i in range(w) if p[i] != q[i]]
        if side == 'L':
            beyond = [z for z in chg if z < x]
            if not beyond: continue
            y = max(beyond) - max(D) + w
            if not (x - 24 <= y < x) or any(y <= z < x for z in chg): continue
            if f.seg(y - w, y) not in (p, q): continue
            sw = primitive(f.seg(y, x))
            if sw not in model.sepL:
                old = model.sepL; model.sepL = tuple(model.sepL) + (sw,)
                pr = predict_one(model, before, lo, lo + 4, lo + len(before) - 5)
                if pr is None or pr[0] != after: model.sepL = old
        else:
            beyond = [z for z in chg if z >= x]
            if not beyond: continue
            y = min(beyond) - min(D)
            if not (x < y <= x + 24) or any(x <= z < y for z in chg): continue
            if f.seg(y, y + w) not in (p, q): continue
            sw = primitive(f.seg(x, y))
            if sw not in model.sepR:
                old = model.sepR; model.sepR = tuple(model.sepR) + (sw,)
                pr = predict_one(model, before, lo, lo + 4, lo + len(before) - 5)
                if pr is None or pr[0] != after: model.sepR = old


def hub_key(sim, window, n=1):
    """the most frequent turn of the next `window` steps (with n > 1: the n most frequent, most frequent first)"""
    turns = Counter()
    res = sim.run(sim.steps + window, turns=turns)
    if res == 'halt' or not turns: return None
    keys = sorted(turns, key=lambda k: (-turns[k], k))
    return keys[0] if n == 1 else keys[:n]


def learn_best(sim, keys, nev):
    """learn at each candidate hub turn and keep the model with the most room to jump (None if none fits)"""
    best = None
    for key in keys:
        m = learn(sim, key, nev=nev)
        if sim.halted: return None
        if m is None: continue
        r = room(m, sim)[0]
        if best is None or r > best[0]: best = (r, m)
    if best is None: return None
    if best[1].key == keys[-1] or len(keys) == 1: return best[1]
    # the run is at an event of another key: learn the chosen one again, which ends in its own phase
    return learn(sim, best[1].key, nev=nev)


def event_step(sim, model):
    """simulate (directly) to the next model event (period events); returns 'event' or other"""
    for _ in range(model.period):
        res = sim.run(sim.steps + 10 ** 8, key=model.key, skip_first=True)
        if res != 'event': return res
    return 'event'


def accel(tm, maxsteps, maxtime=60.0, log=sys.stdout, warm=100000, verbose=1, snaps=None):
    sim = Sim(tm)
    sim.run(warm)
    t0 = time.time(); small = 0; mid = 0; nev = 64; model = None; njumps = 0; jumped = 0; fails = 0; exact = True
    middesc = None; midoff = False; lastdesc = None
    lastrep = t0
    while sim.steps < maxsteps and time.time() - t0 < maxtime:
        if model is None:
            window = min(2 * 10 ** 6, max(30000, 30000 * (1 + fails)))
            keys = hub_key(sim, window, n=4)
            if sim.halted: break
            if not keys: continue
            key = keys[0]
            model = learn_best(sim, keys, nev)
            if sim.halted: break
            if model is None:
                fails += 1
                if verbose and fails in (1, 10, 100, 1000): print(f"[{sim.steps:.4e}] no model at {key} ({fails} tries)", file=log, flush=True)
                continue
            fails = 0
            if middesc is not None:
                # relearnt over more events after short jumps: the same model again means the counter is just short
                midoff = model.desc() == middesc; middesc = None
                if midoff: nev = 64
            elif model.desc() != lastdesc: midoff = False
            lastdesc = model.desc()
            if verbose: print(f"[{sim.steps:.4e}] learned {model.desc()}\n    counters {model.counters(sim)}", file=log, flush=True)
        k, parsed = room(model, sim)
        small = small + 1 if k < 64 and not midoff else 0
        mid = mid + 1 if k < 1 << 14 and not midoff else 0
        if k >= 1 << 14: nev = 64
        if small > 300 or mid > 3000:
            # short jumps: a separator or digit kind not seen while learning; learn again over more events (if
            # that gives the same model, the counter is just short: keep it until the model changes)
            nev = min(4 * nev, 4096); middesc = model.desc()
            small = 0; mid = 0; model = None
            if verbose: print(f"[{sim.steps:.4e}] small jumps: relearning over {nev} events", file=log, flush=True)
            continue
        if k >= 2 and sim.steps + model.cost_of(features_k(model, parsed, k))[0] > maxsteps - 10 ** 6:
            # do not jump past maxsteps: the largest k that stays below it (costs grow with k)
            a, b = 0, k
            while a < b:
                c = (a + b + 1) // 2
                if sim.steps + model.cost_of(features_k(model, parsed, c))[0] <= maxsteps - 10 ** 6: a = c
                else: b = c - 1
            k = a
        didjump = k >= 2
        if k >= 2:
            cost, ex = apply_events(sim, model, k, parsed)
            exact = exact and ex
            njumps += 1; jumped += k
            if verbose > 1: print(f"  jump {k} events -> {sim.steps}", file=log)
        lo, hi = sim.lo - 4, sim.hi + 4
        snap = sim.seg(lo, hi); st0 = sim.steps
        res = event_step(sim, model)
        if res == 'halt': break
        if res != 'event':
            if verbose: print(f"[{sim.steps:.4e}] no event at {model.key} in 10^8 steps\n    counters before {model.counters(Fake(bytearray(snap), lo, lo + 4, hi - 4))}", file=log, flush=True)
            model = None; continue
        now = sim.seg(lo, hi) if (sim.lo - 4, sim.hi + 4) == (lo, hi) else None
        if now is not None: learn_sep_online(model, snap, now, lo)
        if snaps is not None and didjump and len(snaps) < 400:
            snaps.append((sim.steps, sim.head, sim.state, sim.lo, sim.seg(sim.lo, sim.hi + 1)))
        pr = predict_one(model, snap, lo, lo, hi)
        if pr is None: continue
        if now != pr[0] or not model.add_row(pr[1], sim.steps - st0):
            if verbose: print(f"    counters before {model.counters(Fake(bytearray(snap), lo, lo + 4, hi - 4))}", file=log)
            if verbose: print(f"[{sim.steps:.4e}] model broke ({'tape' if now != pr[0] else 'cost'})", file=log, flush=True)
            model = None
        if verbose and time.time() - lastrep > 30:
            lastrep = time.time(); print(f"  ... steps {sim.steps:.4e} width {sim.hi - sim.lo + 1} jumps {njumps}", file=log, flush=True)
    return sim, dict(jumps=njumps, events_jumped=jumped, learn_fails=fails, time=round(time.time() - t0, 1), steps_exact=exact)


if __name__ == '__main__':
    tm = sys.argv[1]; mx = (int(float(sys.argv[2])) if float(sys.argv[2]) < 1e300 else 10 ** 3000) if len(sys.argv) > 2 else 10 ** 30
    tl = float(sys.argv[3]) if len(sys.argv) > 3 else 60
    sim, info = accel(tm, mx, tl, verbose=int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    print(('HALT' if sim.halted else 'running'), sim.steps, 'width', sim.hi - sim.lo + 1, info)


def sim_from_tapeat(tm, line):
    """a Sim from a line 'SNAP N HEAD_OFFSET STATE CELLS' of tools/c/tapeat.c"""
    p = line.split()
    n, hoff, st, cells = int(p[1]), int(p[2]), p[3], p[4]
    sim = Sim(tm, n=max(1 << 14, 4 * len(cells)))
    sim.setseg(0, bytes(int(x) for x in cells))
    sim.head = hoff; sim.state = ord(st) - 65 if st.isalpha() else int(st); sim.steps = n
    sim.lo = 0; sim.hi = len(cells) - 1; sim.dir = 0
    return sim
