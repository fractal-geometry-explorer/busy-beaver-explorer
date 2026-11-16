"""A faster exact accelerated run of 1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA--- (same rules as accel.py, local work).

accel.py rebuilds, re-tokenises and re-parses the whole tape at every event; that is O(number of digits) per event
and became the cost of the run (10^2000 steps).  Here the tape is a list of *chunks* (cells before a block, block
length): chunk 0 is (cells, n0), chunk i >= 1 is (separator of digit i, n_i), and the last chunk may be (end cells,
None).  The normal prefix is chunk 0 with no cells and then the chunks whose separator is one of the four digit
separators.  Everything is the same as in accel.py, but local:

* bulk: t = min(4^k - 1 - V, min_i Vb_i - V - 1) with Vb_i (the V at which block i would drop below 1) kept in a heap:
  Vb_i does not change during bulks (when digit i wraps, V // 4^(i+1) goes up by one and N_i down by one), so it is
  computed once per digit and again only when a simulated sweep changes that digit.  Only the digits below the
  highest digit that changes are touched (their wraps, timers and step counts), as in accel.bulk.
* overflow (every digit 3, the end 01): in closed form, every block + 1, separators 0101 -> 0, 1010 in front, in
  6 n0 + 6 (n_1 + ... + n_k) + 10 k + 15 steps (fitted on the run, checked against rlsim on every overflow of the
  compared stretch and on random counters).
* simulated sweep: only a window of chunks is turned into tokens (up to the first digit below 3, plus guard chunks,
  or the whole tape when the carry runs into the irregular part); the run-length simulator rlsim.Sim runs the sweep
  on it and the window is re-chunked.  If the head comes near the end of the window the sweep is redone on a larger
  window, so the result is the exact sweep.

usage: python3 accel2.py run 1eX [checkpoint]   run to 10^X steps (progress lines, catalogue of irregular cells)
       python3 accel2.py compare 1eX            compare with accel.run at every simulated sweep (tape, steps)
       python3 accel2.py overtest N             the closed-form overflow against rlsim on N random counters
       (environment: OVERCHECK=1 checks every closed-form overflow against rlsim; NOFASTOVER=1 simulates them)
"""
import collections
import heapq
import os
import pickle
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.set_int_max_str_digits(0)
from rlsim import Sim, canon, head_first  # noqa: E402
import accel  # noqa: E402

M = accel.M
S, R, C = accel.S, accel.R, accel.C
STATE_C = accel.STATE_C


class Halt(Exception):
    pass


DIG = {'00': 0, '01': 1, '10': 2, '11': 3}
FASTOVER = [os.environ.get('NOFASTOVER') is None]
OVERCHECK = [os.environ.get('OVERCHECK') is not None]


class Run:
    def __init__(self):
        tok, steps = accel.first()
        self.steps = steps
        self.sweeps = 0
        self.chunks = rechunk(tok, True)
        self.nfull = 0
        self.nsweep = 0
        self.nbulk = 0
        self.nover = 0
        self.full_recompute()

    # ------------------------------------------------------------ the normal prefix
    def full_recompute(self):
        ch = self.chunks
        self.nfull += 1
        d, N = [], []
        if ch[0][0] == '':
            for sep, n in ch[1:]:
                if n is None or sep not in R or n < 1:
                    break
                di = R[sep]
                d.append(di)
                N.append(n + C[di])
        self.d, self.N = d, N
        self.ok0 = ch[0][0] == ''
        self.V = int(''.join(str(x) for x in reversed(d)), 4) if d else 0
        self.VB = [self.vb(i) for i in range(len(d))]
        self.heap = [(v, i) for i, v in enumerate(self.VB)]
        heapq.heapify(self.heap)

    def vb(self, i):
        sh, q, Ni = 2 * (i + 1), 1 << (2 * i), self.N[i]
        hi = self.V >> sh
        if Ni >= 3:
            return (hi + (Ni - 2)) << sh | 3 * q
        if Ni == 2:
            return hi << sh | 3 * q
        return hi << sh | q

    def minvb(self):
        h = self.heap
        while h:
            v, i = h[0]
            if i < len(self.VB) and self.VB[i] == v:
                return v
            heapq.heappop(h)
        return None

    # ------------------------------------------------------------ bulk
    def bulk(self):
        if not self.ok0:
            return False
        d, N = self.d, self.N
        k = len(d)
        V = self.V
        t = 4 ** k - 1 - V
        m = self.minvb()
        if m is not None:
            if m <= V:
                return False
            t = min(t, m - V - 1)
        if t <= 0:
            return False
        V2 = V + t
        x = V ^ V2
        hd = (x.bit_length() - 1) // 2          # highest digit that changes
        lowmask = (1 << (2 * (hd + 1))) - 1
        a, b = V & lowmask, V2 & lowmask
        n0 = self.chunks[0][1]
        steps = 8 * (t * n0 + t * (t - 1) // 2) + 6 * t
        aa, bb = a >> 2, b >> 2
        for i in range(hd):
            w = bb - aa                       # wraps of digit i: V crosses a multiple of 4^(i+1)
            if w:
                Ni = N[i]
                steps += w * (8 * (Ni - 2) + 10) - 8 * w * (w - 1) // 2
                N[i] = Ni - w
            aa >>= 2
            bb >>= 2
        m = min(hd + 1, k)
        bits = bin(b)[2:].zfill(2 * m)
        L = len(bits)
        ch = self.chunks
        for i in range(m):
            di = DIG[bits[L - 2 * i - 2:L - 2 * i]]
            d[i] = di
            n = N[i] - C[di]
            assert n > 0
            ch[i + 1] = (S[di], n)
        self.chunks[0] = ('', n0 + t)
        self.V = V2
        self.steps += steps
        self.sweeps += t
        self.nbulk += 1
        return True

    # ------------------------------------------------------------ one simulated sweep
    def sweep(self):
        ch = self.chunks
        k = len(self.d)
        j = None
        if self.ok0:
            for i in range(k):
                if self.d[i] < 3:
                    j = i
                    break
        # last chunk index of the window: the chunk of the first digit below 3, or the first irregular chunk; then
        # two guard chunks (the window grows if the head gets near its end)
        e = (j + 1 if j is not None else (k + 1 if self.ok0 else 0)) + 2
        while True:
            whole = e >= len(ch) - 1
            e = min(e, len(ch) - 1)
            toks = materialize(ch[:e + 1])
            last = len(materialize(ch[e:e + 1]))
            s = Sim(M, head_first(toks), STATE_C)
            s.dir, s.steps = -1, self.steps
            r, dmin = run_track(s, self.steps)
            if r == 'halt':
                raise Halt(s.steps)
            if whole or dmin > last + 1:
                break
            e = 2 * e + 2
        if s.h < 0:
            s.tok.insert(0, ['0', 1])
        new = rechunk(canon(s.tok, minrun=1), whole)
        self.steps = s.steps
        self.sweeps += 1
        self.nsweep += 1
        old_k = k
        ch[:e + 1] = new
        # update the prefix locally when the window kept its shape and stayed normal
        if (len(new) == e + 1 and new[0][0] == '' and self.ok0 and old_k >= e and not whole and
                all(n is not None and sep in R and n >= 1 for sep, n in new[1:])):
            V = self.V
            for i in range(e):
                sep, n = new[i + 1]
                di = R[sep]
                V += (di - self.d[i]) * 4 ** i
                self.d[i] = di
                self.N[i] = n + C[di]
            self.V = V
            for i in range(e):
                v = self.vb(i)
                if v != self.VB[i]:
                    self.VB[i] = v
                    heapq.heappush(self.heap, (v, i))
        else:
            self.full_recompute()

    # ------------------------------------------------------------ the overflow, in closed form
    def overflow_shape(self):
        """every digit 3, nothing irregular, the end 01: the carry runs into the end"""
        ch = self.chunks
        k = len(self.d)
        return (self.ok0 and k >= 1 and len(ch) == k + 2 and ch[-1] == ('01', None) and
                self.V == 4 ** k - 1)

    def overflow(self):
        """C> a^n0 (0101 a^n_i)_i 01  ->  C> 1010 a^n0 (0 a^(n_i+1))_i 01  in 6 n0 + 6 sum n_i + 10 k + 15 steps
        (found on the run and checked against the run-length simulator: OVERCHECK, and accel2.py overtest)"""
        ch = self.chunks
        k = len(self.d)
        n0 = ch[0][1]
        S = 0
        for i in range(1, k + 1):
            n = ch[i][1]
            S += n
            ch[i] = ('0', n + 1)
        ch[0] = ('1010', n0)
        self.steps += 6 * n0 + 6 * S + 10 * k + 15
        self.sweeps += 1
        self.nover += 1
        self.full_recompute()

    def step(self):
        if not self.bulk():
            if FASTOVER[0] and self.overflow_shape():
                if OVERCHECK[0]:
                    saved = (list(self.chunks), self.steps, self.sweeps)
                    self.sweep()
                    want = (list(self.chunks), self.steps, self.sweeps)
                    self.chunks[:] = saved[0]
                    self.steps, self.sweeps = saved[1], saved[2]
                    self.full_recompute()
                    self.overflow()
                    assert (self.chunks, self.steps, self.sweeps) == want, 'overflow law fails'
                    self.nsweep += 1
                else:
                    self.overflow()
                return 'F'
            self.sweep()
            return 'F'
        return 'B'

    def tokens(self):
        return materialize(self.chunks)


def materialize(chunks):
    out = []
    for sep, n in chunks:
        out.extend([c, 1] for c in sep)
        if n is not None:
            out.append(['001', n])
    return out


def rechunk(toks, whole):
    out = []
    cur = ''
    for w, n in toks:
        if w == '001':
            out.append((cur, n))
            cur = ''
        else:
            cur += w * n
    if whole:
        cur = cur.rstrip('0')
        if cur:
            out.append((cur, None))
    else:
        assert cur == '', cur
    return out


def run_track(s, steps0):
    """rlsim.Sim.run until the sweep ends (C at the left end), tracking how close the head came to the right end"""
    tok = s.tok
    dmin = len(tok)
    while True:
        h = s.h
        if h < 0:
            tok.insert(0, ['0', 1]); h = 0
        elif h >= len(tok):
            tok.append(['0', 1])
        if len(tok) - h < dmin:
            dmin = len(tok) - h
        w, n = tok[h]
        dd = s.dir
        if not (n == 1 and len(w) == 1):
            r = s.cross(w, s.q, dd)
            if r is not None and r[0] == s.q and r[2] == dd:
                tok[h] = [r[1], n]
                s.steps += n * r[3]
                s.h = h + dd
                continue
            h = s.explode(h, dd)
            if len(tok) - h < dmin:
                dmin = len(tok) - h
        tr = s.t[(s.q, int(tok[h][0]))]
        if tr is None:
            s.halted = True; s.steps += 1; s.h = h
            return 'halt', dmin
        b, mv, q = tr
        tok[h][0] = str(b); s.q = q; s.dir = mv; s.h = h + mv; s.steps += 1
        if s.q == STATE_C and s.h <= 0 and s.steps > steps0:
            return 'stop', dmin


def norm_tok(tok):
    t = [list(x) for x in tok]
    while t and t[-1][0] == '0':
        t.pop()
    return t


def compare(maxsteps):
    old = accel.run(maxsteps)
    r = Run()
    n = 0
    for kind, steps, sweeps, tok in old:
        if kind == 'B':
            continue
        while True:
            k2 = r.step()
            if k2 == 'F':
                break
        a = canon(norm_tok(tok), minrun=1)
        b = canon(norm_tok(r.tokens()), minrun=1)
        assert (steps, sweeps) == (r.steps, r.sweeps), (n, steps, r.steps, sweeps, r.sweeps)
        assert a == b, (n, a[:20], b[:20])
        n += 1
    print('ok: %d simulated sweeps agree with accel.py (tape, step and sweep counts) up to %d steps' % (n, maxsteps))


def main_run(maxexp, ckpt=None, every=600):
    r = None
    if ckpt and os.path.exists(ckpt):
        r = pickle.load(open(ckpt, 'rb'))
        print('resumed at 10^%d steps' % (len(str(r.steps)) - 1), flush=True)
    if r is None:
        r = Run()
    maxsteps = 10 ** maxexp
    cat = collections.Counter()
    t0 = tlast = time.time()
    mark = len(str(r.steps))
    while r.steps < maxsteps:
        if r.step() == 'F':
            for sep, n in r.chunks:
                if sep not in R and sep != '':
                    cat[sep] += 1
        while r.steps >= 10 ** mark:
            print('steps >= 1e%d  sweeps 1e%d  digits %d  bulks %d  simulated sweeps %d  overflows %d  %.0fs' % (
                mark, len(str(r.sweeps)) - 1, len(r.chunks) - 2, r.nbulk, r.nsweep, r.nover, time.time() - t0),
                flush=True)
            mark += 10 if mark < 300 else 100
        if ckpt and time.time() - tlast > every:
            pickle.dump(r, open(ckpt + '.tmp', 'wb'))
            os.replace(ckpt + '.tmp', ckpt)
            tlast = time.time()
    if ckpt:
        pickle.dump(r, open(ckpt + '.tmp', 'wb'))
        os.replace(ckpt + '.tmp', ckpt)
    print('no halt; final step count has %d digits (%d sweeps, %d digits)' % (len(str(r.steps)), r.sweeps,
                                                                               len(r.chunks) - 2))
    print('irregular cell patterns seen after simulated sweeps (count, cells):')
    for k, v in cat.most_common(40):
        print(' ', v, k)


def overtest(trials):
    """the overflow law against the run-length simulator on random counters (k digits all 3, random blocks)"""
    import random
    rnd = random.Random(5)
    for _ in range(trials):
        k = rnd.randint(1, 40)
        r = Run.__new__(Run)
        r.steps, r.sweeps, r.nfull, r.nsweep, r.nbulk, r.nover = 0, 0, 0, 0, 0, 0
        big = rnd.choice([10, 1000, 10 ** 30])
        r.chunks = [('', rnd.randint(2, big))] + [('0101', rnd.randint(1, big)) for _ in range(k)] + [('01', None)]
        r.full_recompute()
        assert r.overflow_shape()
        saved = list(r.chunks)
        r.sweep()
        want = (list(r.chunks), r.steps)
        r.chunks[:] = saved
        r.steps = 0
        r.full_recompute()
        r.overflow()
        assert (r.chunks, r.steps) == want, (saved, want)
    print('ok: the overflow law agrees with the run-length simulator on %d random counters' % trials)


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'overtest':
        overtest(int(sys.argv[2]))
        sys.exit()
    x = int(sys.argv[2].split('e')[1])
    if cmd == 'compare':
        compare(10 ** x)
    else:
        try:
            main_run(x, sys.argv[3] if len(sys.argv) > 3 else None)
        except Halt as h:
            print('HALT at step', h.args[0])
