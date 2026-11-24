"""Odometer-jump run of 1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA--- with lazy timers (same rules as accel2.py).

accel2.py does O(number of digits) Python work at almost every event: its bulk visits every digit below the highest
one that changes, and almost every simulated sweep ends in a full recompute of the counter.  Since irregular
patterns sit near the bottom of the counter (the low chunks) and the long upper part only counts, this version
splits the tape in two:

* L, the low part: chunk 0 (cells, n0) and the concrete chunks up to the topmost irregular chunk.  It is run
  exactly as in accel2.py (bulk of its normal prefix, simulated sweeps on a window, rlsim); it is small.
* U, the upper part: normal digits only, kept *lazily*.  Digits are indexed from the top (j = 0 is the highest
  digit), K = len(U), V the value of the U digits (lowest digit of U = lowest bits), E the number of U overflows.
  Digit j has the value (V >> 2(K-1-j)) & 3 and the timer

        N_j = A_j - 4^j E - floor(V / 4^(K-j))

  with a constant A_j.  Between overflows digit j wraps each time V crosses a multiple of 4^(K-j) (that is the
  floor term) and the overflow wraps every digit once (V: 4^K - 1 -> 0, E + 1).  Adding a new lowest digit
  (V -> 4V + d) or removing the lowest one (V -> V >> 2) leaves floor(V / 4^(K-j)) unchanged for the others, so
  A_j never has to be touched while the digit stays in U.  The time at which block j runs out, measured as
  X = E + V/4^K, is the constant key_j = (4(A_j - 2) + 3) / 4^(j+1) (or (4(A_j - 1) + 1) / 4^(j+1) when N_j = 1),
  kept in a heap.
* steps: the wraps of digit j cost 8 (N_j - 2) + 10 = P(N_j) - P(N_j - 1) with P(x) = 4x^2 - 2x, so w wraps from
  the timer M (its value when the digit entered U) cost P(M) - P(M - w) = 8Mw - 4w^2 - 2w.  The run keeps S, the
  steps without the wraps still pending in U; that cost is added when a digit leaves U, and the exact step count
  S + sum_U (8 M_j w_j - 4 w_j^2 - 2 w_j) is computed only when it is printed.

A bulk of t sweeps in U-mode (L is just chunk 0) is then O(1) big-integer operations: V += t, n0 += t, S += the n0
part of the step count.  The overflow (every digit 3, end 01) is closed form as in accel2.py (6 n0 + 6 sum n_i +
10k + 15 steps), with sum n_i read off sum A_j.  A run-out or a carry into the irregular part moves the lowest few
U digits into L (O(depth)), and after each L event the normal chunks above L's topmost irregular chunk move back.

usage: python3 accel3.py run 1eX [checkpoint]    run to 10^X steps
       python3 accel3.py compare 1eX              compare with accel2.Run at every non-bulk sweep (tape, steps, sweeps)
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
import accel2  # noqa: E402

M = accel.M
SEP, R, C = accel.S, accel.R, accel.C
STATE_C = accel.STATE_C
GUARD = 2


class Halt(Exception):
    pass


def wrapcost(M, w):
    """steps of w wraps of a digit whose timer was M: sum of 8 (x - 2) + 10 for x = M, M-1, ..., M-w+1"""
    return 8 * M * w - 4 * w * w - 2 * w


class Key:
    """the rational num / 4^(j+1)"""
    __slots__ = ('num', 'j')

    def __init__(self, num, j):
        self.num, self.j = num, j

    def __lt__(a, b):
        if a.j <= b.j:
            return (a.num << (2 * (b.j - a.j))) < b.num
        return a.num < (b.num << (2 * (a.j - b.j)))


def normal(ch):
    sep, n = ch
    return n is not None and sep in R and n >= 1


class Run3:
    def __init__(self):
        tok, steps = accel.first()
        self.S = steps
        self.sweeps = 0
        self.L = accel2.rechunk(tok, True)      # ends with the end chunk (cells, None) while U is empty
        if self.L[-1][1] is not None:
            self.L.append(('', None))
        self.end = None                          # the end cells while U is not empty
        self.U = []                              # [A_j, id]
        self.E = 0
        self.V = 0
        self.sumA = 0
        self.heap = []
        self.nid = 0
        self.nbulk = self.nlbulk = self.nsweep = self.nover = self.npop = self.npush = 0
        self.normalize()

    @classmethod
    def from_chunks(cls, chunks, steps=0):
        """start at a sweep start (head at the left end in C) given as chunks, e.g. [('', 2), ('0', 4), ('01', None)]"""
        r = cls.__new__(cls)
        r.S, r.sweeps = steps, 0
        r.L = list(chunks)
        r.end, r.U, r.E, r.V, r.sumA, r.heap, r.nid = None, [], 0, 0, 0, [], 0
        r.nbulk = r.nlbulk = r.nsweep = r.nover = r.npop = r.npush = 0
        r.normalize()
        return r

    # ------------------------------------------------------------------ U, the lazy part
    def N_of(self, j):
        return self.U[j][0] - (self.E << (2 * j)) - (self.V >> (2 * (len(self.U) - j)))

    def push_low(self, sep, n):
        d = R[sep]
        N = n + C[d]
        j = len(self.U)
        if j == 0:
            assert self.L[-1][1] is None
            self.end = self.L.pop()[0]
        p = self.V                                # floor(V' / 4^(K'-j)) with V' = 4V + d, K' = j + 1
        self.V = 4 * self.V + d
        A = N + (self.E << (2 * j)) + p
        self.nid += 1
        self.U.append([A, self.nid, N])
        self.sumA += A
        num = 4 * (A - 2) + 3 if N >= 2 else 4 * (A - 1) + 1
        heapq.heappush(self.heap, (Key(num, j), self.nid, j))
        self.npush += 1

    def pop_low(self):
        j = len(self.U) - 1
        N = self.N_of(j)
        d = self.V & 3
        n = N - C[d]
        assert n >= 1, (j, N, d)
        A, _, M = self.U.pop()
        self.sumA -= A
        self.S += wrapcost(M, M - N)
        self.V >>= 2
        self.L.append((SEP[d], n))
        if not self.U:
            self.L.append((self.end, None))
            self.end = None
        self.npop += 1

    def minkey(self):
        h, U = self.heap, self.U
        if len(h) > 3 * len(U) + 1000:
            self.heap = h = [e for e in h if e[2] < len(U) and U[e[2]][1] == e[1]]
            heapq.heapify(h)
        while h:
            key, i, j = h[0]
            if j < len(U) and U[j][1] == i:
                return key
            heapq.heappop(h)
        return None

    def u_mode(self):
        return len(self.L) == 1 and self.L[0][0] == '' and self.U

    def u_step(self):
        K = len(self.U)
        V, E = self.V, self.E
        t_over = (1 << (2 * K)) - 1 - V
        t = t_over
        m = self.minkey()
        jrun = None
        if m is not None and m.num < ((E + 1) << (2 * (m.j + 1))):     # runs out in this epoch
            Vb = (m.num << (2 * (K - m.j - 1))) - (E << (2 * K))
            assert Vb > V, 'run-out key in the past'
            if Vb - 1 - V < t:
                t = Vb - 1 - V
                jrun = m.j
        if t > 0:
            n0 = self.L[0][1]
            self.S += 8 * (t * n0 + t * (t - 1) // 2) + 6 * t
            self.L[0] = ('', n0 + t)
            self.V = V + t
            self.sweeps += t
            self.nbulk += 1
            return 'B'
        if jrun is not None:
            # the next sweep makes block jrun run out: move the digits up to it (and guards) into L
            for _ in range(min(K, K - jrun + GUARD)):
                self.pop_low()
            return None
        if self.end == '01':
            self.overflow()
            return 'F'
        while self.U:
            self.pop_low()
        return None

    def overflow(self):
        K = len(self.U)
        n0 = self.L[0][1]
        sumN = self.sumA - (self.E + 1) * (((1 << (2 * K)) - 1) // 3) + K
        sumn = sumN - 2 * K
        self.S += 6 * n0 + 15 - 2 * sumn
        self.V = 0
        self.E += 1
        self.L[0] = ('1010', n0)
        self.sweeps += 1
        self.nover += 1

    # ------------------------------------------------------------------ L, the concrete part (as accel2.py)
    def l_prefix(self):
        L = self.L
        d, N = [], []
        if L[0][0] == '':
            for sep, n in L[1:]:
                if n is None or sep not in R or n < 1:
                    break
                di = R[sep]
                d.append(di)
                N.append(n + C[di])
        V = 0
        for di in reversed(d):
            V = 4 * V + di
        return d, N, V

    def l_step(self):
        L = self.L
        d, N, V = self.l_prefix()
        ok0 = L[0][0] == ''
        k = len(d)
        if ok0:
            t = 4 ** k - 1 - V
            for i in range(k):
                v = accel2_vb(V, i, N[i])
                t = min(t, v - V - 1)
            if t > 0:
                self.l_bulk(d, N, V, t)
                return 'B'
        self.l_sweep(d, ok0)
        return 'F'

    def l_bulk(self, d, N, V, t):
        L = self.L
        k = len(d)
        n0 = L[0][1]
        steps = 8 * (t * n0 + t * (t - 1) // 2) + 6 * t
        V2 = V + t
        for i in range(k):
            w = (V2 >> (2 * (i + 1))) - (V >> (2 * (i + 1)))
            if w:
                Ni = N[i]
                steps += w * (8 * (Ni - 2) + 10) - 8 * w * (w - 1) // 2
                N[i] = Ni - w
        for i in range(k):
            di = (V2 >> (2 * i)) & 3
            n = N[i] - C[di]
            assert n > 0
            L[i + 1] = (SEP[di], n)
        L[0] = ('', n0 + t)
        self.S += steps
        self.sweeps += t
        self.nlbulk += 1

    def ensure(self, e):
        """L has chunks 0..e (or ends with the end chunk)"""
        while len(self.L) <= e + 1 and self.U:
            self.pop_low()

    def l_sweep(self, d, ok0):
        k = len(d)
        j = None
        if ok0:
            for i in range(k):
                if d[i] < 3:
                    j = i
                    break
        e = (j + 1 if j is not None else (k + 1 if ok0 else 0)) + 2
        while True:
            self.ensure(e)
            ch = self.L
            at_end = ch[-1][1] is None
            whole = at_end and e >= len(ch) - 1
            e = min(e, len(ch) - 1)
            toks = accel2.materialize(ch[:e + 1])
            last = len(accel2.materialize(ch[e:e + 1]))
            s = Sim(M, head_first(toks), STATE_C)
            s.dir, s.steps = -1, self.S
            r, dmin = accel2.run_track(s, self.S)
            if r == 'halt':     # S leaves out the wraps pending in U
                raise Halt(s.steps + self.pending())
            if whole or dmin > last + 1:
                break
            e = 2 * e + 2
        if s.h < 0:
            s.tok.insert(0, ['0', 1])
        new = accel2.rechunk(canon(s.tok, minrun=1), whole)
        self.S = s.steps
        self.sweeps += 1
        self.nsweep += 1
        ch[:e + 1] = new
        if whole and ch[-1][1] is not None:
            ch.append(('', None))

    def normalize(self):
        """move the normal chunks above L's topmost irregular chunk into U"""
        L = self.L
        top = len(L) - 1
        if L[top][1] is None:
            if self.U:
                raise AssertionError('end chunk in L while U is not empty')
            top -= 1
            if top < 1 or not normal(L[top]):
                return
        r = top
        while r >= 1 and normal(L[r]):
            r -= 1
        # chunks r+1..top are normal digits; push from the top down (the first push takes the end chunk out)
        for i in range(top, r, -1):
            sep, n = L[i]
            self.push_low(sep, n)
            L.pop()

    def step(self):
        if self.u_mode():
            r = self.u_step()
            if r is not None:
                return r
        r = self.l_step()
        self.normalize()
        return r

    # ------------------------------------------------------------------ reading out
    def steps(self):
        return self.S + self.pending()

    def pending(self):
        return sum(wrapcost(u[2], u[2] - self.N_of(j)) for j, u in enumerate(self.U))

    def chunks(self):
        out = list(self.L)
        if self.U:
            K = len(self.U)
            for j in range(K - 1, -1, -1):
                dj = (self.V >> (2 * (K - 1 - j))) & 3
                out.append((SEP[dj], self.N_of(j) - C[dj]))
            out.append((self.end, None))
        return out

    def ndigits(self):
        return len(self.L) + len(self.U) - 2


def accel2_vb(V, i, Ni):
    sh, q = 2 * (i + 1), 1 << (2 * i)
    hi = V >> sh
    if Ni >= 3:
        return (hi + (Ni - 2)) << sh | 3 * q
    if Ni == 2:
        return hi << sh | 3 * q
    return hi << sh | q


def compare(maxsteps, a=None, b=None, quiet=False):
    if a is None:
        a, b = accel2.Run(), Run3()
    n = 0
    while a.steps < maxsteps:
        while a.step() != 'F':
            pass
        while b.step() != 'F':
            pass
        ca = canon(accel2.norm_tok(a.tokens()), minrun=1)
        cb = canon(accel2.norm_tok(accel2.materialize(b.chunks())), minrun=1)
        bs = b.steps()
        assert (a.steps, a.sweeps) == (bs, b.sweeps), (n, a.steps, bs, a.sweeps, b.sweeps)
        assert ca == cb, (n, ca[:30], cb[:30])
        n += 1
    if quiet:
        return n
    print('ok: %d non-bulk sweeps agree with accel2.py (tape, step and sweep counts) up to 10^%d steps; '
          'pops %d pushes %d' % (n, len(str(maxsteps)) - 1, b.npop, b.npush))


MAXRSS = int(os.environ.get('MAXRSS_MB', '6000'))


def rss_mb():
    with open('/proc/self/status') as f:
        for line in f:
            if line.startswith('VmRSS:'):
                return int(line.split()[1]) // 1024
    return 0


def main_run(maxexp, ckpt=None, every=1800):
    r = None
    if ckpt and os.path.exists(ckpt):
        r = pickle.load(open(ckpt, 'rb'))
        print('resumed: S has %d digits, %d digits in the counter' % (len(str(r.S)), r.ndigits()), flush=True)
    if r is None:
        r = Run3()
    cat = collections.Counter()
    t0 = tlast = time.time()
    st = r.steps()
    mark = len(str(st))
    nexact = 0
    while True:
        if r.step() == 'F':
            for sep, n in r.L:
                if sep not in R and sep != '':
                    cat[sep] += 1
        nexact += 1
        if r.S >= 10 ** mark and nexact >= 64:
            nexact = 0
            st = r.steps()
            if st >= 10 ** mark:
                mark = len(str(st))
                print('steps >= 1e%d  sweeps 1e%d  digits %d  bulks %d+%d  simulated sweeps %d  overflows %d  '
                      'pops %d  %.0fs' % (mark - 1, len(str(r.sweeps)) - 1, r.ndigits(), r.nbulk, r.nlbulk,
                                          r.nsweep, r.nover, r.npop, time.time() - t0), flush=True)
                if mark - 1 >= maxexp:
                    break
                if mark < 300:
                    mark = (mark // 10 + 1) * 10
                elif mark < 10000:
                    mark = (mark // 100 + 1) * 100
                else:
                    mark = (mark // 1000 + 1) * 1000
        if ckpt and time.time() - tlast > every:
            pickle.dump(r, open(ckpt + '.tmp', 'wb'))
            os.replace(ckpt + '.tmp', ckpt)
            tlast = time.time()
            if rss_mb() > MAXRSS:
                print('checkpoint written; exiting to release memory (resident %d MB)' % rss_mb(), flush=True)
                sys.exit(3)
    if ckpt:
        pickle.dump(r, open(ckpt + '.tmp', 'wb'))
        os.replace(ckpt + '.tmp', ckpt)
    print('no halt; step count has %d digits (sweeps %d digits, counter %d digits)' % (
        len(str(r.steps())), len(str(r.sweeps)), r.ndigits()))
    print('irregular cell patterns in L after simulated sweeps (count, cells):')
    for k, v in cat.most_common(40):
        print(' ', v, k)


def randcheck(T, X, seed=7):
    """random counter tapes as in perturb.py (2..7 digits, block i up to 4^(i+2)): accel3 against accel2 at every
    non-bulk sweep up to 10^X steps, and the same halting step"""
    import random
    rnd = random.Random(seed)
    nh = 0
    for _ in range(T):
        k = rnd.randint(2, 7)
        ch = [('', rnd.randint(2, 50))] + [(SEP[rnd.randrange(4)], rnd.randint(1, 4 ** (i + 2))) for i in range(k)]
        ch.append(('01', None))
        a = accel2.Run.__new__(accel2.Run)
        a.steps, a.sweeps, a.nfull, a.nsweep, a.nbulk, a.nover = 0, 0, 0, 0, 0, 0
        a.chunks = list(ch)
        a.full_recompute()
        b = Run3.from_chunks(ch)
        ha = hb = None
        try:
            compare(10 ** X, a, b, quiet=True)
        except accel2.Halt as h:
            ha = h.args[0]
            try:
                while True:
                    b.step()
            except Halt as h2:
                hb = h2.args[0]
        except Halt as h:
            hb = h.args[0]
        assert ha == hb, (ch, ha, hb)
        nh += ha is not None
    print('ok: %d random counter tapes, accel3 = accel2 at every non-bulk sweep to 10^%d steps; %d halt (same step)'
          % (T, X, nh))


def halttest():
    """the two counter tapes of lean/Perturbed.lean halt at the proved step counts"""
    for chunks, want in [([('', 2), ('0', 4), ('01', None)], 309457),
                         ([('', 43), ('0101', 4), ('0101', 4), ('01', None)], 4905443)]:
        r = Run3.from_chunks(chunks)
        try:
            while True:
                r.step()
        except Halt as h:
            assert h.args[0] == want, (chunks, h.args[0], want)
            print('ok: %s halts at step %d' % (chunks, h.args[0]))


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'randcheck':
        randcheck(int(sys.argv[2]), int(sys.argv[3]))
        sys.exit()
    if cmd == 'halttest':
        halttest()
        sys.exit()
    x = int(sys.argv[2].split('e')[1])
    if cmd == 'compare':
        compare(10 ** x)
    else:
        try:
            main_run(x, sys.argv[3] if len(sys.argv) > 3 else None)
        except Halt as h:
            print('HALT at step', h.args[0])
