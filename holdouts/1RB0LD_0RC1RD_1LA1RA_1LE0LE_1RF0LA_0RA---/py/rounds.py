"""Generic round maps "counter block + tail word", shared by several G01 machines (used by their py/roundmap.py).

A machine of this kind is sampled when the head is in state S at the LEFT end reading a symbol x; the tape then is

    S> PRE (UNIT)^m T 0^inf           (T: a short tail word, the rest of the tape)

and one round (to the next such event) sends m to (NUM*m + c)/Q and T to T', where c, T' and the step count
(a quadratic polynomial in (m - r)/Q) depend only on r = m mod Q and T once m >= Q*K0.  `RoundMap.rep` computes the
round from four representatives m0 = Q*j + r (j = K0..K0+3) and refuses (`INCONS`) if they disagree, so a round with
a huge m costs as much as one with m ~ Q*K0.  `check` compares the orbit with a direct C run (tools/c/tmrun.c).
"""
import os
import re
import subprocess
import tempfile

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')


def parse_machine(m):
    t = []
    for g in m.split('_'):
        row = []
        for i in (0, 3):
            s = g[i:i + 3]
            row.append(None if s[2] == '-' else (int(s[0]), 1 if s[1] == 'R' else -1, ord(s[2]) - 65))
        t.append(row)
    return t


class RoundMap:
    def __init__(self, machine, state, read, pre, unit, Q, NUM, K0=10, SCALE=4):
        self.machine = machine
        self.T = parse_machine(machine)
        self.st = ord(state) - 65
        self.state = state
        self.read = read
        self.pre, self.unit, self.Q, self.NUM, self.K0, self.SCALE = pre, unit, Q, NUM, K0, SCALE
        self.rx = re.compile(re.escape(pre) + '((?:%s)*)' % re.escape(unit))
        self.cache = {}

    def parse(self, right):
        """The cells from the head to the right end -> (m, T), or None."""
        x = right.rstrip('0')
        mm = self.rx.match(x)
        if not mm:
            return None
        return len(mm.group(1)) // len(self.unit), x[mm.end():]

    _proc = None

    def ev(self, m, tail, cap=10 ** 9):
        """As `ev_py`, by the C helper ../c/evrun.c (compiled once into a temporary directory)."""
        if self._proc is None:
            d = tempfile.mkdtemp()
            exe = os.path.join(d, 'evrun')
            subprocess.check_call(['gcc', '-O2', '-o', exe, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                                          '..', 'c', 'evrun.c')])
            self._proc = subprocess.Popen([exe, self.machine, self.state, str(self.read), str(cap)],
                                          stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
        self._proc.stdin.write(self.pre + self.unit * m + tail + '\n')
        self._proc.stdin.flush()
        f = self._proc.stdout.readline().split()
        if f[0] == 'HALT':
            return ('HALT', int(f[1]))
        if f[0] == 'CAP':
            return ('?',)
        x = f[1] if len(f) > 1 else ''
        p = self.parse(x)
        if p is None:
            return ('BAD', x, int(f[0]))
        return (p[0], p[1], int(f[0]))

    def ev_py(self, m, tail, cap=10 ** 8):
        """Direct run from the event (m, tail) to the next one: (m', T', steps) or ('HALT', steps) / ('?',) /
        ('BAD', tape, steps) when the next event does not have the form."""
        R = self.pre + self.unit * m + tail
        pad = 4 * len(R) + 400
        tape = bytearray(pad) + bytearray(int(c) for c in R) + bytearray(pad)
        h = lo = pad
        hi = pad + len(R) - 1
        st, k, n, TT = self.st, 0, len(tape), self.T
        while k < cap:
            tr = TT[st][tape[h]]
            if tr is None:
                return ('HALT', k + 1)
            w, d, st = tr
            tape[h] = w
            h += d
            k += 1
            if h < lo:
                lo = h
            if h > hi:
                hi = h
            if h <= 0 or h >= n - 1:
                tape = bytearray(n) + tape + bytearray(n)
                h += n; lo += n; hi += n; n = len(tape)
            if st == self.st and h == lo and tape[h] == self.read:
                x = ''.join(map(str, tape[h:hi + 1]))
                p = self.parse(x)
                if p is None:
                    return ('BAD', x.rstrip('0'), k)
                return (p[0], p[1], k)
        return ('?',)

    def k0(self, tail):
        """The smallest j used for a tail: the representatives must be long compared with the tail."""
        return max(self.K0, (self.SCALE * len(tail)) // self.Q + 1)

    def rep(self, r, tail):
        key = (r, tail)
        if key in self.cache:
            return self.cache[key]
        pts = []
        k0 = self.k0(tail)
        for j in (k0, k0 + 1, k0 + 2, k0 + 3, 2 * k0 + 7):
            m0 = self.Q * j + r
            o = self.ev(m0, tail)
            if o[0] in ('HALT', '?', 'BAD'):
                self.cache[key] = (o[0], m0, o)
                return self.cache[key]
            pts.append((m0,) + o)
        Ts = {p[2] for p in pts}
        cs = {self.Q * p[1] - self.NUM * p[0] for p in pts}
        ss = [p[3] for p in pts]
        d1 = [ss[i + 1] - ss[i] for i in range(3)]
        d2 = [d1[i + 1] - d1[i] for i in range(2)]
        poly = (k0, ss[0], d1[0], d2[0])
        if len(Ts) != 1 or len(cs) != 1 or d2[0] != d2[1] or _poly(poly, 2 * k0 + 7) != ss[4]:
            self.cache[key] = ('INCONS', pts)
        else:
            self.cache[key] = ('ok', cs.pop(), Ts.pop(), poly)
        return self.cache[key]

    def rnd(self, m, tail):
        """One round; run directly while m is small compared with the tail (below the representatives)."""
        if m < self.Q * (2 * self.k0(tail) + 7):
            return self.ev(m, tail)
        r = m % self.Q
        res = self.rep(r, tail)
        if res[0] != 'ok':
            return res
        _, c, T2, poly = res
        assert (self.NUM * m + c) % self.Q == 0
        return ((self.NUM * m + c) // self.Q, T2, _poly(poly, (m - r) // self.Q))

    def orbit(self, m, tail, t, N):
        """Events from (m, tail) at step t: yields (round, step, m, T); a final (round, 'HALT'/..., result, T)."""
        yield 0, t, m, tail
        for i in range(N):
            o = self.rnd(m, tail)
            if not isinstance(o[0], int):
                yield i + 1, o[0], o, tail
                return
            m, tail, s = o
            t += s
            yield i + 1, t, m, tail


def _poly(poly, k):
    k0, s0, d1, d2 = poly
    t = k - k0
    return s0 + t * d1 + t * (t - 1) // 2 * d2


def compress(s):
    out, i = [], 0
    while i < len(s):
        best = None
        for L in (1, 2, 3, 4, 5):
            w = s[i:i + L]
            if len(w) < L:
                break
            k = 1
            while s[i + k * L:i + (k + 1) * L] == w:
                k += 1
            if k >= 2 and k * L > L + 1 and (best is None or k * L > best[1] * len(best[0])):
                best = (w, k)
        if best:
            w, k = best
            out.append(('(%s)^%d' % (w, k)) if len(w) > 1 else '%s^%d' % (w, k))
            i += k * len(w)
        else:
            out.append(s[i])
            i += 1
    return ' '.join(out)


def _expand(fields):
    out, head = [], None
    for f in fields:
        if '>' in f:
            head = len(out)
            f = f.split('>')[1]
            if not f:
                continue
        if '^' in f:
            w, e = f.split('^')
            out.append(w.strip('()') * int(e))
        else:
            out.append(f)
    return ''.join(out), head


def check(rm, start, steps, skip=0):
    """Direct C run; every event (state at the left end reading `read`) after the first `skip` ones must be the
    orbit's next one from `start` = (m, tail, step)."""
    d = tempfile.mkdtemp()
    exe = os.path.join(d, 'tmrun')
    subprocess.check_call(['gcc', '-O2', '-o', exe, os.path.join(ROOT, 'tools', 'c', 'tmrun.c')])
    p = subprocess.Popen([exe, rm.machine, str(int(float(steps))), 'at', rm.state, 'L', '10000000'],
                         stdout=subprocess.PIPE, text=True)
    pred = rm.orbit(start[0], start[1], start[2], 10 ** 7)
    n = bad = seen = 0
    for line in p.stdout:
        f = line.split()
        if not f[0].isdigit():
            print(line.strip())
            continue
        cells, h = _expand(f[1:])
        if int(cells[h]) != rm.read:
            continue
        seen += 1
        if seen <= skip:
            continue
        got = rm.parse(cells[h:])
        i, t, m, T = next(pred)
        n += 1
        if got is None or (int(f[0]), got[0], got[1]) != (t, m, T):
            bad += 1
            print('DIFFER', f[0], got, (t, m, T))
    print('events compared: %d, differing: %d' % (n, bad))
    return bad == 0


def iterate(rm, start, N):
    last, ret, maxlen = None, 0, 0
    for i, t, m, T in rm.orbit(start[0], start[1], start[2], N):
        if not isinstance(t, int):
            print('STOP in round', i, m, T)
            return
        last = (i, t, m)
        maxlen = max(maxlen, len(T))
        ret += T == start[1]
    i, t, m = last
    dig = lambda x: int(x.bit_length() * 0.30103)
    print('%d rounds without a halt; last event at step ~10^%d with m ~10^%d; tail back to the start tail in %d '
          'rounds; longest tail %d cells; %d (residue, tail) pairs used' % (i, dig(t), dig(m), ret, maxlen,
                                                                             len(rm.cache)))


def bfs(rm, tail0, N, maxlen):
    from collections import deque
    seen, q, bad, n = {tail0}, deque([tail0]), [], 0
    while q and n < N:
        T = q.popleft()
        n += 1
        for r in range(rm.Q):
            res = rm.rep(r, T)
            if res[0] != 'ok':
                bad.append((r, T, res[0]))
                continue
            T2 = res[2]
            if T2 not in seen and len(T2) <= maxlen:
                seen.add(T2)
                q.append(T2)
    print('tails expanded %d (x%d residues), seen %d, rounds that do not return to the form: %d' % (n, rm.Q, len(seen),
                                                                                                 len(bad)))
    for b in bad[:20]:
        print('  ', b)
    return bad
