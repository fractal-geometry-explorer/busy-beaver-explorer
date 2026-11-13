"""wsim: exact accelerated simulator for 2-symbol TMs whose tape is runs of repeated words.

Tape: two stacks of items [word, count] (word: str of '0'/'1').  L: bottom..top, top nearest the head, words in
natural order.  R: bottom..top, top nearest the head, words in natural order (its first char is next to the head).
Head sits on a cell boundary, in state q, facing f (+1: reads R top's first cell, -1: reads L top's last cell).
Macro steps:
  * cross: the faced item (w, n) with a context u of c<=3 cells behind the head: if one copy is crossed coming out
    the far side in the same state with u restored, all n copies are crossed at once (an exact shift rule).
  * one copy crossed, any exit state (exact).
  * single cell step.
Sample points (left turns) canonicalise the tape and look for a period of P samples over which the tape's shape is
the same and its counts change by constant amounts; then m periods are applied at once (counts + m*delta, steps by
the exact quadratic sum).  Exactness of a jump relies on the period's macro steps depending on the counts only
through 'count >= 1'; counts are kept well above their minimum (MARGIN), and the whole thing is validated against
direct simulation.
"""
import sys
from collections import defaultdict

def parse(m):
    T = {}
    for i, g in enumerate(m.split('_')):
        for r in range(2):
            t = g[3*r:3*r+3]
            T[(i, r)] = None if t[2] == '-' or not ('A' <= t[2] <= 'Z') else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return T

def primitive(w):
    n = len(w)
    for p in range(1, n // 2 + 1):
        if n % p == 0 and w[:p] * (n // p) == w:
            return w[:p], n // p
    return w, 1

class Halt(Exception):
    pass

class WSim:
    MAXCTX = 3
    MARGIN = 6
    MAXP = 400       # max period (in samples) searched
    MINREP = 2       # copies needed to compress a raw string
    MAXW = 600       # max word length for repeat detection
    SMALL = 64       # atomic items of at most this many cells are re-expanded at samples

    def __init__(self, machine, trace=None):
        self.m = machine
        self.T = parse(machine)
        self.L = []
        self.R = []
        self.q = 0
        self.f = 1
        self.steps = 0
        self.cache = {}
        self.hist = []          # per sample: (sig, counts, steps)
        self.sigpos = defaultdict(list)
        self.nsamples = 0
        self.jumps = 0
        self.jumped_steps = 0
        self.trace = trace      # callback(event, sim) for halting-relevant events
        self.lastdir = 1
        self.halted = False
        self.watch = None
        self.log = None
        self.nsamp_since = 0

    # ---------- basic stack ops
    @staticmethod
    def push(st, w, n=1):
        if not w or n == 0:
            return
        if st and st[-1][0] == w:
            st[-1][1] += n
        elif n == 1 and st and st[-1][1] == 1 and len(st[-1][0]) + len(w) <= 4000:
            # raw concat (L stack: natural order; R stack handled by caller with reversed concat)
            st[-1][0] = st[-1][0] + w
        else:
            st.append([w, n])

    def pushL(self, w, n=1):
        if not w or n == 0: return
        L = self.L
        if L and L[-1][0] == w:
            L[-1][1] += n
        elif n == 1 and L and L[-1][1] == 1:
            L[-1][0] = L[-1][0] + w
        else:
            L.append([w, n])

    def pushR(self, w, n=1):
        if not w or n == 0: return
        R = self.R
        if R and R[-1][0] == w:
            R[-1][1] += n
        elif n == 1 and R and R[-1][1] == 1:
            R[-1][0] = w + R[-1][0]
        else:
            R.append([w, n])

    def popcellR(self):
        R = self.R
        if not R:
            return '0'
        it = R[-1]
        w, n = it
        if n > 1:
            it[1] -= 1
            if len(w) > 1:
                R.append([w[1:], 1])
            return w[0]
        if len(w) > 1:
            it[0] = w[1:]
        else:
            R.pop()
        return w[0]

    def popcellL(self):
        L = self.L
        if not L:
            return '0'
        it = L[-1]
        w, n = it
        if n > 1:
            it[1] -= 1
            if len(w) > 1:
                L.append([w[:-1], 1])
            return w[-1]
        if len(w) > 1:
            it[0] = w[:-1]
        else:
            L.pop()
        return w[-1]

    def peekL(self, c):
        """last c cells of L (fewer if L is short: blank cells beyond are '0', we pad)."""
        if c == 0:
            return ''
        out = []
        need = c
        for w, n in reversed(self.L):
            # take from the end
            s = w * min(n, (need // len(w)) + 1)
            take = s[-need:] if need <= len(s) else s
            out.append(take)
            need -= len(take)
            if need <= 0:
                break
        r = ''.join(reversed(out))
        return '0' * (c - len(r)) + r

    def peekR(self, c):
        if c == 0:
            return ''
        out = []
        need = c
        for w, n in reversed(self.R):
            s = w * min(n, (need // len(w)) + 1)
            take = s[:need]
            out.append(take)
            need -= len(take)
            if need <= 0:
                break
        r = ''.join(out)
        return r + '0' * (c - len(r))

    def dropL(self, c):
        for _ in range(c):
            self.popcellL()

    def dropR(self, c):
        for _ in range(c):
            self.popcellR()

    # ---------- local simulation of one copy
    def local(self, q, s, pos, f):
        """simulate on string s, head facing cell pos (f is only for bookkeeping); returns (exit_side, state, s', steps) or None"""
        T = self.T
        c = list(s)
        n = len(c)
        steps = 0
        while 0 <= pos < n:
            tr = T[(q, int(c[pos]))]
            if tr is None:
                return None
            w, d, q2 = tr
            c[pos] = '1' if w else '0'
            pos += d
            q = q2
            steps += 1
            if steps > 200000:
                return None
        return (1 if pos >= n else -1, q, ''.join(c), steps)

    def try_rule(self, q, f, w, u):
        key = (q, f, w, u)
        r = self.cache.get(key)
        if r is not None:
            return r
        if f == 1:
            res = self.local(q, u + w, len(u), 1)
        else:
            res = self.local(q, w + u, len(w) - 1, -1)
        self.cache[key] = res if res is not None else False
        return self.cache[key]

    # ---------- one macro step
    def macro(self):
        q, f = self.q, self.f
        st = self.R if f == 1 else self.L
        if st:
            w, n = st[-1]
            # full-run crossing with context
            for c in range(self.MAXCTX + 1):
                u = self.peekL(c) if f == 1 else self.peekR(c)
                r = self.try_rule(q, f, w, u)
                if not r:
                    continue
                side, q2, s2, k = r
                if side != f:
                    continue
                if q2 == q and ((f == 1 and s2.endswith(u) and s2[len(s2)-c:] == u) or (f == -1 and s2.startswith(u))):
                    # shift rule over all n copies
                    st.pop()
                    if f == 1:
                        self.dropL(c)
                        y = s2[:len(w)]
                        self.pushL(y, n)
                        self.pushL(u)
                    else:
                        self.dropR(c)
                        y = s2[c:]
                        self.pushR(y, n)
                        self.pushR(u)
                    self.steps += k * n
                    return
                # single copy
                if n > 1:
                    st[-1][1] -= 1
                else:
                    st.pop()
                if f == 1:
                    self.dropL(c)
                    self.pushL(s2)
                else:
                    self.dropR(c)
                    self.pushR(s2)
                self.q = q2
                self.steps += k
                return
        # single cell step
        cell = self.popcellR() if f == 1 else self.popcellL()
        tr = self.T[(q, int(cell))]
        if tr is None:
            # put back and halt
            if f == 1: self.pushR(cell)
            else: self.pushL(cell)
            self.halted = True
            raise Halt()
        wb, d, q2 = tr
        wc = '1' if wb else '0'
        if d == 1:
            self.pushL(wc)
        else:
            self.pushR(wc)
        if self.watch is not None and q2 == self.watch[0]:
            self.watch_hit(q2, d)
        self.lastdir = self.f
        self.f = d
        self.q = q2
        self.steps += 1

    def watch_hit(self, q2, d):
        ctx = self.peekL(8) + '|' + self.peekR(8) if d == 1 else self.peekL(8) + '|' + self.peekR(8)
        self.watch[1][(d, ctx)] = self.watch[1].get((d, ctx), 0) + 1

    # ---------- canonical form
    def items(self):
        """the tape as a list of items left to right; returns (items, headindex) where head is before items[headindex]"""
        its = [list(x) for x in self.L] + [list(x) for x in reversed(self.R)]
        return its, len(self.L)

    def compress_raw(self, s):
        """split raw string s into items: repeats of MINREP+ copies become atomic (greedy, leftmost)"""
        n = len(s)
        out = []
        buf = []
        i = 0
        MR = self.MINREP
        while i < n:
            best = None
            maxp = min(self.MAXW, (n - i) // MR)
            for p in range(1, maxp + 1):
                if s[i + p] != s[i]:
                    continue
                w = s[i:i+p]
                if not s.startswith(w, i + p):
                    continue
                r = 2
                while s.startswith(w, i + r * p):
                    r += 1
                if r >= MR:
                    gain = (r - 1) * p
                    if best is None or gain > best[2]:
                        best = (p, r, gain)
            if best is None:
                buf.append(s[i]); i += 1
                continue
            p, r, g = best
            if buf:
                out.append([''.join(buf), 1]); buf = []
            w, k = primitive(s[i:i+p])
            out.append([w, r * k])
            i += p * r
        if buf:
            out.append([''.join(buf), 1])
        return out

    _lyn = {}

    def lyndon(self, w):
        r = self._lyn.get(w)
        if r is None:
            best = w; o = 0
            for i in range(1, len(w)):
                c = w[i:] + w[:i]
                if c < best:
                    best = c; o = i
            r = (best, o)
            self._lyn[w] = r
        return r

    def maxreps(self, st):
        """non-overlapping maximal repetitions of st, chosen greedily by coverage: list of (a, end, p)"""
        N = len(st)
        cands = []
        for p in range(1, min(self.MAXW, N // 2) + 1):
            i = 0
            # find maximal intervals where st[i]==st[i+p]
            while i + p < N:
                if st[i] != st[i + p]:
                    i += 1; continue
                a = i
                while i + p < N and st[i] == st[i + p]:
                    i += 1
                L = i - a + p   # covers [a, a+L)
                if L >= self.MINREP * p and L >= 4:
                    cands.append((L - p, a, a + L, p))   # gain
        cands.sort(key=lambda c: (-c[0], c[1], c[3]))
        used = []
        for g, a, b, p in cands:
            ok = True
            for (a2, b2, p2) in used:
                if a < b2 and a2 < b:
                    ok = False; break
            if ok:
                used.append((a, b, p))
        used.sort()
        return used

    _sic = {}

    def str_items(self, st):
        r = self._sic.get(st)
        if r is None:
            r = self._str_items(st)
            if len(self._sic) > 200000:
                self._sic.clear()
            self._sic[st] = r
        return [list(x) for x in r]

    def _str_items(self, st):
        """canonical items of a raw string"""
        out = []
        pos = 0
        for a, b, p in self.maxreps(st):
            w = st[a:a+p]
            pw, _ = primitive(w)
            p = len(pw)
            lw, o = self.lyndon(pw)
            # first start of the Lyndon rotation at or after a: positions a + ((o) mod p) ... w starts at a
            f = a + o if o > 0 else a
            m = (b - f) // p
            if m < 2:
                f = a; lw = pw; m = (b - a) // p
            if pos < f:
                self.raw_split(st[pos:f], out)
            out.append([lw, m])
            pos = f + m * p
        if pos < len(st):
            self.raw_split(st[pos:], out)
        return out

    @staticmethod
    def raw_split(r, out):
        """raw piece: runs of one symbol of length >= 3 become items"""
        i = 0; n = len(r); buf = ''
        while i < n:
            j = i
            while j < n and r[j] == r[i]:
                j += 1
            if j - i >= 3:
                if buf: out.append([buf, 1]); buf = ''
                out.append([r[i], j - i])
            else:
                buf += r[i:j]
            i = j
        if buf: out.append([buf, 1])

    def canon(self):
        its, h = self.items()
        while h > 0 and set(its[0][0]) == {'0'}:
            its.pop(0); h -= 1
        while len(its) > h and set(its[-1][0]) == {'0'}:
            its.pop()
        seq = []
        for idx, (w, n) in enumerate(its):
            if idx == h:
                seq.append(['head'])
            if n >= 2 and n * len(w) > self.SMALL:
                pw, k = primitive(w)
                seq.append(['big', pw, n * k])
            else:
                if seq and seq[-1][0] == 'str':
                    seq[-1][1] += w * n
                else:
                    seq.append(['str', w * n])
        if h == len(its):
            seq.append(['head'])
        # re-cut every big item over its maximal run with the Lyndon rotation
        for i, e in enumerate(seq):
            if e[0] != 'big':
                continue
            w = e[1]; p = len(w); n = e[2]
            left = seq[i-1][1] if i > 0 and seq[i-1][0] == 'str' else ''
            right = seq[i+1][1] if i + 1 < len(seq) and seq[i+1][0] == 'str' else ''
            # x: longest suffix of left continuing the period backwards
            k = 0
            while k < len(left) and left[len(left)-1-k] == w[(p - 1 - k) % p]:
                k += 1
            x = k
            k = 0
            while k < len(right) and right[k] == w[k % p]:
                k += 1
            y = k
            lw, o = self.lyndon(w)
            # run = left[-x:] + w^n + right[:y]; positions relative to run start; w copies start at x (mod p)
            total = x + n * p + y
            f = (x + o) % p
            m = (total - f) // p
            pre = (left[len(left)-x:] + (w * 2))[:f] if f <= x + 2 * p else None
            # build prefix string of length f and suffix string
            def runchar(j):
                if j < x: return left[len(left)-x+j]
                j2 = j - x
                if j2 < n * p: return w[j2 % p]
                return right[j2 - n * p]
            prefix = ''.join(runchar(j) for j in range(f))
            send = f + m * p
            suffix = ''.join(runchar(j) for j in range(send, total))
            if i > 0 and seq[i-1][0] == 'str':
                seq[i-1][1] = left[:len(left)-x] + prefix
            else:
                e.append(prefix)   # extra prefix stored on the item
            e[1] = lw; e[2] = m
            if i + 1 < len(seq) and seq[i+1][0] == 'str':
                seq[i+1][1] = suffix + right[y:]
            else:
                e.append(suffix) if len(e) == 4 else e.extend(['', suffix])
        seq2 = []
        for e in seq:
            if e[0] == 'big' and len(e) > 3:
                pre, suf = e[3], (e[4] if len(e) > 4 else '')
                if pre: seq2.append(['str', pre])
                seq2.append(e[:3])
                if suf: seq2.append(['str', suf])
            else:
                seq2.append(e)
        seq = seq2
        items = []
        def add(w, n):
            if not w or n == 0:
                return
            if n == 1:
                if items and items[-1] is not None and items[-1][1] == 1:
                    items[-1][0] += w
                else:
                    items.append([w, 1])
            else:
                if items and items[-1] is not None and items[-1][0] == w and items[-1][1] >= 2:
                    items[-1][1] += n
                else:
                    items.append([w, n])
        for e in seq:
            if e[0] == 'head':
                items.append(None)
            elif e[0] == 'big':
                add(e[1], e[2])
            else:
                for w, n in self.str_items(e[1]):
                    add(w, n)
        h = items.index(None)
        self.L = items[:h]
        self.R = list(reversed(items[h+1:]))

    def signature(self):
        sig = (self.q, self.f,
               tuple((w, n == 1 and 1 or 0, (w if n == 1 else None)) for w, n in self.L),
               tuple((w, n == 1 and 1 or 0) for w, n in self.R))
        counts = [n for w, n in self.L if n >= 2] + [n for w, n in self.R if n >= 2]
        return sig, counts

    def wlens(self):
        return [len(w) for w, n in self.L if n >= 2] + [len(w) for w, n in self.R if n >= 2]

    def set_counts(self, counts):
        i = 0
        for it in self.L:
            if it[1] >= 2:
                it[1] = counts[i]; i += 1
        for it in self.R:
            if it[1] >= 2:
                it[1] = counts[i]; i += 1

    # ---------- sample + jump
    def sample(self):
        self.nsamp_since += 1
        self.canon()
        sig, counts = self.signature()
        idx = len(self.hist)
        self.hist.append((sig, counts, self.steps, self.wlens()))
        lst = self.sigpos[sig]
        lst.append(idx)
        if len(lst) > 6:
            del lst[0]
        if len(self.hist) > 20000:
            self.hist = [self.hist[-1]]
            self.sigpos = defaultdict(list)
            self.sigpos[sig].append(0)
            return False
        # look for period
        for j in reversed(lst[:-1]):
            P = idx - j
            if P > self.MAXP or j - P < 0:
                continue
            k0 = j - P
            if self.hist[k0][0] != sig:
                continue
            ok = True
            for t in range(P):
                if self.hist[k0 + t][0] != self.hist[j + t][0]:
                    ok = False; break
            if not ok:
                continue
            c0, c1, c2 = self.hist[k0][1], counts and self.hist[j][1], counts
            d1 = [b - a for a, b in zip(c0, c1)]
            d2 = [b - a for a, b in zip(c1, c2)]
            if d1 != d2 or not any(d2):
                continue
            s0, s1, s2 = self.hist[k0][2], self.hist[j][2], self.steps
            S1, S2 = s1 - s0, s2 - s1
            D = S2 - S1
            # number of periods: decreasing counts stay >= margin
            m = None
            wl = self.wlens()
            for t in range(P):
                cc = self.hist[j + t][1]
                dt = [y - x for x, y in zip(self.hist[k0 + t][1], cc)]
                wlt = self.hist[j + t][3]
                for x, dd, lw in zip(cc, dt, wlt):
                    if dd < 0:
                        floor_ = max(self.MARGIN, self.SMALL // lw + 2)
                        mm = (x - floor_ - 2 * (-dd)) // (-dd)
                        m = mm if m is None else min(m, mm)
            if m is None:
                m = 10 ** 6  # nothing decreasing: cap (caller limits by target)
            m = min(m, self.jumpcap())
            if m < 1:
                continue
            newc = [x + m * dd for x, dd in zip(counts, d2)]
            self.set_counts(newc)
            add = m * S2 + D * m * (m + 1) // 2
            self.steps += add
            self.jumps += 1
            if self.log is not None: self.log.append((self.steps, P, m, self.nsamp_since)); self.nsamp_since = 0
            self.jumped_steps += add
            # reset history (shapes after jump continue the same pattern, but keep it simple)
            self.hist = []
            self.sigpos = defaultdict(list)
            return True
        return False

    def jumpcap(self):
        return getattr(self, 'cap', 10 ** 18)

    def run(self, maxsteps, maxmacro=None, sample_every_turn=True):
        nm = 0
        try:
            while self.steps < maxsteps:
                pf = self.f
                self.macro()
                nm += 1
                if pf == -1 and self.f == 1:
                    self.sample()
                if maxmacro and nm >= maxmacro:
                    break
        except Halt:
            return 'halt'
        return 'ok'

    def tape_str(self, limit=10 ** 6):
        its, h = self.items()
        s = ''.join(w * n for w, n in its[:h]) + '|' + ''.join(w * n for w, n in its[h:])
        return s

if __name__ == '__main__':
    M = sys.argv[1]; N = float(sys.argv[2])
    s = WSim(M)
    import time
    t0 = time.time()
    r = s.run(N)
    print(r, s.steps, 'jumps', s.jumps, 'time %.1f' % (time.time() - t0))
