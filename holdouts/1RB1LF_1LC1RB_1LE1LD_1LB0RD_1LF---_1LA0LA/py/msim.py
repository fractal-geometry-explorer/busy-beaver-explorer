"""Macro simulator (blocks of K cells, run-length coded, big counts) with a hook that hands sub-tape wall visits to the
digit engine geng.  Exact when the hook is off; with the hook on, exact provided the recursion G is (tested)."""
import sys
import geng
from geng import gpow, zcons, rcons, dcons, pcons, econs, to_tokens

INF = 10 ** 30000
PLAN = [__import__("os").environ.get("NOPLAN") is None]


def parse_machine(m):
    T = []
    for row in m.split("_"):
        r = []
        for i in range(2):
            q = row[3 * i:3 * i + 3]
            r.append(None if q[0] == '-' else (int(q[0]), 1 if q[1] == 'R' else -1, ord(q[2]) - 65))
        T.append(r)
    return T


class Halt(Exception):
    pass


class Macro:
    def __init__(self, machine, K=24, hook=True):
        self.T = parse_machine(machine)
        self.K = K
        self.L = []          # runs [block, count], far left first
        self.R = []          # far right first
        self.s = 0
        self.dir = 1
        self.steps = 0       # machine steps made outside the hook
        self.gvisits = 0     # wall visits made by the hook (their steps are not counted)
        self.hooks = 0
        self.rejects = 0
        self.msteps = 0
        self.memo = {}
        self.hook = hook
        self.fmt = "0%db" % K
        self.trace = None
        geng.CST.update({'g0': 16, 'cend': -4, 'c1': 0, 'd1': 2, 'd0': 0, 'cR': 26})
        self.topv = 0
        self.landed = False
        self.on_top = None
        self.impure = 0
        self.maxjump = None
        self.topcap = 10 ** 100
        self.top_targets = []
        self.log = []
        self.pend = ""       # cells right of the explicit blocks of R
        self.lazy = None     # token list right of pend (not yet turned into blocks)
        self.plan = []       # facts from the last event walk: (S, d, W, cost): G^d(S) = W, G(W) is an event
        self.pi = 0
        self.planned = 0
        self.use_plan = PLAN[0]
        self.win = None

    # ---------------------------------------------------------------- cell level
    def runwin(self, s, cells, pos, skip_first, hook):
        T = self.T
        n = len(cells)
        steps = 0
        while 0 <= pos < n:
            r = cells[pos]
            if hook and s == 0 and r == 0 and not skip_first:
                if (pos + 1 >= n or cells[pos + 1] == 1) and (pos < 1 or cells[pos - 1] == 0) and \
                        (pos < 2 or cells[pos - 2] == 0):
                    return 'C', s, pos, steps
            skip_first = False
            tr = T[s][r]
            if tr is None:
                return 'H', s, pos, steps
            cells[pos] = tr[0]
            pos += tr[1]
            s = tr[2]
            steps += 1
            if steps > 5000000:
                raise RuntimeError("window loop")
        return ('L' if pos < 0 else 'R'), s, pos, steps

    def bits(self, b):
        return [int(c) for c in format(b, self.fmt)]

    def val(self, cells):
        v = 0
        for c in cells:
            v = v * 2 + c
        return v

    def trans(self, s, d, faced, behind):
        key = (s, d, faced, behind)
        r = self.memo.get(key)
        if r is None:
            K = self.K
            if d == 1:
                cells = self.bits(behind) + self.bits(faced); pos = K
            else:
                cells = self.bits(faced) + self.bits(behind); pos = K - 1
            kind, s2, pos2, st = self.runwin(s, cells, pos, False, self.hook)
            r = (kind, s2, self.val(cells[:K]), self.val(cells[K:]), pos2, st)
            self.memo[key] = r
        return r

    # ---------------------------------------------------------------- stacks
    @staticmethod
    def pop(st):
        if not st:
            return 0
        t = st[-1]
        b = t[0]
        if t[1] == 1:
            st.pop()
        else:
            t[1] -= 1
        return b

    @staticmethod
    def push(st, b, c=1):
        if st:
            if st[-1][0] == b:
                st[-1][1] += c
                return
        elif b == 0:
            return
        st.append([b, c])

    def step(self):
        if self.win is not None:
            cells, pos = self.win
            self.win = None
            self.msteps += 1
            self.winloop(5, cells, pos, False)
            return
        L, R = self.L, self.R
        d = self.dir
        s = self.s
        if not R and (self.pend or self.lazy is not None):
            self.fill()
        if d == 1:
            faced = self.pop(R); behind = self.pop(L)
        else:
            faced = self.pop(L); behind = self.pop(R)
        kind, s2, lb, rb, pos, st = self.trans(s, d, faced, behind)
        self.msteps += 1
        self.finish(kind, s2, lb, rb, pos, st, s, d, faced)

    def finish(self, kind, s2, lb, rb, pos, st, s, d, faced):
        L, R = self.L, self.R
        self.steps += st
        if not R and (self.pend or self.lazy is not None):
            self.fill()
        if kind == 'R':
            self.push(L, lb); self.push(L, rb)
            self.s = s2; self.dir = 1
            if d == 1 and s2 == s and R and R[-1][0] == faced:
                n = R[-1][1]
                r = self.trans(s, 1, faced, rb)
                if r[0] == 'R' and r[1] == s and r[3] == rb:
                    R.pop()
                    self.pop(L)
                    self.push(L, r[2], n)
                    self.push(L, rb)
                    self.steps += n * r[5]
        elif kind == 'L':
            self.push(R, rb); self.push(R, lb)
            self.s = s2; self.dir = 0
            if d == 0 and s2 == s and L and L[-1][0] == faced:
                n = L[-1][1]
                r = self.trans(s, 0, faced, lb)
                if r[0] == 'L' and r[1] == s and r[2] == lb:
                    L.pop()
                    self.pop(R)
                    self.push(R, r[3], n)
                    self.push(R, lb)
                    self.steps += n * r[5]
        elif kind == 'H':
            self.push(L, lb); self.push(R, rb)       # head inside; only for reporting
            self.s = s2
            self.steps += 1
            self.halt_pos = pos
            raise Halt()
        else:
            self.candidate(s2, lb, rb, pos)

    # ---------------------------------------------------------------- the hook
    def candidate(self, s, lb, rb, pos):
        cells = self.bits(lb) + self.bits(rb)
        ok = self.try_hook(cells, pos)
        if ok:
            self.win = ok          # the run loop resumes in this window (state F)
            return
        self.rejects += 1
        self.winloop(s, cells, pos, True)

    def winloop(self, s, cells, pos, skip):
        K = self.K
        while True:
            kind, s2, pos2, st = self.runwin(s, cells, pos, skip, self.hook)
            if kind == 'C':
                self.steps += st
                ok = self.try_hook(cells, pos2)
                if ok:
                    self.win = ok
                    return
                self.rejects += 1
                s, pos, skip = s2, pos2, True
                continue
            lb, rb = self.val(cells[:K]), self.val(cells[K:])
            self.finish(kind, s2, lb, rb, pos2, st, None, None, None)
            return

    def lstream(self):
        return [(format(b, self.fmt), c) for b, c in self.L]

    def rstream(self):
        self.flush()
        return [(format(b, self.fmt), c) for b, c in reversed(self.R)]

    # ---------------------------------------------------------------- the lazy right part
    def expand_one(self):
        """moves a few cells from the front of the lazy token list to pend"""
        T = self.lazy
        t, tail = T
        if type(t) is tuple:
            k = t[0]
            if k == 'E':
                self.lazy = t[1]
                return
            n = t[1]
            if k == 'Z':
                u = "10"; j = min(n, 24)
            elif k == 'R':
                u = "111010"; j = min(n, 8)
            else:
                u = "".join("11" * d + "10" for d in t[2]); j = 1
            cells = u * j
            if j < n:
                self.lazy = ((k, n - j) + t[2:], tail)
            else:
                self.lazy = tail
                if tail is None:
                    cells = cells[:-2]
            self.pend += cells
            return
        j = min(t, 24)
        if j < t:
            self.pend += "11" * j
            self.lazy = (t - j, tail)
        else:
            self.pend += "11" * t + ("10" if tail is not None else "")
            self.lazy = tail

    def take_right(self, n):
        """the n cells right of the explicit part (R must be empty)"""
        assert not self.R
        while len(self.pend) < n and self.lazy is not None:
            self.expand_one()
        if len(self.pend) < n:
            self.pend += "0" * (n - len(self.pend))
        c = self.pend[:n]
        self.pend = self.pend[n:]
        if self.lazy is None and '1' not in self.pend:
            self.pend = ""
        return c

    def fill(self):
        """R is empty: turn the front of the lazy part into blocks"""
        K = self.K
        blocks = []
        while not blocks and (self.pend or self.lazy is not None):
            stream = [(self.pend, 1)]
            T = self.lazy
            for _ in range(8):
                while T is not None and type(T[0]) is tuple and T[0][0] == 'E':
                    T = T[0][1]
                if T is None:
                    break
                t, tail = T
                if type(t) is tuple:
                    if t[0] == 'Z':
                        piece = [("10", t[1])]
                    elif t[0] == 'R':
                        piece = [("111010", t[1])]
                    else:
                        piece = [("".join("11" * d + "10" for d in t[2]), t[1])]
                else:
                    piece = [("11", t), ("10", 1)]
                if tail is None:
                    w, c = piece[-1]
                    piece[-1:] = ([(w, c - 1)] if c > 1 else []) + ([(w[:-2], 1)] if len(w) > 2 else [])
                stream.extend(piece)
                T = tail
            self.lazy = T
            blocks, self.pend = to_blocks(stream, K, pad=(T is None))
        self.R[:] = [[b, c] for b, c in reversed(blocks)]
        while self.R and self.R[0][0] == 0 and self.lazy is None and not self.pend:
            self.R.pop(0)

    def flush(self):
        """everything explicit"""
        if not self.pend and self.lazy is None:
            return
        stream = [(self.pend, 1)] + (word_cells(self.lazy) if self.lazy is not None else [])
        blocks, _ = to_blocks(stream, self.K, pad=True)
        self.pend = ""; self.lazy = None
        self.R[:] = [[b, c] for b, c in reversed(blocks)] + self.R
        # merge equal neighbours at the seam and drop far zeros
        R2 = []
        for b, c in self.R:
            if R2 and R2[-1][0] == b:
                R2[-1][1] += c
            else:
                R2.append([b, c])
        while R2 and R2[0][0] == 0:
            R2.pop(0)
        self.R[:] = R2

    def left_zeros(self, x):
        """number of 0 cells at the end of (L, x); None if all blank"""
        z = len(x) - len(x.rstrip('0'))
        if z < len(x):
            return z
        K = self.K
        for i in range(len(self.L) - 1, -1, -1):
            b, c = self.L[i]
            if b == 0:
                z += K * c
                continue
            w = format(b, self.fmt)
            return z + len(w) - len(w.rstrip('0'))
        return None

    def try_hook(self, cells, pos):
        """the head is in A on cells[pos] == 0 (window = cells, the stacks and the lazy part hold the rest).
        returns False, or (cells, pos) of a window with the head (state F) after the visits made"""
        K = self.K
        cs = "".join(map(str, cells))
        x = cs[:pos]
        z = self.left_zeros(x)
        jp = INF if z is None else z // 2
        if jp == 0:
            return False
        # the right part: explicit cells, then the lazy tokens
        expl = [(cs[pos + 1:], 1)] + [(format(b, self.fmt), c) for b, c in reversed(self.R)] + [(self.pend, 1)]
        first = None
        for w, c in expl:
            if w:
                first = w[0]; break
        if first is None and self.lazy is not None:
            self.flush()
            return self.try_hook(cells, pos)
        if first != '1':
            return False
        expl = drop_head(expl, 1)
        toks = parse_word(expl, self.lazy)
        if toks is BAD_SEAM:
            self.flush()
            return self.try_hook(cells, pos)
        top = jp >= INF
        if top:
            if self.landed:
                self.landed = False
            else:
                self.topv += 1
                if self.on_top:
                    self.on_top(self, toks)
        if toks is None:
            self.impure += 1
            return False
        M = 1 + jp if jp < INF else INF
        if self.maxjump is not None and M > self.maxjump:
            M = self.maxjump
        if top:
            if M > self.topcap:
                M = self.topcap
            if self.top_targets:
                while self.top_targets and self.top_targets[0] <= self.topv:
                    self.top_targets.pop(0)
                if self.top_targets and M > self.top_targets[0] - self.topv:
                    M = self.top_targets[0] - self.topv
        fact = None
        if self.use_plan:
            for j in range(self.pi, min(self.pi + 6, len(self.plan))):
                if eqlist(toks, self.plan[j][0]) and self.plan[j][1] <= M:
                    fact = self.plan[j]; self.pi = j + 1
                    break
        if fact is not None:
            self.planned += 1
            m, T2, cost = fact[1], fact[2], fact[3]
            if m == 0:
                return False
        else:
            geng.C[0] = 0
            self.last_call = (M, toks)
            try:
                T2, done = gpow(M, toks)
            except geng.Replay:
                # a deep carry that let go of its inputs stopped early (an event): redo the call keeping them
                geng.C[0] = 0
                del geng.EVTRACE[:]
                dsave = geng.DROP[0]
                geng.DROP[0] = False
                try:
                    T2, done = gpow(M, toks)
                finally:
                    geng.DROP[0] = dsave
            m = M if done is True else done
            cost = geng.C[0]
            if done is not True:
                plan = [(T2, 0, T2, 0)]
                for S, d, W, c, k in reversed(geng.EVTRACE):
                    if d > 0:
                        plan.append((S, d, W, c))
                    plan.append((W, 0, W, 0))
                self.plan = plan; self.pi = 0
                if m > 0:
                    self.plan.insert(0, (toks, m, T2, cost))
                    self.pi = 1
            if m == 0:
                return False
        self.steps += cost - 1
        if top:
            self.topv += m
            self.landed = True
            if self.on_top:
                self.on_top(self, T2)
        self.hooks += 1
        self.gvisits += m
        if self.trace:
            self.trace(self, m, toks, T2)
        # the right part is now the word T2; the left part loses 2 (m - 1) blank cells
        del self.R[:]
        self.pend = ""
        self.lazy = T2
        D = 2 * (m - 1)
        L = self.L
        while D > len(x):
            if not L:
                x = ""; D = 0
                break
            b, c = L[-1]
            if b == 0:
                q = min(c, (D - len(x)) // K)
                if q:
                    if q == c:
                        L.pop()
                    else:
                        L[-1][1] -= q
                    D -= q * K
                    continue
            x = format(self.pop(L), self.fmt) + x
        x = x[:len(x) - D]
        # a window with the head (state F) on the last cell of the left part
        p = len(x)
        if p <= K:
            lb = self.pop(self.L)
            w = format(lb, self.fmt) + x + self.take_right(K - p)
            hp = K + p - 1
        else:
            w = x + self.take_right(2 * K - p)
            hp = p - 1
        return [int(ch) for ch in w], hp

    def run(self, max_msteps=None, until=None):
        try:
            while True:
                self.step()
                if max_msteps is not None and self.msteps >= max_msteps:
                    return 'limit'
                if until is not None and until(self):
                    return 'until'
        except Halt:
            return 'halt'

    def tape_str(self, limit=10 ** 7):
        """the whole tape as a string of 0/1 with the head marker, when it is small enough"""
        while self.win is not None:
            self.step()
        self.flush()
        tot = sum(c for b, c in self.L) + sum(c for b, c in self.R)
        assert tot * self.K <= limit
        l = "".join(format(b, self.fmt) * c for b, c in self.L)
        r = "".join(format(b, self.fmt) * c for b, c in reversed(self.R))
        return l, r


# -------------------------------------------------------------------- streams of cells: lists of (word, count)
def trailing_zeros(stream):
    """number of 0 cells at the end of a left stream; None if it is all zeros (blank to infinity)"""
    z = 0
    for w, c in reversed(stream):
        if not w:
            continue
        if '1' not in w:
            z += len(w) * c
            continue
        z += len(w) - len(w.rstrip('0'))
        return z
    return None


def drop_head(stream, k):
    out = list(stream)
    while k:
        w, c = out[0]
        if len(w) * c <= k:
            k -= len(w) * c; out.pop(0); continue
        q, r = divmod(k, len(w))
        c -= q
        k = 0
        if r:
            out[0:1] = [(w[r:], 1)] + ([(w, c - 1)] if c > 1 else [])
        else:
            out[0] = (w, c)
    return out


def drop_tail(stream, k):
    out = list(stream)
    while k:
        if not out:
            return out               # blank to infinity
        w, c = out[-1]
        if len(w) * c <= k:
            k -= len(w) * c; out.pop(); continue
        q, r = divmod(k, len(w))
        c -= q
        k = 0
        if r:
            out[-1:] = ([(w, c - 1)] if c > 1 else []) + [(w[:-r], 1)]
        else:
            out[-1] = (w, c)
    return out


class DParse:
    def __init__(self):
        self.out = []
        self.y = 0
        self.half = None
        self.ok = True

    def cells(self, w):
        half, y, out = self.half, self.y, self.out
        for ch in w:
            if half is None:
                half = ch
            else:
                if half == '1':
                    if ch == '1':
                        y += 1
                    else:
                        out.append(y); y = 0
                else:
                    self.ok = False
                half = None
        self.half, self.y = half, y

    def feed(self, w, n):
        if not w:
            return
        if n <= 4:
            for _ in range(n):
                self.cells(w)
            return
        self.cells(w); self.cells(w)
        n -= 2
        if not self.ok:
            return
        k0, y0, h0 = len(self.out), self.y, self.half
        self.cells(w)
        n -= 1
        E = self.out[k0:]
        if '0' not in w and len(w) % 2 == 0:
            self.y += (len(w) // 2) * n
            return
        if self.y == y0 and self.half == h0 and E:
            if all(e == 0 for e in E):
                self.out.append(('Z', len(E) * n)); return
            if len(E) % 2 == 0 and all(E[i] == (1 if i % 2 == 0 else 0) for i in range(len(E))):
                self.out.append(('R', (len(E) // 2) * n)); return
            if len(E) % 2 == 0 and all(E[i] == (0 if i % 2 == 0 else 1) for i in range(len(E))):
                # 0 1 0 1 ... = 0 (1 0)^(k n - 1) 1
                self.out.append(0); self.out.append(('R', (len(E) // 2) * n - 1)); self.out.append(1); return
            if len(E) <= 12:
                r = 0
                while E[r] == 0:
                    r += 1
                if n >= 2:
                    self.out.extend(E[:r])
                    self.out.append(('P', n - 1, tuple(E[r:] + E[:r])))
                    self.out.extend(E[r:])
                    return
        if n * len(w) > 2000000:
            self.ok = False
            return
        for _ in range(n):
            self.cells(w)


BAD_SEAM = "bad seam"


def atoms(T):
    """the digits of a token list in a canonical run form: ('z', m) for a maximal run of zeros, a digit >= 1, or a
    long run token; each with the list node it starts at (None when it starts inside a token)"""
    z = 0
    zs = None
    while T is not None:
        t = T[0]
        if type(t) is tuple:
            k = t[0]
            if k == 'E':
                T = t[1]
                continue
            if k == 'Z':
                if z == 0:
                    zs = T
                z += t[1]
            else:
                w = (1, 0) if k == 'R' else t[2]
                n = t[1]
                if n <= 4:
                    node = T
                    for d in w * n:
                        if d == 0:
                            if z == 0:
                                zs = node
                            z += 1
                        else:
                            if z:
                                yield ('z', z), zs
                                z = 0
                            yield d, node
                        node = None
                else:
                    if z:
                        yield ('z', z), zs
                        z = 0
                    yield (k, n, w), T
        else:
            if z:
                yield ('z', z), zs
                z = 0
            yield t, T
        T = T[1]
    if z:
        yield ('z', z), zs
    yield 'end', None


def eqlist(A, B):
    """equal words (token lists up to their token structure); cheap when they share their tails"""
    while True:
        if A is B:
            return True
        if A is None or B is None:
            break
        if A[0] != B[0] or (type(A[0]) is tuple and A[0][0] == 'E'):
            break
        A = A[1]; B = B[1]
    ga, gb = atoms(A), atoms(B)
    while True:
        a, na = next(ga)
        b, nb = next(gb)
        if na is not None and na is nb:
            return True
        if a != b:
            return False
        if a == 'end':
            return True


def parse_word(stream, lazy=None):
    """a right stream (cells after the wall pair), followed by the token list lazy, as a token list; None if it is
    not a word of X and Y up to the blank end"""
    s = list(stream)
    if lazy is None:
        while s and '1' not in s[-1][0]:
            s.pop()
        if s:
            w, c = s[-1]
            ws = w.rstrip('0')
            if ws != w:
                s[-1:] = ([(w, c - 1)] if c > 1 else []) + [(ws, 1)]
    p = DParse()
    for w, c in s:
        p.feed(w, c)
        if not p.ok:
            return None
    if lazy is not None:
        if p.half is not None or p.y != 0:
            return BAD_SEAM
        items = p.out
    else:
        if p.half is not None:
            if p.half != '1':
                return None
            p.out.append(p.y); p.y = 0
        items = p.out + [p.y]
    T = lazy
    for it in reversed(items):
        if type(it) is tuple:
            T = zcons(it[1], T) if it[0] == 'Z' else rcons(it[1], T) if it[0] == 'R' else econs(it[1], it[2], T)
        elif it == 0:
            T = zcons(1, T)
        else:
            T = dcons(it, T)
    return T


def word_cells(T):
    """the cells of a token list as a stream"""
    out = []
    toks = to_tokens(T)
    for i, t in enumerate(toks):
        if type(t) is tuple:
            if t[0] == 'Z':
                out.append(("10", t[1]))
            elif t[0] == 'R':
                out.append(("111010", t[1]))
            else:
                out.append(("".join("11" * d + "10" for d in t[2]), t[1]))
        else:
            out.append(("11", t)); out.append(("10", 1))
    # drop the last X
    w, c = out[-1]
    assert w.endswith("10")
    out[-1:] = ([(w, c - 1)] if c > 1 else []) + ([(w[:-2], 1)] if len(w) > 2 else [])
    return out


def to_blocks(stream, K, pad=None):
    """chunks a stream into blocks of K cells (the last one padded with zeros); list of (block, count)"""
    out = []
    pend = ""
    work = list(reversed(stream))

    def emit(bs, c):
        b = int(bs, 2)
        if out and out[-1][0] == b:
            out[-1][1] += c
        else:
            out.append([b, c])
    while work:
        w, n = work.pop()
        Lw = len(w)
        if Lw == 0 or n == 0:
            continue
        if n * Lw <= 4 * K or K % Lw != 0:
            if n * Lw > 5000000:
                raise RuntimeError("to_blocks: run of period %d too long" % Lw)
            pend += w * n
            while len(pend) >= K:
                emit(pend[:K], 1); pend = pend[K:]
            continue
        if pend == "":
            per = K // Lw
            c = n // per
            emit(w * per, c)
            n -= c * per
            if n:
                pend = w * n
            continue
        need = K - len(pend)
        q, r = divmod(need, Lw)
        cellsw = w * q + w[:r]
        emit(pend + cellsw, 1)
        pend = ""
        if r:
            work.append((w[r:], 1))
            if n - q - 1 > 0:
                work.append((w[r:] + w[:r], n - q - 1))
        else:
            if n - q > 0:
                work.append((w, n - q))
    if pad is None:
        if pend:
            emit(pend + "0" * (K - len(pend)), 1)
        return out
    if pad and pend:
        emit(pend + "0" * (K - len(pend)), 1)
        pend = ""
    return out, pend
