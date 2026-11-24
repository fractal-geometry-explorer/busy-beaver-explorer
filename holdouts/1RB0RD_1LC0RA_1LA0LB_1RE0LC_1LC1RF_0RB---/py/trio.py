"""trio: exact accelerated simulator with symbolically verified bounce jumps.

Written for the three holdouts 1RB0RD_1LC0RA_1LA0LB_1RE0LC_{1LC,1LD,1RA}1RF_0RB---, which share one outer phase
(a word over c = 1101010 and a = 10 that gains one c per round trip), but it takes any 2-symbol machine.

Tape: left stack + buffer + right stack.  A stack item is [word, value, form]: `value` copies of `word` (a string of
0/1 in tape order); the top of a stack is the item nearest the buffer.  The head moves cell by cell in the buffer.
Cells leaving the buffer are cut into the words c, its image 0011001, 10 and 01 (longest first) and run-length coded;
tandem repeats of items become one item whose word is their string (a *group*: the blocks of these machines nest,
with group words of 38, 110, 326, 974, ... cells).

Level 1, sweeps (exact by induction on the copies).  When the head leaves the buffer in state s and faces an item
(w, n), with the D cells behind it equal to T (D = 0..3), the machine is run on one copy of w plus T alone.  If the head
leaves that copy at the far side in state s, never stepping behind T, and the D cells behind it are T again, then n
copies are crossed at once, leaving n copies of the written word behind.  When no such rule exists, the run is
re-cut at the point where two successive copies are entered in the same state (w^n = p (q p)^(n-1) q), and failing
that one copy is unrolled.

Level 2, bounce jumps (exact, verified by symbolic execution, no extrapolation).  A *window* starts at a macro turn
(the head reaches one stack after last touching the other) whose state, head and buffer were seen at an earlier turn.
Each item first touched in the window gets a variable x_i equal to its count; counts and the step counter are carried
along as affine forms in these variables, and every decision that depended on a count (a copy taken off a run of k
copies leaves a run, or leaves nothing) is recorded as a guard (x_i + c >= 1, or x_i + c = 0).  The window closes at a
later turn with the same state, head and buffer whose touched part of the tape, brought to a canonical form (each run
turned to the least rotation of its word and absorbing the whole copies next to it; a rewriting that keeps the
string), has the same words and constant cells, every count equal to its start variable plus a constant d_i.  The run
of the window is then a proof that from every tape of this form whose counts satisfy the guards the machine reaches the
same form with counts x + d, in S(x) steps (S affine).  The jump applies it J more times, the largest J for which all
guards hold at x + j d for j <= J; the step counter grows by the exact sum.

Everything rests on this code being right; trio_check.py compares it with a plain C simulator (tape, state, head) at
step counts up to 10^10.
"""
import sys

WORDS = ['1101010', '0011001', '10', '01']


def parse(m):
    T = []
    for g in m.split('_'):
        row = []
        for r in range(2):
            t = g[3 * r:3 * r + 3]
            row.append(None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65))
        T.append(row)
    return T


class Halt(Exception):
    pass


# ----------------------------------------------------------------- affine forms: dict var -> coef, key None = const
def fadd(f, g):
    r = dict(f)
    for k, v in g.items():
        r[k] = r.get(k, 0) + v
        if r[k] == 0 and k is not None:
            del r[k]
    return r


def fscale(f, a):
    return {k: v * a for k, v in f.items()} if a else {}


def fconst(f):
    return f.get(None, 0)


class Sim:
    MAXD = 3
    GROUP = True
    PMAX = 8
    GMAX = 4096
    WMAX = 600
    KEEP = 24
    BIG = 2          # counts below this get no variable (they are kept as constants and must match exactly)

    def __init__(self, machine, words=WORDS, jumps=True):
        self.m = machine
        self.T = parse(machine)
        self.words = sorted(set(words), key=len, reverse=True)
        self.maxw = max(len(w) for w in self.words)
        self.L = []      # items, top = last
        self.R = []
        self.buf = [0]
        self.h = 0
        self.s = 0
        self.steps = 0
        self.rules = {}
        self.aligns = {}
        self.jumps = jumps
        self.lastdir = 0
        self.win = None
        self.nvar = 0
        self.njumps = 0
        self.jumped_steps = 0
        self.nsweeps = 0
        self.nabsorb = 0
        self.ngroup = 0
        self.nsamp = 0
        self.lastsig = {}
        self.nrot = 0
        self.turns = 0
        self.why = 0
        self.log = None   # optional callable(sim, kind, info)
        self.halted = False

    # ------------------------------------------------------------- window bookkeeping
    def _touch(self, side):
        """the top item of the stack `side` is about to be changed or removed: register it as an original"""
        w = self.win
        if w is None:
            return
        st = self.L if side < 0 else self.R
        i = len(st) - 1
        low = w['lowL'] if side < 0 else w['lowR']
        if i < low:
            it = st[i]
            if it[1] >= self.BIG:
                self.nvar += 1
                v = self.nvar
                it[2] = {v: 1}
                w['vals'][v] = it[1]
            else:
                it[2] = None
            w['orig'][side].append((it[0], it[1], it[2]))   # in order of decreasing index
            if side < 0:
                w['lowL'] = i
            else:
                w['lowR'] = i

    def _form(self, it):
        return it[2] if it[2] is not None else {None: it[1]}

    def _guard_ge1(self, f):
        if self.win is not None and len(f) > (1 if None in f else 0):
            self.win['ge'].append(dict(f))

    def _guard_eq(self, f, val):
        if self.win is not None and len(f) > (1 if None in f else 0):
            self.win['eq'].append((dict(f), val))

    def _set(self, it, val, form):
        it[1] = val
        it[2] = form if (self.win is not None and form is not None and len(form) > (1 if None in form else 0)) else None

    # ------------------------------------------------------------- stacks
    def _push_item(self, side, word, val, form):
        """push (word, val) onto stack side, merging with an equal-word top"""
        if val == 0:
            return
        st = self.L if side < 0 else self.R
        if st and st[-1][0] == word:
            self._touch(side)
            top = st[-1]
            if self.win is not None:
                nf = fadd(self._form(top), form if form is not None else {None: val})
            else:
                nf = None
            self._set(top, top[1] + val, nf)
        else:
            it = [word, val, None]
            st.append(it)
            self._set(it, val, form)
        if self.GROUP and st[-1][2] is None:
            self._group(side)

    def _group(self, side):
        """tandem repeats of constant items at the top become one item whose word is their string"""
        st = self.L if side < 0 else self.R
        n = len(st)
        top = st[-1]
        for p in range(1, self.PMAX + 1):
            if n < p + 1:
                break
            # the top p items equal the word of the item below them: add one copy to it
            below = st[n - 1 - p]
            if p >= 2 and below[1] >= 1 and len(below[0]) > self.maxw:
                ok = True
                for q in range(n - p, n):
                    if st[q][2] is not None or st[q][1] == 0:
                        ok = False
                        break
                if ok:
                    items = st[n - p:]
                    s = ''.join(w * c for w, c, _ in (items if side < 0 else reversed(items)))
                    if s == below[0]:
                        for _ in range(p):
                            self._touch(side)
                            st.pop()
                        self._touch(side)
                        self._set(below, below[1] + 1, fadd(self._form(below), {None: 1}) if self.win is not None else None)
                        self.ngroup += 1
                        return
            if n < 2 * p or p < 2:
                continue
            a = st[n - p:]
            b = st[n - 2 * p:n - p]
            if a[-1][0] != b[-1][0] or a[-1][1] != b[-1][1]:
                continue
            ok = True
            for x, y in zip(a, b):
                if x[0] != y[0] or x[1] != y[1] or x[2] is not None or y[2] is not None or x[1] == 0:
                    ok = False
                    break
            if not ok:
                continue
            s = ''.join(w * c for w, c, _ in (a if side < 0 else reversed(a)))
            if len(s) > self.GMAX:
                continue
            for _ in range(2 * p):
                self._touch(side)
                st.pop()
            it = [s, 2, None]
            st.append(it)
            self.ngroup += 1
            return

    def _push_run(self, side, word, val, form):
        """push a run, first absorbing whole copies of `word` from the constant items next to it"""
        st = self.L if side < 0 else self.R
        lw = len(word)
        tot = 0
        k = 0
        while k < len(st) and k < 8:
            it = st[-1 - k]
            if (self.win is not None and it[2] is not None) or it[1] * len(it[0]) > 4 * lw:
                break
            tot += it[1] * len(it[0])
            k += 1
            if tot >= 2 * lw:
                break
        if k and tot >= lw:
            items = st[len(st) - k:]
            if side < 0:
                X = ''.join(w * c for w, c, _ in items)            # tape order, run goes to its right
                j = 0
                while len(X) - (j + 1) * lw >= 0 and X.endswith(word, 0, len(X) - j * lw):
                    j += 1
                if j:
                    for _ in range(k):
                        self._touch(side)
                        st.pop()
                    self._push_cells(side, [int(c) for c in X[:len(X) - j * lw]])
            else:
                X = ''.join(w * c for w, c, _ in reversed(items))  # tape order, run goes to its left
                j = 0
                while X.startswith(word, j * lw):
                    j += 1
                if j:
                    for _ in range(k):
                        self._touch(side)
                        st.pop()
                    self._push_cells(side, [int(c) for c in X[j * lw:]])
            if j:
                val += j
                if form is not None:
                    form = fadd(form, {None: j})
                self.nabsorb += 1
        self._push_item(side, word, val, form)

    def _push_cells(self, side, cells):
        """cells in tape order; side -1: they go onto the left stack (cells[0] deepest); +1: right stack"""
        s = ''.join(map(str, cells))
        # re-parse the small constant items on top together with the new cells
        st = self.L if side < 0 else self.R
        pre = []
        tot = 0
        while st and len(pre) < 12:
            it = st[-1]
            if it[1] != 1 or len(it[0]) >= self.maxw or (self.win is not None and it[2] is not None):
                break
            if tot + len(it[0]) > 40:
                break
            self._touch(side)
            st.pop()
            pre.append(it[0])
            tot += len(it[0])
        if pre:
            if side < 0:
                s = ''.join(reversed(pre)) + s
            else:
                s = s + ''.join(pre)
        if side < 0:
            i = 0
            n = len(s)
            while i < n:
                st = self.L
                for bw in self.words:
                    if s.startswith(bw, i):
                        break
                else:
                    bw = s[i]
                if st:
                    w = st[-1][0]
                    lw = len(w)
                    if lw >= len(bw) and s.startswith(w, i):
                        k = 0
                        while s.startswith(w, i + k * lw):
                            k += 1
                        self._push_item(-1, w, k, None)
                        i += k * lw
                        continue
                w = bw
                self._push_item(-1, w, 1, None)
                i += len(w)
        else:
            j = len(s)
            while j > 0:
                st = self.R
                for bw in self.words:
                    if len(bw) <= j and s.endswith(bw, 0, j):
                        break
                else:
                    bw = s[j - 1]
                if st:
                    w = st[-1][0]
                    lw = len(w)
                    if lw >= len(bw) and s.endswith(w, 0, j):
                        k = 0
                        while j - (k + 1) * lw >= 0 and s.endswith(w, 0, j - k * lw):
                            k += 1
                        self._push_item(1, w, k, None)
                        j -= k * lw
                        continue
                w = bw
                self._push_item(1, w, 1, None)
                j -= len(w)

    def _push_cells_sep(self, side, cells):
        """push cells without merging them into the item below"""
        st = self.L if side < 0 else self.R
        st.append(['#', 0, None])
        self._push_cells(side, cells)
        j = len(st) - 1
        while st[j][0] != '#':
            j -= 1
        del st[j]

    def align(self, s, d, w, T):
        """for a run of w faced in state s with context T and no sweep rule: the number r of cells (0 < r < |w|) to
        take off the near end so that the rest is entered at a point where two successive copies are entered in the
        same state, or None"""
        key = (s, d, w, T)
        r = self.aligns.get(key, 0)
        if r != 0:
            return r
        r = None
        lw = len(w)
        D = len(T)
        TT = self.T
        if d < 0:
            cells = [int(c) for c in w + w] + list(T)
            h = 2 * lw - 1
        else:
            cells = list(T) + [int(c) for c in w + w]
            h = D
        n = len(cells)
        cross = {}
        st = s
        for _ in range(40 * n):
            t = TT[st][cells[h]]
            if t is None:
                break
            cells[h] = t[0]
            nh = h + t[1]
            st = t[2]
            if d < 0 and nh < h and h not in cross:
                cross[h] = st
            if d > 0 and nh > h and nh not in cross:
                cross[nh] = st
            h = nh
            if h < 0 or h >= n:
                break
        for rr in range(1, lw):
            if d < 0:
                x = 2 * lw - rr
                y = x - lw
            else:
                x = D + rr
                y = x + lw
            if x in cross and y in cross and cross[x] == cross[y]:
                r = rr
                break
        if len(self.aligns) > 20000:
            self.aligns.clear()
        self.aligns[key] = r
        return r

    def flush(self):
        """keep at most KEEP cells on each side of the head in the buffer"""
        b = self.buf
        h = self.h
        K = self.KEEP
        if h > 2 * K:
            self._push_cells(-1, b[:h - K])
            del b[:h - K]
            self.h = h = K
        if len(b) - h > 2 * K + 1:
            self._push_cells(1, b[h + K + 1:])
            del b[h + K + 1:]

    # ------------------------------------------------------------- sweep rules
    def rule(self, s, d, w, T):
        key = (s, d, w, T)
        r = self.rules.get(key, 0)
        if r != 0:
            return r
        r = None
        lw = len(w)
        D = len(T)
        if d < 0:
            cells = [int(c) for c in w] + list(T)
            h = lw - 1
        else:
            cells = list(T) + [int(c) for c in w]
            h = D
        st = s
        n = len(cells)
        k = 0
        TT = self.T
        ok = False
        while k < 50 * (lw + D) + 50:
            t = TT[st][cells[h]]
            if t is None:
                break
            cells[h] = t[0]
            h += t[1]
            st = t[2]
            k += 1
            if d < 0:
                if h < 0:
                    ok = True
                    break
                if h >= n:
                    break
            else:
                if h >= n:
                    ok = True
                    break
                if h < 0:
                    break
        if ok and st == s:
            if d < 0:
                if tuple(cells[:D]) == T:
                    r = (''.join(map(str, cells[D:])), k)
            else:
                if tuple(cells[lw:]) == T:
                    r = (''.join(map(str, cells[:lw])), k)
        if len(self.rules) > 20000:
            self.rules.clear()
        self.rules[key] = r
        return r

    # ------------------------------------------------------------- edges
    def edge(self, d):
        """the head has left the buffer on side d"""
        if d != self.lastdir:
            self.lastdir = d
            self.turns += 1
            if self.jumps:
                self.sample(d)
        st = self.L if d < 0 else self.R
        if not st:
            if d < 0:
                self.buf.insert(0, 0)
                self.h = 0
            else:
                self.buf.append(0)
            return
        top = st[-1]
        w = top[0]
        b = self.buf
        for D in range(min(self.MAXD, len(b)), -1, -1):
            T = tuple(b[:D]) if d < 0 else tuple(b[len(b) - D:])
            r = self.rule(self.s, d, w, T)
            if r is not None:
                break
        if r is not None:
            O, k = r
            self._touch(d)
            st.pop()
            n = top[1]
            f = self._form(top)
            self._guard_ge1(f)
            if d < 0:
                rest = b[D:]
                if rest:
                    self._push_cells(1, rest)
                self._push_run(1, O, n, f if self.win is not None else None)
                self.buf = list(T)
                self.h = -1
            else:
                rest = b[:len(b) - D]
                if rest:
                    self._push_cells(-1, rest)
                self._push_run(-1, O, n, f if self.win is not None else None)
                self.buf = list(T)
                self.h = D
            self.steps += n * k
            if self.win is not None:
                self.win['S'] = fadd(self.win['S'], fscale(f, k))
            self.nsweeps += 1
            return
        r = self.align(self.s, d, w, tuple(b[:min(self.MAXD, len(b))]) if d < 0 else tuple(b[max(0, len(b) - self.MAXD):])) if top[1] >= 2 and len(w) >= 2 else None
        if r is not None:
            # rotate: w^n = p (q p)^(n-1) q on the left (q = the r cells nearest the head), mirrored on the right
            self._touch(d)
            f = self._form(top)
            nf = fadd(f, {None: -1})
            self._guard_ge1(nf)
            st.pop()
            if d < 0:
                p, q = w[:-r], w[-r:]
                self._push_cells(-1, [int(x) for x in p])
                self._push_run(-1, q + p, top[1] - 1, nf if self.win is not None else None)
            else:
                q, p = w[:r], w[r:]
                self._push_cells(1, [int(x) for x in p])
                self._push_run(1, p + q, top[1] - 1, nf if self.win is not None else None)
            cells = [int(x) for x in q]
            if r <= 16:
                if d < 0:
                    self.buf[:0] = cells
                    self.h = r - 1
                else:
                    self.buf.extend(cells)
            else:
                self._push_cells_sep(d, cells)
            self.nrot += 1
            return
        # unroll one copy
        self._touch(d)
        f = self._form(top)
        nf = fadd(f, {None: -1})
        if top[1] == 1:
            st.pop()
            self._guard_eq(nf, 0)
        else:
            self._guard_ge1(nf)
            self._set(top, top[1] - 1, nf)
        cells = [int(c) for c in w]
        if len(w) > 16:
            # a group word: put its cells back on the stack, tokenized (not merged into what is below)
            self._push_cells_sep(d, cells)
            return
        if d < 0:
            self.buf[:0] = cells
            self.h = len(cells) - 1
        else:
            self.buf.extend(cells)

    # ------------------------------------------------------------- samples / jumps
    def _sig(self, d):
        return (d, self.s, self.h, tuple(self.buf))

    def _clear_forms(self):
        w = self.win
        for it in self.L[w['lowL']:]:
            it[2] = None
        for it in self.R[w['lowR']:]:
            it[2] = None
        self.win = None
        if self.GROUP:
            for side, st, low in ((-1, self.L, w['lowL']), (1, self.R, w['lowR'])):
                if len(st) - low > 3:
                    low = max(0, low - 2 * self.PMAX)
                    rest = st[low:]
                    del st[low:]
                    for it in rest:
                        self._push_item(side, it[0], it[1], None)

    def _open(self, d, sig, P):
        self.win = {'sig': sig, 'P': max(P, 1) if P else 64, 'lowL': len(self.L), 'lowR': len(self.R), 'orig': {-1: [], 1: []},
                    'vals': {}, 'ge': [], 'eq': [], 'S': {}, 'steps0': self.steps, 'n': 0}

    def sample(self, d):
        self.nsamp += 1
        sig = self._sig(d)
        w = self.win
        if w is not None:
            w['n'] += 1
            if sig == w['sig']:
                ok = self.tryjump(w)
                if ok:
                    self._clear_forms()
                    self.win = None
                    self.lastsig = {}
                    return
                if w['n'] >= self.WMAX or self.why in (1, 8):
                    self._clear_forms()
                    self.win = None
            elif w['n'] >= self.WMAX:
                self._clear_forms()
                self.win = None
        last = self.lastsig.get(sig)
        self.lastsig[sig] = self.nsamp
        if len(self.lastsig) > 4096:
            self.lastsig = {}
        if self.win is None and last is not None and self.nsamp - last <= 256:
            self._open(d, sig, self.nsamp - last)

    _lr = {}

    @classmethod
    def least_rot(cls, w):
        r = cls._lr.get(w)
        if r is None:
            # Booth's algorithm: start of the least rotation
            S = w + w
            n2 = len(S)
            f = [-1] * n2
            k = 0
            for j in range(1, n2):
                sj = S[j]
                i = f[j - k - 1]
                while i != -1 and sj != S[k + i + 1]:
                    if sj < S[k + i + 1]:
                        k = j - i - 1
                    i = f[i]
                if sj != S[k + i + 1]:
                    if sj < S[k]:
                        k = j
                    f[j - k] = -1
                else:
                    f[j - k] = i + 1
            r = k % len(w)
            if len(cls._lr) > 100000:
                cls._lr.clear()
            cls._lr[w] = r
        return r

    @classmethod
    def _rotkey(cls, w):
        r = cls.least_rot(w)
        return w[r:] + w[:r] if r else w

    @classmethod
    def canon(cls, items):
        """canonical form of a list of items (word, val, form) in tape order, as an equal string: constant items as
        cells; each run with a variable turned to the least rotation of its word, then absorbing whole copies next to
        it"""
        seq = []
        cur = []
        for w, v, f in items:
            if f is None:
                cur.append(w * v)
            else:
                seq.append(''.join(cur))
                cur = []
                seq.append([w, dict(f)])
        seq.append(''.join(cur))
        for i in range(1, len(seq), 2):
            w, f = seq[i]
            r = cls.least_rot(w)
            if r:
                u, v = w[:r], w[r:]
                seq[i - 1] += u
                seq[i + 1] = v + seq[i + 1]
                f[None] = f.get(None, 0) - 1
                seq[i] = [v + u, f]
        ch = True
        while ch:
            ch = False
            for i in range(1, len(seq), 2):
                w, f = seq[i]
                lw = len(w)
                X = seq[i - 1]
                Y = seq[i + 1]
                e = len(X)
                j = 0
                while e >= lw and X.endswith(w, 0, e):
                    e -= lw
                    j += 1
                if j:
                    X = X[:e]
                b = 0
                while Y.startswith(w, b):
                    b += lw
                    j += 1
                if b:
                    Y = Y[b:]
                if j:
                    f[None] = f.get(None, 0) + j
                    ch = True
                seq[i - 1] = X
                seq[i + 1] = Y
        return [tuple(x) if isinstance(x, list) else x for x in seq]

    def tryjump(self, w):
        pinned = {}
        for f, val in w['eq']:
            if len(f) - (1 if None in f else 0) == 1:
                (v,) = [k for k in f if k is not None]
                if f[v] == 1:
                    pinned[v] = val - fconst(f)
                    continue
            self.why = 1
            return False
        delta = {}
        for side, st, low in ((-1, self.L, w['lowL']), (1, self.R, w['lowR'])):
            orig = w['orig'][side]
            cur = st[low:]
            if side < 0:
                orig = orig[::-1]
            else:
                cur = cur[::-1]
            # pinned variables are constants
            o = [(a, b, (None if (f is None or next(iter(f)) in pinned) else f)) for a, b, f in orig]
            c = []
            for a, b, f in cur:
                if f is not None:
                    ks = [k for k in f if k is not None]
                    if len(ks) != 1 or f[ks[0]] != 1:
                        self.why = 6
                        return False
                    if ks[0] in pinned:
                        f = None
                c.append((a, b, f))
            ka = [self._rotkey(a) for a, b, f in o if f is not None]
            kb = [self._rotkey(a) for a, b, f in c if f is not None]
            if ka != kb:
                self.why = 2
                return False
            A = self.canon(o)
            B = self.canon(c)
            if len(A) != len(B):
                self.why = 2
                return False
            for i in range(0, len(A), 2):
                if A[i] != B[i]:
                    self.why = 3
                    return False
            for i in range(1, len(A), 2):
                (wa, fa), (wb, fb) = A[i], B[i]
                if wa != wb:
                    self.why = 3
                    return False
                (va,) = [k for k in fa if k is not None]
                kb = [k for k in fb if k is not None]
                if kb != [va] or va in delta:
                    self.why = 6
                    return False
                delta[va] = fb.get(None, 0) - fa.get(None, 0)
        vals = w['vals']
        for v in vals:
            if v not in delta and v not in pinned:
                self.why = 7
                return False
        for v in pinned:
            delta[v] = 0
        if not any(delta.values()):
            raise RuntimeError('exact cycle found (would prove non-halting) at step %d' % self.steps)
        J = None
        for g in w['ge']:
            gd = sum(c * delta[k] for k, c in g.items() if k is not None)
            if gd >= 0:
                continue
            g0 = fconst(g) + sum(c * vals[k] for k, c in g.items() if k is not None)
            # current (after one period) values are vals + delta: condition at iteration j (start values vals+j*delta)
            jmax = (g0 - 1) // (-gd)
            if J is None or jmax < J:
                J = jmax
        if J is None:
            raise RuntimeError('unbounded jump (would prove non-halting) at step %d' % self.steps)
        # iterations j = 1..J are valid (j = 0 was the window itself); state now = start of iteration 1
        if J < 1:
            self.why = 9
            return False
        S = w['S']
        Sd = sum(c * delta[k] for k, c in S.items() if k is not None)
        S0 = fconst(S) + sum(c * vals[k] for k, c in S.items() if k is not None)
        # sum_{j=1}^{J} (S0 + j*Sd)
        add = J * S0 + Sd * J * (J + 1) // 2
        # apply: every item with a form x_v + d_v gets value vals[v] + (J+1)*delta[v]
        for st, low in ((self.L, w['lowL']), (self.R, w['lowR'])):
            for it in st[low:]:
                if it[2] is not None:
                    (v,) = [k for k in it[2] if k is not None]
                    it[1] += J * delta[v]
                    assert it[1] >= 1
        self.steps += add
        self.njumps += 1
        self.jumped_steps += add
        if self.log:
            self.log(self, 'jump', (J, add, sorted(delta.values())))
        return True

    # ------------------------------------------------------------- main loop
    def run(self, maxsteps, maxops=None):
        T = self.T
        ops = 0
        while self.steps < maxsteps:
            buf = self.buf
            h = self.h
            s = self.s
            n = len(buf)
            k = 0
            while 0 <= h < n:
                t = T[s][buf[h]]
                if t is None:
                    self.h = h
                    self.s = s
                    self.steps += k
                    self.halted = True
                    raise Halt(self.steps)
                buf[h] = t[0]
                h += t[1]
                s = t[2]
                k += 1
            self.h = h
            self.s = s
            self.steps += k
            if self.win is not None and k:
                self.win['S'] = fadd(self.win['S'], {None: k})
            if h < 0:
                self.edge(-1)
            else:
                self.edge(1)
            if self.h > 2 * self.KEEP or len(self.buf) - self.h > 2 * self.KEEP + 1:
                self.flush()
            ops += 1
            if maxops and ops >= maxops:
                break

    def tape(self):
        left = ''.join(w * c for w, c, _ in self.L)
        mid = ''.join(map(str, self.buf))
        right = ''.join(w * c for w, c, _ in reversed(self.R))
        s = left + mid + right
        return s, len(left) + self.h

    def norm(self):
        s, hp = self.tape()
        a = len(s) - len(s.lstrip('0'))
        a = min(a, hp)
        s = s[a:]
        hp -= a
        b = len(s.rstrip('0'))
        b = max(b, hp + 1)
        return 'ABCDEF'[self.s], hp, s[:b]

    def tokens(self, side=None):
        """the tape as a run-length list (word, count) in tape order, buffer included as loose cells"""
        out = [(w, c) for w, c, _ in self.L] + [(str(x), 1) for x in self.buf] + [(w, c) for w, c, _ in reversed(self.R)]
        return out
