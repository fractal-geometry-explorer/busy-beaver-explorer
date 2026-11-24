"""The macro machine of py/mac14.py on a run-length list, so that a sweep costs O(1) instead of O(len).

The list L = [N, s1, v1, ...] of mac14 is split at the window i:
  left  = units [v, c] meaning c copies of `v D` (D = '. 0 ! 1 .'); left[0] = [N, 1] is the fuel.
          Empty when the window is the fuel itself (i = 0, "own" mode).
  right = the list from the window on, reversed (top = window), whose items are raw tokens
          (int, '.', '!') or runs ('R', v, c) = c copies of `v D`.
`Map.step()` does exactly what mac14.step does; `Map.fast()` what mac14.fast does.
"""
D = ['.', 0, '!', 1, '.']
TAIL = [1, '!', 0]
DR = D[::-1]


class Unknown(Exception):
    pass


class Map:
    def __init__(self, L):
        self.left = []
        self.R = []
        self.rlen = 0
        for t in reversed(L):
            self.R.append(t)
        self.rlen = len(L)
        self.sweeps = 0
        self.rules = {}
        self.log = None
        self.jumps = 0
        self.normalize()

    # ---- right part ---------------------------------------------------------
    def ensure(self, k):
        """Make the top k tokens of the right part raw, padding with blank if it is shorter."""
        R = self.R
        while True:
            # find first run among the top k items
            n = 0
            j = len(R) - 1
            ok = True
            while n < k and j >= 0:
                it = R[j]
                if type(it) is tuple:
                    ok = False
                    break
                n += 1
                j -= 1
            if ok:
                break
            _, v, c = R[j]
            if c > 1:
                R[j:j + 1] = [('R', v, c - 1)] + DR + [v]
            else:
                R[j:j + 1] = DR + [v]
        if self.rlen < k:
            pad = []
            for p in range(self.rlen, k if k % 2 else k + 1):
                pad.append('.' if p % 2 else 0)
            R[0:0] = pad[::-1]
            self.rlen += len(pad)

    def g(self, t):
        if t >= self.rlen:
            return '.' if t % 2 else 0
        self.ensure(t + 1)
        return self.R[-1 - t]

    def rep(self, k, new):
        self.ensure(k)
        del self.R[len(self.R) - k:]
        self.R.extend(reversed(new))
        self.rlen += len(new) - k

    def trim(self):
        R = self.R
        while True:
            if len(R) >= 2 and type(R[0]) is not tuple and type(R[1]) is not tuple and R[0] == 0 and R[1] == '.' and self.total_len() >= 3:
                del R[0:2]
                self.rlen -= 2
            else:
                break

    def total_len(self):
        return 6 * sum(c for _, c in self.left) + self.rlen

    def right_is_tail_after_block(self):
        """right part is exactly `v D TAIL` (the append window)."""
        if self.rlen != 9:
            return False
        self.ensure(9)
        return self.R[-2:-7:-1] == D and self.R[0:3] == TAIL[::-1]

    # ---- window -------------------------------------------------------------
    def normalize(self):
        """Move done blocks (v D followed by more, not exactly TAIL) from the right part to the left."""
        R = self.R
        while True:
            if not R:
                return
            top = R[-1]
            if type(top) is tuple:
                _, v, c = top
                rest = self.rlen - 6 * c
                if rest == 3:
                    # run then TAIL? check
                    if R[0:3] == TAIL[::-1] and len(R) == 4:
                        if c == 1:
                            return
                        R[-1] = ('R', v, 1)
                        self.rlen -= 6 * (c - 1)
                        self.push_left(v, c - 1)
                        continue
                if rest == 0:
                    # run is the end: last block v D then blank -> i+6<len fails for last
                    if c == 1:
                        self.ensure(6)
                        return
                    R[-1] = ('R', v, 1)
                    self.rlen -= 6 * (c - 1)
                    self.push_left(v, c - 1)
                    continue
                R.pop()
                self.rlen -= 6 * c
                self.push_left(v, c)
                continue
            # raw window value
            if self.rlen <= 6:
                return
            self.ensure(6)
            if R[-2:-7:-1] != D:
                return
            if self.right_is_tail_after_block():
                return
            v = R[-1]
            del R[-6:]
            self.rlen -= 6
            self.push_left(v, 1)

    def push_left(self, v, c):
        L = self.left
        if self.log is not None:
            self.log.append((v, c))
        if not L:
            L.append([v, 1])
            c -= 1
            if c == 0:
                return
        if len(L) >= 2 and L[-1][0] == v:
            L[-1][1] += c
        else:
            L.append([v, c])

    def fuel(self):
        if self.left:
            return self.left[0][0]
        return self.g(0)

    def set_fuel(self, n):
        if self.left:
            self.left[0][0] = n
        else:
            self.ensure(1)
            self.R[-1] = n

    def fuel_followed_by_D(self):
        """L[1:6] == D"""
        if self.left:
            return True
        if self.rlen < 6:
            return False
        self.ensure(6)
        return self.R[-2:-7:-1] == D

    def drop_fuel_block(self):
        """L = L[6:]"""
        if self.left:
            self.left.pop(0)
            if self.left and self.left[0][1] > 1:
                v, c = self.left[0]
                self.left[0:1] = [[v, 1], [v, c - 1]]
        else:
            self.ensure(6)
            del self.R[-6:]
            self.rlen -= 6

    def to_own(self):
        """Move the whole left part (without the fuel) back to the right part; window becomes i=0."""
        L = self.left
        n = L[0][0]
        for v, c in reversed(L[1:]):
            self.R.append(('R', v, c))
            self.rlen += 6 * c
        self.left = []
        return n

    # ---- one sweep ------------------------------------------------------------
    def apply_rule(self):
        """Apply the window rule (no fuel change). Returns (rule, i_is_zero, kind)."""
        self.normalize()
        own = not self.left
        g = self.g
        x = g(0)
        if self.right_is_tail_after_block():
            self.rep(9, [x] + D + [2] + D + TAIL)
            return 'append', own, 'append'
        if not own and [g(t) for t in range(1, 8)] == ['.', 0, '!', 0, '!', 1, '.'] and type(g(8)) is int:
            # fold: `x . 0 ! 0 ! 1 . z` is read as the single value x+3+z, and the sweep goes on
            z = g(8)
            self.rep(9, [x + 3 + z])
            r2, own2, kind2 = self.apply_rule()
            return 'fold+' + r2, False, kind2
        if not own and g(1) == '!' and g(2) == 0 and g(3) == '.' and type(g(4)) is int and 4 < self.rlen - 1:
            # fold2: `x ! 0 . z` (not at the end) is read as the single value x+1+z
            z = g(4)
            self.rep(5, [x + 1 + z])
            r2, own2, kind2 = self.apply_rule()
            return 'fold2+' + r2, False, kind2
        s, y, n = g(1), g(2), g(3)
        if y >= 2:
            self.rep(3, [x + 4, '!' if s == '.' else '.', y - 1]); rule = 'pair'
        elif y == 1 and s == '!' and n == '.': self.rep(3, [x + 4, '.', 0]); rule = 'p1!.'
        elif y == 1 and s == '.' and n == '.': self.rep(5, [x + 5 + g(4)]); rule = 'p1..'
        elif y == 1 and s == '.' and n == '!': self.rep(3, [x + 4, '!', 0]); rule = 'p1.!'
        elif y == 1 and s == '!' and n == '!': self.rep(3, [x + 4, '.', 0]); rule = 'p1!!'
        elif y == 0 and s == '.' and n == '.' and g(4) == 0 and g(5) == '.' and g(6) == 0 and g(7) == '!' and g(8) == 1 and g(9) == '.' and 10 < self.rlen:
            self.rep(10, [x] + D + [2, '!', 1, '.']); rule = 'restart2'
        elif y == 0 and s == '.' and n == '.': self.rep(5, [x] + D + [1, '!', g(4)]); rule = 'next'
        elif y == 0 and s == '!' and n == '!' and g(5) == '.': self.rep(6, [x + 4 + g(4), '.']); rule = 'merge!'
        elif y == 0 and s == '!' and n == '!' and g(5) == '!' and 5 < self.rlen - 1: self.rep(6, [x + 4 + g(4), '!']); rule = 'merge!!'
        elif y == 0 and s == '.' and n == '!' and type(g(4)) is int and g(4) >= 2: self.rep(5, [x] + D + [3, '.', g(4) - 2]); rule = 'mid.!'
        elif y == 0 and s == '.' and n == '!' and g(4) == 0 and 4 >= self.rlen - 1: self.rep(5, [x + 4, '!', 0]); rule = 'end.!'
        elif y == 0 and s == '!' and n == '.' and 2 >= self.rlen - 1: self.rep(3, [x + 1] + D + TAIL); rule = 'end!'
        elif y == 0 and s == '.' and n == '!' and g(4) == 0 and g(5) == '.' and type(g(6)) is int and g(6) >= 1: self.rep(7, [x + 4, '!', g(6)]); rule = 'mid0.'
        elif y == 0 and s == '.' and n == '!' and g(4) == 0 and g(5) == '!' and type(g(6)) is int and g(6) >= 2: self.rep(7, [x + 6, '.', g(6) - 2]); rule = 'mid0!'
        else:
            raise Unknown(self.window_str())
        return rule, own, None

    def window_str(self):
        self.ensure(min(12, self.rlen))
        return str(self.R[-1:-13:-1])

    def step(self):
        N0 = self.fuel()
        rule, own, kind = self.apply_rule()
        self.trim()
        if own and kind != 'append':
            n = self.fuel() - 2
            if n < 0:
                raise Unknown('N<0 own')
            self.set_fuel(n)
        elif N0 == 0:
            self.normalize()
            if not self.fuel_followed_by_D():
                raise Unknown('N0')
            self.normalize()
            if self.left:
                self.to_own()
            else:
                self.ensure(6); del self.R[-6:]; self.rlen -= 6
            # L = [2, '.'] + L[6:]
            self.R.append('.'); self.R.append(2); self.rlen += 2
        elif N0 == 1:
            self.normalize()
            if not self.fuel_followed_by_D():
                raise Unknown('N1')
            r2, _, _ = self.apply_rule()
            self.trim()
            self.normalize()
            if not self.fuel_followed_by_D():
                raise Unknown('N1b')
            self.drop_fuel_block()
            rule = rule + '+' + r2 + '/N1'
        else:
            self.normalize()
            n = self.fuel() - 2
            if n < 0:
                raise Unknown('N<0')
            self.set_fuel(n)
        self.trim()
        self.normalize()
        self.sweeps += 1
        self.rules[rule] = self.rules.get(rule, 0) + 1
        return rule

    def fast(self):
        """Like mac14.fast: several sweeps at once for pair runs and appends. Returns number of sweeps."""
        self.normalize()
        N0 = self.fuel()
        if N0 >= 4:
            own = not self.left
            if self.right_is_tail_after_block():
                k = N0 // 2 - 1
                if k >= 1:
                    x = self.g(0)
                    self.ensure(9)
                    del self.R[-9:]
                    self.R.extend(TAIL[::-1]); self.R.append(('R', 2, k)); self.R.extend(DR); self.R.append(x)
                    self.rlen += 6 * k
                    self.set_fuel(N0 - 2 * k)
                    self.normalize()
                    self.sweeps += k
                    self.rules['append'] = self.rules.get('append', 0) + k
                    return k
            else:
                s, y = self.g(1), self.g(2)
                if s in '.!' and type(y) is int and y >= 3:
                    k = y - 2 if own else min(y - 2, N0 // 2 - 1)
                    if k >= 1:
                        R = self.R
                        R[-1] += 4 * k
                        R[-3] -= k
                        if k % 2:
                            R[-2] = '!' if s == '.' else '.'
                        if own:
                            R[-1] -= 2 * k
                        else:
                            self.set_fuel(N0 - 2 * k)
                        self.normalize()
                        self.sweeps += k
                        self.rules['pair'] = self.rules.get('pair', 0) + k
                        return k
        self.step()
        return 1

    # ---- export ---------------------------------------------------------------
    def to_list(self):
        out = []
        for v, c in self.left:
            out += ([v] + D) * c
        for it in reversed(self.R):
            if type(it) is tuple:
                out += ([it[1]] + D) * it[2]
            else:
                out.append(it)
        while len(out) >= 3 and out[-1] == 0 and out[-2] == '.':
            out = out[:-2]
        return out


START = [0, '.', 0, '!', 1, '.', 1, '!', 0]


def compact_top(M):
    """Fold raw `v D` tokens sitting directly above a run ('R', v, c) back into the run."""
    R = M.R
    while True:
        j = len(R) - 1
        # find the topmost run
        while j >= 0 and type(R[j]) is not tuple:
            j -= 1
        if j < 0 or len(R) - 1 - j < 6 + 2:
            return
        _, v, c = R[j]
        blk = R[j + 1:j + 7]
        if blk == DR + [v] and True:
            R[j:j + 7] = [('R', v, c + 1)]
        else:
            return


def sig(M):
    R = M.R
    if not M.left or len(R) < 3:
        return None
    if type(R[-1]) is int and R[-2] in ('.', '!') and type(R[-3]) is tuple:
        return (R[-1], R[-2], R[-3][1])
    return None


def jump(M, maxit=400):
    """If the window stands before a run of equal blocks, cross one block by plain fast(), and when the
    window comes back to the same pattern in front of the shorter run, cross many more at once.
    Returns sweeps done (0 if not applicable)."""
    compact_top(M)
    s0 = sig(M)
    if s0 is None:
        return 0
    c0 = M.R[-3][2]
    if c0 < 8:
        return 0
    F0 = M.fuel()
    sw0 = M.sweeps
    M.log = []
    rules0 = dict(M.rules)
    it = 0
    ok = False
    while it < maxit:
        M.fast(); it += 1
        if M.fuel() < 8 or not M.left:
            break
        compact_top(M)
        if sig(M) == s0:
            ok = M.R[-3][2] == c0 - 1
            break
    log = M.log
    M.log = None
    if not ok:
        return M.sweeps - sw0
    dF = F0 - M.fuel()
    dS = M.sweeps - sw0
    F = M.fuel()
    m = min(M.R[-3][2] - 4, (F - 8) // dF - 1)
    if m < 1:
        return dS
    _, v, c = M.R[-3]
    M.R[-3] = ('R', v, c - m)
    M.rlen -= 6 * m
    M.set_fuel(F - m * dF)
    # emitted done blocks, m more times
    if len(log) == 1 or all(u == log[0][0] for u, _ in log):
        tot = sum(k for _, k in log)
        M.push_left(log[0][0], tot * m)
    else:
        for _ in range(m):
            for u, k in log:
                M.push_left(u, k)
    M.sweeps += m * dS
    for r, n in M.rules.items():
        d = n - rules0.get(r, 0)
        if d:
            M.rules[r] = n + m * d
    M.jumps += 1
    return dS * (m + 1)


def show(M, width=400):
    """Compressed picture: `v|` a block v D, `vxc|` a run of c of them, other tokens raw."""
    parts = []
    for v, c in M.left:
        parts.append(f"{v}x{c}|" if c > 1 else f"{v}|")
    parts.append('#')
    for it in reversed(M.R):
        if type(it) is tuple:
            parts.append(f"{it[1]}x{it[2]}|" if it[2] > 1 else f"{it[1]}|")
        else:
            parts.append(str(it))
    s = ' '.join(parts)
    # merge raw "v . 0 ! 1 ." into v|
    s = s.replace('. 0 ! 1 .', '|')
    return s if len(s) <= width else s[:width] + ' ...'


def canon_rle(M):
    """The whole list as a run-length token list: ('B', v, c) for c >= 1 copies of `v D`, else raw tokens."""
    toks = []
    for v, c in M.left:
        toks.append(('B', v, c))
    for it in reversed(M.R):
        if type(it) is tuple:
            toks.append(('B', it[1], it[2]))
        else:
            toks.append(it)
    # fold raw "v D" into blocks, then merge equal neighbours (keep the fuel block separate)
    out = []
    i = 0
    while i < len(toks):
        t = toks[i]
        if type(t) is int and toks[i + 1:i + 6] == D:
            t = ('B', t, 1); i += 6
        else:
            i += 1
        if type(t) is tuple and len(out) >= 2 and type(out[-1]) is tuple and out[-1][1] == t[1]:
            out[-1] = ('B', t[1], out[-1][2] + t[2])
        else:
            out.append(t)
    return out
