"""rsim: exact accelerated simulator for 2-symbol Turing machines whose tape is a list of repeated words.

Tape = left rope + buffer + right rope.  A rope is a stack of items [word, count] (word a str of 0/1 in tape order,
top of the stack nearest the buffer).  The head lives in the buffer (a list of cells), where plain steps are made.

When the head leaves the buffer it faces the top item (w, c) of a rope.  Three things can happen:
  * a learned *periodic rule* applies: from state s with the D cells behind the head equal to T, crossing P copies of w
    brings the head out the far side in state s with the same D cells behind it, never looking back further than D
    cells behind where each crossing started; then floor(c/P) periods are crossed at once, each leaving the same word O
    behind (exact, by induction on the copies);
  * a learned *transition rule* applies (one copy crossed, any exit state, lookback D);
  * otherwise one copy of w is unrolled into the buffer.
Rules are learned by running the machine on a scratch tape (trailing buffer + up to K copies).

On top of that, *samples* are taken at major left turns: the tape as a signature (loose text and words of long runs)
and the vector of run counts.  When the same signature comes back at equal spacing with equal count changes twice in a
row (and all signatures in between match), m periods are applied at once: counts += m*delta, steps by the arithmetic
series.  This level is validated against direct simulation, not proved (it assumes the period's behaviour depends on
the counts only through 'large enough' and their residues modulo the periods of the rules used).
"""
import sys
from math import gcd


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


_canon = {}


def canon(w):
    """(root word in its minimal rotation, copies of the root in w, offset r): w = (root')^k, min rotation = root'[r:]+root'[:r]"""
    c = _canon.get(w)
    if c is None:
        n = len(w)
        root = w
        for p in range(1, n // 2 + 1):
            if n % p == 0 and w[:p] * (n // p) == w:
                root = w[:p]
                break
        p = len(root)
        dd = root + root
        r = min(range(p), key=lambda i: dd[i:i + p])
        c = (dd[r:r + p], n // p, r)
        _canon[w] = c
    return c


_cmemo = {}


def compress(s):
    r = _cmemo.get(s)
    if r is None:
        r = compress0(s)
        if len(_cmemo) > 2000000:
            _cmemo.clear()
        _cmemo[s] = r
    return [x[:] for x in r]


def compress0(s):
    """two levels: short-period repeats in the string, then repeated groups of items"""
    items = compress1(s)
    n = len(items)
    if n < 3:
        return items
    out = []
    i = 0
    while i < n:
        hit = None
        for q in range(1, 7):
            if i + 3 * q > n:
                break
            g = items[i:i + q]
            r = 1
            while items[i + r * q:i + (r + 1) * q] == g:
                r += 1
            if r >= 3 and (q > 1 or g[0][1] == 1):
                hit = (q, r)
                break
        if hit:
            q, r = hit
            X = ''.join(w * c for w, c in items[i:i + q])
            W, k, o = canon(X)
            if o == 0:
                out.append([W, r * k])
            else:
                root = X[:len(W)]
                out.append([root[:o], 1])
                out.append([W, r * k - 1])
                out.append([root[o:], 1])
            i += q * r
        else:
            out.append(items[i])
            i += 1
    return out


def compress1(s, minrep=3, maxp=12, mincover=6):
    """split a string into items [word, count] (count 1 = loose) by greedy short-period repeats, words in minimal rotation"""
    out = []
    i = 0
    n = len(s)
    loose = 0
    while i < n:
        best = None
        for p in range(1, maxp + 1):
            if i + p * minrep > n:
                break
            w = s[i:i + p]
            r = 1
            while s.startswith(w, i + r * p):
                r += 1
            if r >= minrep and r * p >= mincover and (best is None or r * p > best[0]):
                best = (r * p, p, r)
        if best:
            _, p, r = best
            w, _k, o = canon(s[i:i + p])
            if o:
                i += o
                r = 1
                while s.startswith(w, i + r * p):
                    r += 1
            if r >= 2:
                if loose < i:
                    out.append([s[loose:i], 1])
                out.append([w, r])
                i += p * r
                loose = i
            else:
                i += 1
        else:
            i += 1
    if loose < n:
        out.append([s[loose:], 1])
    return out


class RSim:
    KEEP = 1024        # buffer cells kept on the far side before flushing
    TRAIL = 256        # trailing cells made available when learning
    TRAILMAX = 1024
    K = 10             # copies tried when learning a periodic rule
    SCRATCH_STEPS = 400000
    MARGIN = 8
    BIG = 8            # runs with at least this count are 'long' in signatures
    TRAVEL = 48        # leftward travel that makes a left turn a sample point

    def __init__(self, machine, jumps=True):
        self.m = machine
        self.T = parse(machine)
        self.L = []
        self.R = []
        self.buf = [0]
        self.h = 0
        self.base = 0          # absolute coordinate of buf[0]
        self.s = 0
        self.steps = 0
        self.rules = {}        # (s, dir, w) -> {D: {T: rule}}   transition rules
        self.prules = {}       # the same for periodic rules
        self.ptried = set()
        self.fail = set()
        self.jumps = jumps
        self.hist = {}
        self.samples = []
        self.lastdir = 1
        self.lastright = 0
        self.lastleft = 0
        self.lcm = 1
        self.njumps = 0
        self.jlog = None
        self.jumped = 0
        self.nsamp = 0
        self.nrule = 0
        self.nlearn = 0
        self.on_sample = None
        self.on_right_end = None
        self.halted = False

    # ---------------------------------------------------------------- ropes
    def _tidy(self, rope, left):
        """after appending to a rope: absorb completed copies into the run below, and turn three equal groups into a run"""
        while True:
            n = len(rope)
            done = True
            t = ''
            for i in range(1, min(n, 9)):
                it = rope[-i]
                if len(it[0]) * it[1] > 4000:
                    break
                piece = it[0] * it[1]
                t = piece + t if left else t + piece
                W = rope[-i - 1][0]
                if len(W) <= len(t) and W != it[0] and (t.startswith(W) if left else t.endswith(W)):
                    rest = t[len(W):] if left else t[:len(t) - len(W)]
                    del rope[-i:]
                    rope[-1][1] += 1
                    if rest:
                        for x in (compress(rest) if left else reversed(compress(rest))):
                            rope.append(x)
                    done = False
                    break
            if not done:
                continue
            for q in range(1, 7):
                if n >= 3 * q and rope[-q:] == rope[-2 * q:-q] == rope[-3 * q:-2 * q]:
                    grp = rope[-q:] if left else rope[-q:][::-1]
                    X = ''.join(w * c for w, c in grp)
                    if len(X) > 4000:
                        continue
                    del rope[-3 * q:]
                    self._pushrun(rope, left, X, 3)
                    done = False
                    break
            if done:
                return

    def _append(self, rope, left, it):
        if rope and rope[-1][0] == it[0]:
            rope[-1][1] += it[1]
        else:
            rope.append(it)

    def _pushstr(self, rope, left, s):
        if not rope:
            s = s.lstrip('0') if left else s.rstrip('0')      # the blank beyond the tape is never stored
        if not s:
            return
        items = compress(s)
        for it in (items if left else reversed(items)):
            self._append(rope, left, it)
        self._tidy(rope, left)

    def _pushrun(self, rope, left, O, J):
        """J copies of the word O (tape order) appended to the rope, as a run of the canonical rotation"""
        if J <= 0:
            return
        W, k, r = canon(O)
        p = len(W)
        if r == 0:
            self._append(rope, left, [W, J * k])
            self._tidy(rope, left)
            return
        root = O[:p]
        pre, post = root[:r], root[r:]
        if left:
            self._pushstr(rope, left, pre)
            if J * k > 1:
                self._append(rope, left, [W, J * k - 1])
            self._pushstr(rope, left, post)
        else:
            self._pushstr(rope, left, post)
            if J * k > 1:
                self._append(rope, left, [W, J * k - 1])
            self._pushstr(rope, left, pre)

    def pushR(self, s):
        """s (tape order) goes just left of the right rope"""
        self._pushstr(self.R, False, s)

    def pushL(self, s):
        self._pushstr(self.L, True, s)

    def pushrun(self, rope, w, c):
        self._pushrun(rope, rope is self.L, w, c)

    def flush(self):
        """keep the buffer small: push its far parts to the ropes"""
        buf = self.buf
        h = self.h
        if h > 2 * self.KEEP:
            cut = h - self.KEEP
            self.pushL(''.join(map(str, buf[:cut])))
            del buf[:cut]
            self.h -= cut
            self.base += cut
        if len(buf) - self.h > 2 * self.KEEP:
            cut = self.h + self.KEEP
            self.pushR(''.join(map(str, buf[cut:])))
            del buf[cut:]

    def flush_all(self):
        """everything left of the head to L, the rest to R (head then faces R, on the first cell of R)"""
        buf = self.buf
        h = self.h
        if h > 0:
            self.pushL(''.join(map(str, buf[:h])))
        if h < len(buf):
            self.pushR(''.join(map(str, buf[max(h, 0):])))
        self.base += h
        self.buf = []
        self.h = 0

    def ensure_behind(self, d, D):
        """at an edge moving in direction d, make sure the buffer holds at least D cells (pull from the rope behind)"""
        buf = self.buf
        while len(buf) < D:
            rope = self.R if d < 0 else self.L
            if not rope:
                add = [0] * 64
            else:
                it = rope[-1]
                add = [int(ch) for ch in it[0]]
                it[1] -= 1
                if it[1] == 0:
                    rope.pop()
            if d < 0:
                buf.extend(add)
            else:
                buf[0:0] = add
                self.h += len(add)
                self.base -= len(add)

    # ---------------------------------------------------------------- scratch learning
    def scratch(self, s, d, wf, tr, K):
        """Forward-oriented scratch run.  Tape: tr (trailing cells, nearest last) + K copies of wf, head on the first
        cell of the first copy; moves are multiplied by d (the caller mirrors the data for d < 0).
        Returns the records (state, steps, lookback D) of the boundaries 1..k reached, and the tapes at boundaries 0..k."""
        T = self.T
        lt = len(tr)
        lw = len(wf)
        arr = tr + wf * K
        pos = lt
        nextb = lt + lw
        lo = pos
        recs = []
        snaps = [arr[:]]
        steps = 0
        cap = self.SCRATCH_STEPS
        while steps < cap:
            if pos >= nextb:
                recs.append((s, steps, max(nextb - lw - lo, 0)))
                snaps.append(arr[:])
                if len(recs) == K:
                    break
                lo = pos
                nextb += lw
            if pos < 0:
                break
            t = T[s][arr[pos]]
            if t is None:
                break
            arr[pos] = t[0]
            pos += t[1] * d
            s = t[2]
            steps += 1
            if pos < lo:
                lo = pos
        return recs, snaps

    def learn(self, d, force=False):
        """at an edge moving in direction d, facing item (w, c): learn a rule for it, or return None"""
        rope = self.L if d < 0 else self.R
        w, c = rope[-1]
        s = self.s
        self.ensure_behind(d, self.TRAIL)
        buf = self.buf
        if d < 0:
            tr = buf[:self.TRAILMAX][::-1]
            wf = [int(ch) for ch in reversed(w)]
        else:
            tr = buf[-self.TRAILMAX:]
            wf = [int(ch) for ch in w]
        key = (s, d, w, bytes(tr[-128:]))
        if key in self.fail and not force:
            return None
        self.nlearn += 1
        K = min(c, self.K)
        recs, snaps = self.scratch(s, d, wf, tr, K)
        lt = len(tr)
        lw = len(wf)
        if not recs:
            self.fail.add(key)
            return None
        rule = None
        if len(recs) >= 2:
            states = [s] + [r[0] for r in recs]
            stp = [0] + [r[1] for r in recs]
            Ds = [r[2] for r in recs]
            found = None
            for i in range(0, len(recs)):
                for j in range(i + 1, len(recs) + 1):
                    if states[i] != states[j]:
                        continue
                    D = max(Ds[i:j])
                    bi = lt + i * lw
                    bj = lt + j * lw
                    if D > bi:
                        continue
                    if snaps[i][bi - D:bi] == snaps[j][bj - D:bj]:
                        found = (i, j, D)
                        break
                if found:
                    break
            if found:
                i, j, D = found
                P = j - i
                bi = lt + i * lw
                bj = lt + j * lw
                Tt = tuple(snaps[i][bi - D:bi])
                O = snaps[j][bi - D:bj - D]
                prule = ('P', D, Tt, P, O, stp[j] - stp[i])
                self.addrule(states[i], d, w, D, Tt, prule)
                if i == 0:
                    rule = prule
        if rule is None:
            s1, st1, D = recs[0]
            Tt = tuple(tr[lt - D:])
            out = snaps[1][lt - D:lt + lw]
            rule = ('T', D, Tt, s1, out, st1)
            self.addrule(s, d, w, D, Tt, rule)
        return rule

    def addrule(self, s, d, w, D, Tt, rule):
        tabs = self.prules if rule[0] == 'P' else self.rules
        tabs.setdefault((s, d, w), {}).setdefault(D, {})[Tt] = rule

    def lookup(self, tabs, d, w, c):
        byD = tabs.get((self.s, d, w))
        if byD:
            for D, tab in byD.items():
                buf = self.buf
                if len(buf) < D:
                    self.ensure_behind(d, D)
                    buf = self.buf
                if D == 0:
                    Tt = ()
                elif d < 0:
                    Tt = tuple(buf[D - 1::-1])
                else:
                    Tt = tuple(buf[len(buf) - D:])
                r = tab.get(Tt)
                if r is not None and (r[0] == 'T' or c >= r[3]):
                    return r
        return None

    def find(self, d):
        rope = self.L if d < 0 else self.R
        w, c = rope[-1]
        if c >= 2:
            r = self.lookup(self.prules, d, w, c)
            if r is not None:
                return r
        r = self.lookup(self.rules, d, w, c)
        if r is not None and c >= 2:
            key = (self.s, d, w, r[1], r[2])
            if key not in self.ptried:
                self.ptried.add(key)
                r2 = self.learn(d, force=True)
                if r2 is not None and r2[0] == 'P' and c >= r2[3]:
                    return r2
                # learning may have pulled cells into the buffer; the T rule still applies (same trailing cells)
        return r

    def apply(self, d, rule):
        """apply a rule at the edge in direction d"""
        rope = self.L if d < 0 else self.R
        it = rope[-1]
        w, c = it
        lw = len(w)
        buf = self.buf
        D = rule[1]
        self.nrule += 1
        if rule[0] == 'P':
            _, D, Tt, P, O, st = rule
            # flush what lies behind the D trailing cells
            if d < 0:
                if len(buf) > D:
                    self.pushR(''.join(map(str, buf[D:])))
                    del buf[D:]
            else:
                if len(buf) > D:
                    cut = len(buf) - D
                    self.pushL(''.join(map(str, buf[:cut])))
                    del buf[:cut]
                    self.base += cut
            J = c // P
            if d < 0:
                self.pushrun(self.R, ''.join(map(str, reversed(O))), J)
                self.base -= J * P * lw
                self.h = -1
            else:
                self.pushrun(self.L, ''.join(map(str, O)), J)
                self.base += J * P * lw
                self.h = len(buf)
            self.steps += J * st
            it[1] -= J * P
            if it[1] == 0:
                rope.pop()
            if P > 1:
                self.lcm = self.lcm * P // gcd(self.lcm, P)
        else:
            _, D, Tt, s1, out, st = rule
            if d < 0:
                buf[:D] = out[::-1]
                self.base -= lw
                self.h = -1
            else:
                if D:
                    del buf[len(buf) - D:]
                buf.extend(out)
                self.h = len(buf)
            self.s = s1
            self.steps += st
            it[1] -= 1
            if it[1] == 0:
                rope.pop()

    # ---------------------------------------------------------------- edges
    def edge(self, d):
        """the head left the buffer in direction d.  Returns after making the next cell available or crossing items."""
        rope = self.L if d < 0 else self.R
        # sample points: a right edge after left edges
        if d != self.lastdir:
            if d > 0:
                if self.jumps and self.lastright - self.lastleft >= self.TRAVEL:
                    self.sample()
                    rope = self.R
            self.lastdir = d
        if d > 0:
            self.lastright = self.base + self.h
        else:
            self.lastleft = self.base + self.h
        if d > 0 and self.on_right_end and not any('1' in it[0] for it in rope):
            self.on_right_end(self)
            rope = self.R
        if not rope:
            if d < 0:
                self.buf[0:0] = [0] * 64
                self.h += 64
                self.base -= 64
            else:
                self.buf.extend([0] * 64)
            return
        rule = self.find(d)
        if rule is None:
            rule = self.learn(d)
            if rule is not None and rule[0] == 'P' and rope[-1][1] < rule[3]:
                rule = None
            if rule is not None:
                # make sure the trailing cells are those of the rule (learn used the whole buffer)
                pass
        if rule is not None:
            self.apply(d, rule)
            return
        # unroll one copy
        it = rope[-1]
        add = [int(ch) for ch in it[0]]
        it[1] -= 1
        if it[1] == 0:
            rope.pop()
        if d < 0:
            self.buf[0:0] = add
            self.h += len(add)
            self.base -= len(add)
        else:
            self.buf.extend(add)

    # ---------------------------------------------------------------- run
    def run(self, maxsteps):
        T = self.T
        while self.steps < maxsteps:
            buf = self.buf
            h = self.h
            s = self.s
            n = len(buf)
            k = 0
            lim = maxsteps - self.steps
            if lim > 200000:
                lim = 200000
            while 0 <= h < n and k < lim:
                t = T[s][buf[h]]
                if t is None:
                    self.h = h
                    self.s = s
                    self.steps += k + 1
                    self.halted = True
                    raise Halt()
                buf[h] = t[0]
                h += t[1]
                s = t[2]
                k += 1
            self.h = h
            self.s = s
            self.steps += k
            if h < 0:
                self.edge(-1)
            elif h >= n:
                self.edge(1)
            if len(self.buf) > 4 * self.KEEP:
                self.flush()

    # ---------------------------------------------------------------- samples and jumps
    def items(self):
        """the whole tape as a list of items in tape order (buffer flushed)"""
        self.flush_all()
        return self.L + self.R[::-1]

    def signature(self):
        self.flush_all()
        sig = []
        refs = []
        counts = []
        loose = []
        Ls = self.L
        a = 0
        while a < len(Ls) and '1' not in Ls[a][0]:
            a += 1
        Rs = self.R[::-1]
        b = len(Rs)
        while b > 0 and '1' not in Rs[b - 1][0]:
            b -= 1
        for part, rope in ((0, Ls[a:]), (1, Rs[:b])):
            for it in rope:
                if it[1] >= self.BIG:
                    if loose:
                        sig.append(''.join(loose))
                        loose = []
                    sig.append((it[0],))
                    refs.append(it)
                    counts.append(it[1])
                else:
                    loose.append(it[0] * it[1])
            if loose:
                sig.append(''.join(loose))
                loose = []
            if part == 0:
                sig.append(('HEAD', self.s))
        return hash(tuple(sig)), refs, counts

    def sample(self):
        sig, refs, counts = self.signature()
        idx = len(self.samples)
        self.nsamp += 1
        self.samples.append((sig, counts, self.steps, self.lcm))
        self.lcm = 1
        if self.on_sample:
            self.on_sample(self)
        prev = self.hist.setdefault(sig, [])
        prev.append(idx)
        S = self.samples
        tried = 0
        for i in prev[-2:-200:-1]:
            P = idx - i
            if idx - 2 * P < 0:
                break
            if S[idx - 2 * P][0] != sig:
                continue
            tried += 1
            if tried > 12:
                break
            if self.tryjump(idx, P, sig, refs, counts):
                return

    def tryjump(self, idx, P, sig, refs, counts):
        S = self.samples
        if idx - 2 * P < 0 or S[idx - 2 * P][0] != sig or len(S[idx - P][1]) != len(counts):
            return False
        d = [b - a for a, b in zip(S[idx - P][1], counts)]
        if not any(d):
            return False
        # n periods must agree, n = lcm of the rule periods used in them + 1 (see the module docstring)
        n = 2
        while True:
            if idx - n * P < 0:
                return False
            lc = 1
            for t in range(n * P):
                l = S[idx - t][3]
                lc = lc * l // gcd(lc, l)
            if lc + 1 <= n:
                break
            n = lc + 1
        for t in range(1, n + 1):
            i0 = idx - t * P
            if S[i0][0] != sig or len(S[i0][1]) != len(counts):
                return False
            if [b - a for a, b in zip(S[i0][1], S[i0 + P][1])] != d:
                return False
        for t in range(P):
            for u in range(1, n):
                if S[idx - t][0] != S[idx - t - u * P][0]:
                    return False
        e = [S[idx - t * P][2] - S[idx - (t + 1) * P][2] for t in range(n)]      # e[0] = latest period
        f = [e[t] - e[t + 1] for t in range(n - 1)]
        if any(x != f[0] for x in f):
            return False
        J = None
        lim = None
        for c, x, it in zip(counts, d, refs):
            if x < 0:
                j = (c - self.MARGIN - 2 * lc) // (-x)
                if J is None or j < J:
                    J = j
                    lim = (it[0][:40], c, x)
        if self.jlog is not None:
            self.jlog.append((self.steps, J, P, n, lim))
        if J is not None and J >= 2:
            for it, x in zip(refs, d):
                it[1] += J * x
            self.steps += J * e[0] + f[0] * J * (J + 1) // 2
            self.njumps += 1
            self.jumped += J * P
            self.hist = {}
            self.samples = []
            return True
        return False

    def tape(self):
        """(string of the tape between the outermost nonzero cells, head offset in it, state) -- expands everything"""
        left = ''.join(w * c for w, c in self.L)
        mid = ''.join(map(str, self.buf))
        right = ''.join(w * c for w, c in reversed(self.R))
        s = left + mid + right
        hp = len(left) + self.h
        a = len(s) - len(s.lstrip('0'))
        a = min(a, hp) if hp >= 0 else 0
        return s, hp


def direct(m, nsteps):
    T = parse(m)
    tape = {}
    pos = 0
    s = 0
    for k in range(nsteps):
        t = T[s][tape.get(pos, 0)]
        if t is None:
            return None
        tape[pos] = t[0]
        pos += t[1]
        s = t[2]
    return tape, pos, s


def norm(tape_str, hp):
    """strip zeros, return (stripped string, head offset)"""
    l = len(tape_str) - len(tape_str.lstrip('0'))
    r = tape_str.rstrip('0')
    return r[l:], hp - l


if __name__ == '__main__':
    m = sys.argv[1]
    n = int(float(sys.argv[2]))
    sim = RSim(m, jumps=len(sys.argv) < 4)
    try:
        sim.run(n)
        print('running', sim.steps)
    except Halt:
        print('halted', sim.steps)
    print('rules applied', sim.nrule, 'learn calls', sim.nlearn, 'jumps', sim.njumps)
