"""Segment simulator: tape as bits and Rep(word, n); long repeats crossed by two-sided shift rules found on the fly.
Exact: step counts are ordinary transitions (bbchallenge count minus the halting one)."""
import sys
def parse(M):
    T = []
    for g in M.split('_'):
        row = []
        for r in (0, 1):
            t = g[3*r:3*r+3]
            row.append(None if t[2] == '-' or not ('A' <= t[2] <= 'Z') else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65))
        T.append(row)
    return T

class Rep:
    __slots__ = ('w', 'n')
    def __init__(self, w, n): self.w = w; self.n = n
    def __repr__(self): return '(' + ''.join(map(str, self.w)) + ')^' + str(self.n)

class Halt(Exception): pass

class Sim:
    MAXC = 1500
    def __init__(self, M, K=10, K2=40):
        self.T = parse(M); self.K = K; self.K2 = K2
        self.left = []   # far .. near
        self.right = []  # near .. far
        self.q = 0; self.steps = 0
        self.cache = {}
        self.ncross = 0

    # one copy test, rightward: [L] u1 q> u2 w [R]  ->  [L] v u1 q> u2 [R]
    def one_r(self, q, u1, u2, w):
        key = ('r', q, u1, u2, w)
        if key in self.cache: return self.cache[key]
        T = self.T
        tape = list(u1) + list(u2) + list(w); h = len(u1); s = q; res = None
        n = 0
        while n < self.MAXC:
            if h < 0 or h >= len(tape): break
            t = T[s][tape[h]]
            if t is None: break
            tape[h] = t[0]; h += t[1]; s = t[2]; n += 1
            if s == q and h == len(u1) + len(w) and tuple(tape[len(w):len(w)+len(u1)]) == u1 and tuple(tape[len(w)+len(u1):]) == u2:
                res = (tuple(tape[:len(w)]), n); break
        self.cache[key] = res
        return res

    # leftward: [L] w u1 q> u2 [R] -> [L] u1 q> u2 v [R]
    def one_l(self, q, u1, u2, w):
        key = ('l', q, u1, u2, w)
        if key in self.cache: return self.cache[key]
        T = self.T
        tape = list(w) + list(u1) + list(u2); h = len(w) + len(u1); s = q; res = None
        n = 0
        while n < self.MAXC:
            if h < 0 or h >= len(tape): break
            t = T[s][tape[h]]
            if t is None: break
            tape[h] = t[0]; h += t[1]; s = t[2]; n += 1
            if s == q and h == len(u1) and tuple(tape[:len(u1)]) == u1 and tuple(tape[len(u1):len(u1)+len(u2)]) == u2:
                res = (tuple(tape[len(u1)+len(u2):]), n); break
        self.cache[key] = res
        return res

    def try_cross(self):
        if self._try_cross(1, self.K): return True
        return self._try_cross(2, self.K2)

    def _try_cross(self, mult, K):
        L, R = self.left, self.right
        j = 0
        while j < len(R) and j <= self.K and not isinstance(R[j], Rep): j += 1
        if j < len(R) and j <= self.K and isinstance(R[j], Rep) and R[j].n >= mult:
            rep = R[j]; u2 = tuple(R[:j]); w = rep.w * mult
            nb = 0
            while nb < len(L) and nb < K and not isinstance(L[-1-nb], Rep): nb += 1
            for l1 in range(0, nb + 1):
                u1 = tuple(L[len(L)-l1:]) if l1 else ()
                r = self.one_r(self.q, u1, u2, w)
                if r:
                    v, s = r
                    cnt = rep.n // mult
                    del L[len(L)-l1:]
                    self.push_left_rep(v, cnt)
                    L.extend(u1)
                    if rep.n - cnt * mult:
                        rep.n -= cnt * mult; del R[:j]
                    else:
                        del R[:j+1]
                    R[0:0] = list(u2)
                    self.steps += s * cnt; self.ncross += 1; self.lastdir = 'r'; self.lastn = cnt * mult
                    return True
        j = 0
        while j < len(L) and j <= self.K and not isinstance(L[-1-j], Rep): j += 1
        if j < len(L) and j <= self.K and isinstance(L[-1-j], Rep) and L[-1-j].n >= mult:
            rep = L[-1-j]; u1 = tuple(L[len(L)-j:]) if j else (); w = rep.w * mult
            nb = 0
            while nb < len(R) and nb < K and not isinstance(R[nb], Rep): nb += 1
            for l2 in range(0, nb + 1):
                u2 = tuple(R[:l2])
                r = self.one_l(self.q, u1, u2, w)
                if r:
                    v, s = r
                    cnt = rep.n // mult
                    if rep.n - cnt * mult:
                        rep.n -= cnt * mult; del L[len(L)-j:]
                    else:
                        del L[len(L)-j-1:]
                    L.extend(u1)
                    del R[:l2]
                    self.push_right_rep(v, cnt)
                    R[0:0] = list(u2)
                    self.steps += s * cnt; self.ncross += 1; self.lastdir = 'l'; self.lastn = cnt * mult
                    return True
        return False

    def push_left_rep(self, v, n):
        L = self.left
        if L and isinstance(L[-1], Rep) and L[-1].w == v: L[-1].n += n
        else: L.append(Rep(v, n))
    def push_right_rep(self, v, n):
        R = self.right
        if R and isinstance(R[0], Rep) and R[0].w == v: R[0].n += n
        else: R.insert(0, Rep(v, n))

    def compress(self, minrep=3):
        """absorb literal copies next to reps; make new reps from long literal periodic runs (words of the given lengths)."""
        for side in (self.left, self.right):
            self._absorb(side)
        self._rotate_away()

    def _rotate_away(self):
        """Re-bracket reps so that literal cells between the head and a rep move to the far side of the rep."""
        R = self.right
        for i in range(len(R)):
            t = R[i]
            if isinstance(t, Rep):
                w = t.w; k = len(w)
                j = i
                while j > 0 and not isinstance(R[j-1], Rep) and i - j + 1 < k: j -= 1
                # bits R[j:i] closest to rep; find longest z = R[i-m:i] that is a suffix of w
                best = 0
                for m in range(min(i - j, k - 1), 0, -1):
                    if tuple(R[i-m:i]) == w[k-m:]: best = m; break
                if best:
                    z = list(R[i-best:i]); y = w[:k-best]
                    R[i-best:i+1] = [Rep(tuple(z) + y, t.n)] + z
                    return self._rotate_away()
        L = self.left
        for i in range(len(L)):
            t = L[i]
            if isinstance(t, Rep):
                w = t.w; k = len(w)
                j = i
                while j + 1 < len(L) and not isinstance(L[j+1], Rep) and j - i + 1 < k: j += 1
                best = 0
                for m in range(min(j - i, k - 1), 0, -1):
                    if tuple(L[i+1:i+1+m]) == w[:m]: best = m; break
                if best:
                    z = list(L[i+1:i+1+best]); y = w[best:]
                    L[i:i+1+best] = z + [Rep(y + tuple(z), t.n)]
                    return self._rotate_away()

    def _absorb(self, S):
        i = 0
        while i < len(S):
            t = S[i]
            if isinstance(t, Rep):
                w = t.w; k = len(w)
                # bits after (index increasing)
                while i + k < len(S) + 0 and all(not isinstance(x, Rep) for x in S[i+1:i+1+k]) and tuple(S[i+1:i+1+k]) == w:
                    del S[i+1:i+1+k]; t.n += 1
                while i - k >= 0 and all(not isinstance(x, Rep) for x in S[i-k:i]) and tuple(S[i-k:i]) == w:
                    del S[i-k:i]; i -= k; t.n += 1
                if i + 1 < len(S) and isinstance(S[i+1], Rep) and S[i+1].w == w:
                    t.n += S[i+1].n; del S[i+1]; continue
            i += 1

    def make_reps(self, words, minrep=4):
        """replace literal runs of >= minrep copies of a word by a Rep (both sides)."""
        minlen = min(len(w) for w in words) * minrep
        for S in (self.left, self.right):
            i = 0
            while i < len(S):
                if isinstance(S[i], Rep): i += 1; continue
                j = i
                while j < len(S) and not isinstance(S[j], Rep): j += 1
                if j - i >= minlen:
                    seg = S[i:j]; out = self._compress_lit(seg, words, minrep)
                    if out is not None:
                        S[i:j] = out; i += len(out); continue
                i = j
        self._absorb(self.left); self._absorb(self.right)

    @staticmethod
    def _compress_lit(seg, words, minrep):
        import re
        st = ''.join(map(str, seg)); best = None
        for w in words:
            ws = ''.join(map(str, w))
            for m in re.finditer('(?:' + ws + '){%d,}' % minrep, st):
                L = m.end() - m.start()
                if best is None or L > best[1] - best[0]:
                    best = (m.start(), m.end(), w)
        if best is None: return None
        p, e, w = best
        left = Sim._compress_lit(seg[:p], words, minrep) if p >= minrep * len(words[-1]) else None
        right = Sim._compress_lit(seg[e:], words, minrep) if len(seg) - e >= minrep * len(words[-1]) else None
        return (left if left is not None else list(seg[:p])) + [Rep(w, (e - p) // len(w))] + (right if right is not None else list(seg[e:]))

    def step(self):
        L, R = self.left, self.right
        if not R: R.append(0)
        x = R[0]
        if isinstance(x, Rep):
            if x.n > 1: x.n -= 1; R[0:0] = list(x.w)
            else: R[0:1] = list(x.w)
            x = R[0]
        t = self.T[self.q][x]
        if t is None: raise Halt()
        if t[1] == 1:
            R.pop(0); L.append(t[0])
        else:
            R[0] = t[0]
            if not L: L.append(0)
            y = L[-1]
            if isinstance(y, Rep):
                if y.n > 1: y.n -= 1; L.extend(y.w)
                else: L[-1:] = list(y.w)
            R.insert(0, L.pop())
        self.q = t[2]; self.steps += 1

    def tape_str(self):
        f = lambda t: ''.join(map(str, t.w)) * t.n if isinstance(t, Rep) else str(t)
        return ''.join(map(f, self.left)), 'ABCDEFGH'[self.q], ''.join(map(f, self.right))

    def show(self, maxbits=60):
        def side(S):
            out = []; buf = ''
            for t in S:
                if isinstance(t, Rep):
                    if buf: out.append(buf); buf = ''
                    out.append(repr(t))
                else: buf += str(t)
            if buf: out.append(buf)
            return ' '.join(o if len(o) <= maxbits else o[:maxbits//2] + '..' + o[-maxbits//2:] for o in out)
        return side(self.left) + ' ' + 'ABCDEFGH'[self.q] + '> ' + side(self.right)
