"""Cycle acceleration on top of segsim: at sample points (each long leftward cross), when the configuration has the
same shape at t, t-p, t-2p, t-3p with counts moving by constant deltas and steps by a constant second difference,
jump k periods at once."""
import sys; sys.path.insert(0, __import__("os").path.dirname(__file__))
from segsim import Sim, Rep, Halt

class Accel:
    def __init__(self, M, words, big=40, maxp=48, margin=4):
        self.s = Sim(M); self.words = sorted({tuple(map(int, w[i:] + w[:i])) for w in words for i in range(len(w))}, key=lambda w: -len(w))
        self.big = big; self.maxp = maxp; self.margin = margin
        self.hist = []; self.jumps = 0; self.it = 0
        self.on_sample = None

    def snapshot(self):
        s = self.s
        toks = s.left + ['H%d' % s.q] + s.right
        shape = tuple(('R', t.w) if isinstance(t, Rep) else t for t in toks)
        counts = [t.n for t in toks if isinstance(t, Rep)]
        return shape, counts

    def try_jump(self):
        h = self.hist; t = len(h) - 1
        for p in range(1, self.maxp + 1):
            if t - 3 * p < 0: break
            if not (h[t][0] == h[t-p][0] == h[t-2*p][0] == h[t-3*p][0]): continue
            c0, c1, c2, c3 = h[t-3*p][1], h[t-2*p][1], h[t-p][1], h[t][1]
            d = [b - a for a, b in zip(c2, c3)]
            if d != [b - a for a, b in zip(c1, c2)] or d != [b - a for a, b in zip(c0, c1)]: continue
            S3 = h[t][2] - h[t-p][2]; S2 = h[t-p][2] - h[t-2*p][2]; S1 = h[t-2*p][2] - h[t-3*p][2]
            D = S3 - S2
            if S2 - S1 != D: continue
            if all(x == 0 for x in d): continue
            # k: decreasing counts stay >= margin*|d| + margin after the jump, and also through the next 3p (to keep history valid)
            k = None
            for x, dx in zip(c3, d):
                if dx < 0:
                    kk = (x - self.margin - 4 * (-dx)) // (-dx)
                    k = kk if k is None else min(k, kk)
            if k is None: k = 10**9  # no decreasing count: unbounded; cap
            if k < 1: continue
            return p, d, S3, D, k
        return None

    def apply_jump(self, d, S3, D, k):
        s = self.s
        reps = [t for t in s.left + s.right if isinstance(t, Rep)]
        for r, dx in zip(reps, d): r.n += k * dx
        # steps of the next k periods: S3 + D, S3 + 2D, ...
        s.steps += k * S3 + D * k * (k + 1) // 2
        self.jumps += 1
        self.hist = []

    def run(self, until_steps, cap_k=None, log=None):
        s = self.s
        while s.steps < until_steps:
            n0 = s.ncross
            big_cross = False
            if s.try_cross():
                # was it a long leftward cross? detect by a big rep now at right[...] — use flag from count
                big_cross = True
            else:
                s.step()
            self.it += 1
            if self.it % 300 == 0:
                s.compress(); s.make_reps(self.words)
            if big_cross and s.lastdir == 'l' and s.lastn >= self.big:
                s.compress(); s.make_reps(self.words)
                shape, counts = self.snapshot()
                self.hist.append((shape, counts, s.steps))
                if self.on_sample: self.on_sample(self)
                if len(self.hist) > 4 * self.maxp + 4: self.hist.pop(0)
                j = self.try_jump()
                if j:
                    p, d, S3, D, k = j
                    if cap_k: k = min(k, cap_k)
                    if log: log(self, p, d, k)
                    self.apply_jump(d, S3, D, k)

    def _leftward_just(self):
        # the head has just crossed leftward a big rep: a big Rep lies close in front on the right, none close behind
        s = self.s
        return not any(isinstance(t, Rep) and t.n >= self.big for t in s.left[-12:])
