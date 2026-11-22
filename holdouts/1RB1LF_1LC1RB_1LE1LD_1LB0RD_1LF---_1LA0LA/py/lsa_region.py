"""A region = explicit ladder levels on top of a bottom word B handled by the engine.  Hits enter at the top."""
import sys, time
from lsa_ladder import *
import geng
from geng import show, to_tokens


class Region:
    def __init__(self, toks, op='h', Q=44, log=None):
        self.top_op = op
        self.levels, ib = segment(toks, 0, op)
        self.B = build(toks[ib:], None)
        self.Q = Q
        self.steps = 0          # machine steps of everything delivered
        self.used = 0           # hits that entered at the top
        self.bhits = 0          # hits delivered to the bottom
        self.log = log

    def migrate(self, W):
        tb = to_tokens(W)
        nl, ib = segment(tb, 0, 'h' if self.levels else self.top_op)
        self.levels += nl
        self.B = build(tb[ib:], None)

    def _bottom(self, q):
        geng.C[0] = 0
        if self.levels or self.top_op == 'h':
            W, done = geng.hpow(q, self.B)
        else:
            W, done = geng.gpow(q, self.B)
        return W, done, geng.C[0]

    def feed(self, X=None, maxbatch=None):
        """deliver X hits at the top (None: until an event).  returns None, or the index (1-based, counted in
        top hits from the start of this call) of the hit that causes an event; the region is then left in the
        state just before that hit."""
        used0 = self.used
        nb = 0
        while X is None or self.used - used0 < X:
            nb += 1
            if maxbatch and nb > maxbatch:
                return 'budget'
            Q = self.Q
            W, done, cB = self._bottom(Q)
            if done is not True:
                if done > 0:
                    W2, d2, cB2 = self._bottom(done); assert d2 is True
                    need = chain(self.levels, done)
                    if X is not None and self.used - used0 + need > X:
                        return self._partial(X - (self.used - used0))
                    p, s = apply(self.levels, need); assert p == done
                    self.used += need; self.steps += s + cB2; self.bhits += done
                    self.migrate(W2)
                V = chain(self.levels, 1)
                if X is not None and self.used - used0 + V > X:
                    return self._partial(X - (self.used - used0))
                p, s = apply(self.levels, V - 1); assert p == 0
                self.used += V - 1; self.steps += s
                return self.used - used0 + 1
            need = chain(self.levels, Q)
            if X is not None and self.used - used0 + need > X:
                return self._partial(X - (self.used - used0))
            p, s = apply(self.levels, need); assert p == Q
            self.used += need; self.steps += s + cB; self.bhits += Q
            self.migrate(W)
            if self.log and nb % self.log == 0:
                print('   feed batch %d: %d levels, bottom: %s' % (nb, len(self.levels), show(self.B, 10)), flush=True)
        return None

    def _partial(self, r):
        """r more top hits, which give the bottom fewer than Q hits (no event among them by construction)"""
        p, s = apply(self.levels, r)
        self.used += r; self.steps += s
        if p:
            W, done, cB = self._bottom(p)
            assert done is True
            self.steps += cB; self.bhits += p
            self.migrate(W)
        return None

    def word(self):
        return word(self.levels, self.B)
