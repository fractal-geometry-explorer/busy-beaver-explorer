"""A region = explicit ladder levels on top of a bottom word B handled by the engine.  Hits enter at the top."""
import sys, time
from lsa_ladder import *
import geng
from geng import show, to_tokens


def prefix_tokens(T, n):
    """the first n tokens of the word T and the cons cell after them (the shared tail)"""
    out = []
    while T is not None and len(out) < n:
        t = T[0]
        if type(t) is tuple and t[0] == 'E':
            T = t[1]
            continue
        out.append(t); T = T[1]
    return out, T


def seg_prefix(T, op, head=(), n=256):
    """segment head ++ T, looking only at a prefix: (levels, bottom word); the same as segmenting the whole word,
    because segment looks at most JMAX tokens ahead"""
    while True:
        pt, tail = prefix_tokens(T, n)
        toks = list(head) + pt
        lv, ib = segment(toks, 0, op)
        if tail is None or ib + JMAX + 2 < len(toks):
            return lv, build(toks[ib:], tail)
        n *= 4


class MultiPassEvent(Exception):
    """an event among several hits passed by one top hit: not handled here (callers fall back or stop)"""


class Region:
    def __init__(self, toks, op='h', Q=44, log=None, tail=None):
        self.top_op = op
        if tail is None:
            self.levels, ib = segment(toks, 0, op)
            self.B = build(toks[ib:], None)
        else:
            self.levels, self.B = seg_prefix(tail, op, head=toks)
        self.Q = Q
        self.steps = 0          # machine steps of everything delivered
        self.used = 0           # hits that entered at the top
        self.bhits = 0          # hits delivered to the bottom
        self.log = log

    def migrate(self, W):
        nl, self.B = seg_prefix(W, 'h' if self.levels else self.top_op)
        self.levels += nl

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
            p, s = apply(self.levels, need)
            if p != Q:
                # the last top hit passed several hits at once (a level can pass more than one per hit)
                assert p > Q
                W, done, cB = self._bottom(p)
                if done is not True:
                    raise MultiPassEvent()
            self.used += need; self.steps += s + cB; self.bhits += p
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
