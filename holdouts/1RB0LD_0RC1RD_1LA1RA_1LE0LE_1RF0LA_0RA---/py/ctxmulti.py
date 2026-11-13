"""Round maps with several long blocks (trust level: computation; an extrapolation, not a proof).

An event word is cut into tokens (w, c): w^c, maximal periodic runs (period <= PMAX, at least 3 copies) and literals.
Runs of at least TCELLS cells are *long*.  The class of a word is its token list with the count of every long run
replaced by its remainder mod Q.  The round of a class is computed from simulations: a base instance, one with each
long run made Q copies longer, and two check instances (random and large extra lengths); the round is accepted if
all next events have the same token words and counts that are the affine function fitted on the first ones.  When
no modulus works, the threshold for "long" is raised (up to 8 times) for that round.

usage:  python3 ctxmulti.py MACHINE SIDE STATE SYM check STEPS    compare the class rounds with the direct run
        python3 ctxmulti.py MACHINE SIDE STATE SYM orbit ROUNDS   iterate from the last event of the direct run to 3e9 steps
(SIDE STATE SYM name the event as in ctxround.py; TCELLS in the environment sets the threshold, default 40 cells.)
"""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ctxround as C

PMAX = 12


def tokens(w, pmax=PMAX):
    out = []; i = 0; n = len(w); lit = ''
    while i < n:
        best = (1, 1)
        for p in range(1, pmax + 1):
            if i + 3 * p > n: break
            k = 1
            while w[i + k * p:i + (k + 1) * p] == w[i:i + p]: k += 1
            if k >= 3 and k * p > best[0] * best[1]: best = (p, k)
        p, k = best
        if k >= 3:
            if lit: out.append((lit, 1)); lit = ''
            out.append((w[i:i + p], k)); i += p * k
        else:
            lit += w[i]; i += 1
    if lit: out.append((lit, 1))
    return out


def word(toks):
    return ''.join(w * c for w, c in toks)


def show(toks, lim=400):
    s = ' '.join((w if c == 1 else '(%s)^%d' % (w, c) if c < 10 ** 6 else '(%s)^[%d bits]' % (w, c.bit_length())) for w, c in toks)
    return s if len(s) <= lim else s[:lim] + ' ...'


class Multi:
    def __init__(self, machine, side, state, sym, tcells=40, cap=4 * 10 ** 9, qlist=(1, 2, 3, 4, 6, 8, 12)):
        self.eng = C.Engine(machine, side, state, sym, cap=cap)
        self.T = tcells; self.qlist = qlist; self.cache = {}; self.rng = random.Random(1); self.lastQ = None

    def key(self, toks, Q):
        return tuple((w, c) if c < -(-self.T // len(w)) + 2 + Q else (w, '*', c % Q) for w, c in toks)

    def rep(self, key, Q):
        ck = (key, Q, self.T)
        if ck in self.cache: return self.cache[ck]
        self.cache[ck] = r = self._rep(key, Q)
        return r

    def _rep(self, key, Q):
        idx = [i for i, t in enumerate(key) if len(t) == 3]
        base = []
        for i in idx:
            w, _, r = key[i]
            b = -(-self.T // len(w)) + 2
            b += (r - b) % Q
            base.append(b)

        def inst(d):
            toks = [(t[0], t[1]) for t in key]
            for j, i in enumerate(idx): toks[i] = (key[i][0], base[j] + Q * d[j])
            return word(toks)

        def run(d):
            o = self.eng.ev(inst(d))
            if o[0] != 'ok': return o[0]
            return tokens(o[2])
        z = [0] * len(idx)
        o0 = run(z)
        if isinstance(o0, str): 
            # all instances must agree on a halt
            if o0 == 'HALT':
                for _ in range(3):
                    if run([self.rng.randint(1, 5) for _ in idx]) != 'HALT': return ('INCONS', 'mixed halt')
                return ('HALT',)
            return ('CAP',)
        words = [w for w, _ in o0]; c0 = [c for _, c in o0]
        slopes = []
        for j in range(len(idx)):
            d = z[:]; d[j] = 1
            o = run(d)
            if isinstance(o, str) or [w for w, _ in o] != words: return ('INCONS', 'words')
            slopes.append([c - a for (_, c), a in zip(o, c0)])
        for d in ([self.rng.randint(1, 4) for _ in idx], [7 + j % 3 for j in range(len(idx))]):
            o = run(d)
            if isinstance(o, str) or [w for w, _ in o] != words: return ('INCONS', 'words2')
            pred = [c0[t] + sum(slopes[j][t] * d[j] for j in range(len(idx))) for t in range(len(words))]
            if pred != [c for _, c in o]: return ('INCONS', 'affine')
        return ('ok', idx, base, words, c0, slopes)

    def rnd(self, toks):
        """One round, with the threshold for long runs raised (up to 8 times) when the classes disagree."""
        T0 = self.T
        try:
            for f in (1, 2, 4, 8):
                self.T = T0 * f
                o = self.rnd1(toks)
                if o[0] != '?' or o[1] == 'cap': return o
            return o
        finally:
            self.T = T0

    def rnd1(self, toks):
        """One round.  -> ('ok', toks', Q) | ('HALT', Q) | ('?', why)"""
        why = None
        for Q in ([self.lastQ] if self.lastQ else []) + [q for q in self.qlist if q != self.lastQ]:
            r = self.rep(self.key(toks, Q), Q)
            if r[0] == 'HALT': self.lastQ = Q; return ('HALT', Q)
            if r[0] == 'CAP': return ('?', 'cap')
            if r[0] == 'INCONS': why = r[1]; continue
            _, idx, base, words, c0, slopes = r
            d = [(toks[i][1] - base[j]) // Q for j, i in enumerate(idx)]
            if any(x < 0 for x in d): return ('?', 'below base')
            cs = [c0[t] + sum(slopes[j][t] * d[j] for j in range(len(idx))) for t in range(len(words))]
            if any(c < 1 for c in cs): return ('?', 'count below 1')
            self.lastQ = Q
            return ('ok', self.norm(list(zip(words, cs))), Q)
        return ('?', why)

    def norm(self, toks):
        """Re-tokenise the short parts (long runs keep their token)."""
        out = []; buf = ''
        for w, c in toks:
            if c * len(w) >= 40 * self.T:
                if buf: out += tokens(buf); buf = ''
                out.append((w, c))
            else: buf += w * c
        if buf: out += tokens(buf)
        return out

    def direct(self, toks):
        o = self.eng.ev(word(toks))
        return o if o[0] != 'ok' else ('ok', tokens(o[2]))


def check(mu, steps, verbose=False):
    evs = mu.eng.blank_events(steps)
    n = bad = unk = 0; prev = None
    for e in evs:
        if e[0] in ('HALT', 'OUT'): print('direct run:', e); break
        t = tokens(e[1])
        if prev is not None:
            o = mu.rnd(prev)
            if o[0] == 'ok':
                n += 1
                if word(o[1]) != e[1]:
                    bad += 1
                    if verbose: print('MISMATCH at', e[0], '\n pred', show(o[1]), '\n real', show(t))
            else:
                unk += 1
                if verbose: print('not covered', o, 'before step', e[0])
        prev = t
    return len(evs), n, bad, unk, (evs[-1][0], prev)


def orbit(mu, toks, rounds, verbose=0):
    for i in range(rounds):
        o = mu.rnd(toks)
        if o[0] != 'ok':
            return i, o, toks
        toks = o[1]
        if verbose and (i + 1) % verbose == 0:
            print('round', i + 1, 'tokens', len(toks), 'largest', max(c for _, c in toks).bit_length(), 'bits', flush=True)
    return rounds, None, toks


if __name__ == '__main__':
    machine, side, st, sym, cmd, arg = sys.argv[1:7]
    import os
    mu = Multi(machine, side, st, sym, tcells=int(os.environ.get("TCELLS", "40")))
    if cmd == 'check':
        r = check(mu, arg, verbose=True)
        print('events %d, rounds compared %d, mismatches %d, not covered %d' % r[:4])
    elif cmd == 'orbit':
        r = check(mu, '3e9')
        print('check: events %d, compared %d, mismatches %d, not covered %d' % r[:4])
        n, stop, toks = orbit(mu, r[4][1], int(arg), verbose=max(1, int(arg) // 20))
        print('rounds', n, 'stop', stop, 'classes', len(mu.cache)); print(show(toks, 1500))
