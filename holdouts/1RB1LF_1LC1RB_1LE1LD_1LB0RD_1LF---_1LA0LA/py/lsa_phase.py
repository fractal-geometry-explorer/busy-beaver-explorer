"""Regions with symbolic eater phases: jump K super-cycles of an eater at once (K may be astronomically large);
the hit counts above the run of K emitted blocks are exact while they fit in EXACT_BITS bits, then BigF."""
import sys, copy, time, math, pickle, os
from fractions import Fraction
from lsa_ladder import *
from lsa_eater import supercycle, fuel_index
import lsa_eater
from lsa_region import Region, prefix_tokens, MultiPassEvent, seg_prefix
import lsa_ladder
import lsa_law
import lsa_emit
import geng
from geng import show, to_tokens, build

KMIN = 3
SCNEG = {}
SCPOS = {}         # shape of an eater region -> its super-cycle (derived with the fuel symbolic, so valid for any fuel)
PFX = set()        # heads (shape up to the fuel) at which a phase was found: try at once when seen again
LOG = [print]


def shape(toks):
    return tuple(('P', '*', t[2]) if type(t) is tuple and t[0] == 'P' and t[1] > 200 else t for t in toks)


HEADMAX = 24     # an eater's head may have this many tokens before its fuel (16 missed one of 17, after phase 12,174
                 # from visit 10^3200: it was then fed 200 hits a batch)


EXTRAMAX = 40     # tokens of the rest an eater region may take in (16 was one short after phase 13,010 from visit
                  # 10^3200: a x16 eater whose passed hits run through the next [100] fuel into the rest)


# While the fine search looks for a hit where an eater's block is regular (PRegion.step), the super-cycles it
# looks for have the period P of the eater's super-cycle already found: FINEP holds P + 1 as the search bound, and
# failures under that bound are kept apart (SCNEGF), not as failures of the shape.  The fine search stops after
# FINESECS seconds and is not started again for the same eater: after phase 28,829 from visit 10^3200 an eater of
# P = 33,549 hits emitted a block that ends in a lone 0^6; each single hit then cost ~10 searches of 12 s.
FINEP = [None]
LAW = [__import__('os').environ.get('LSA_NOLAW') is None]
INTRANS = [False]   # inside trans_run (fast_next): no law detection there
EMIT = [os.environ.get('LSA_NOEMIT') is None]
LAWC = {}           # eater shape -> law (lsa_law.detect) or 'neg'
SCNEGF = {}
FINESECS = 600
FINEDONE = set()


def find_phase(btoks, known_only=False):
    """an eater super-cycle at the head of the bottom: (sc, E tokens, fuel index, rest tokens, K) or None.
    known_only: only shapes whose super-cycle is already known (no new search)"""
    fi = fuel_index(btoks[:HEADMAX], thr=200)
    if fi is None:
        return None
    # the shape alone is enough to know a failure: the super-cycle search depends on the fuel only through its size
    opq = False
    for extra in range(0, EXTRAMAX):
        if fi + 1 + extra >= len(btoks):
            break
        if extra >= 16 and not opq:
            break       # past 16 tokens only while the rest was too short for the hits passed down
        E = btoks[:fi + 1 + extra]
        key = shape(E)
        sc = SCPOS.get(key)
        if sc is None and key in SCNEG:
            opq = SCNEG[key] == 'opaque'
            continue
        if sc is None and FINEP[0] is not None and (key, FINEP[0]) in SCNEGF:
            opq = SCNEGF[(key, FINEP[0])] == 'opaque'
            continue
        if sc is None and known_only:
            continue
        if sc is None:
            sc = supercycle(E, fi, Pmax=FINEP[0] or 200000)
            if sc is not None:
                SCPOS[key] = sc
        if sc is None:
            opq = lsa_eater.OPQ[0]
            if FINEP[0] is None:
                SCNEG[key] = 'opaque' if opq else 1
            else:
                SCNEGF[(key, FINEP[0])] = 'opaque' if opq else 1
            continue
        K = (E[fi][1] - sc['mmin']) // sc['dm'] + 1
        if K < KMIN:
            return None
        return sc, E, fi, btoks[fi + 1 + extra:], K
    return None


def block_map(sc, E):
    """the emitted block as levels, and its hit map f(x) = a x + b"""
    toks = list(sc['blk']) + list(E)
    bl, j = segment(toks, 0, 'h')
    if toks[j:] != list(E):
        return None
    vals = [chain([copy.copy(L) for L in bl], x) for x in (1, 2, 3, 1000)]
    a = vals[1] - vals[0]; b = vals[0] - a
    assert vals[2] == 3 * a + b and vals[3] == 1000 * a + b, vals
    return bl, a, b


def pass_positions(sc, E, fi):
    if sc.get('law'):
        return lsa_law.pass_positions(sc, E, fi)
    T = build(list(E), (('O', 0), None))
    pos = []
    for i in range(1, sc['P'] + 1):
        T = geng.h(T)
        o = to_tokens(T)[-1]
        assert o[0] == 'O'
        while o[1] > len(pos):      # one hit can pass several hits down
            pos.append(i)
    assert len(pos) == sc['c'], (pos, sc['c'])
    return pos


EXACT_BITS = 10 ** 7   # numbers above this many bits are kept as BigF (a float mantissa and an exact exponent)


class BigF:
    """m * 2^E, 1 <= m < 2, E an exact (huge) integer: for counts far too large to write down"""
    __slots__ = ('m', 'E')

    def __init__(self, m, E):
        if m <= 0:
            raise ValueError(m)
        fe = math.frexp(m)
        self.m = fe[0] * 2; self.E = E + fe[1] - 1

    @staticmethod
    def of(x):
        if isinstance(x, BigF):
            return x
        x = Fraction(x)
        if x.denominator != 1:
            n, d = BigF.of(x.numerator), BigF.of(x.denominator)
            return BigF(n.m / d.m, n.E - d.E)
        x = int(x); n = x.bit_length()
        top = x >> max(0, n - 60)
        return BigF(float(top), max(0, n - 60))

    def mul(self, c):          # c: positive int, Fraction or BigF
        if isinstance(c, BigF):
            return BigF(self.m * c.m, self.E + c.E)
        c = Fraction(c)
        return BigF(self.m * (BigF.of(c.numerator).m / BigF.of(c.denominator).m),
                    self.E + BigF.of(c.numerator).E - BigF.of(c.denominator).E)

    def shl(self, e):
        return BigF(self.m, self.E + e)

    def add(self, o):          # o a BigF, or an int or Fraction (negative ones much smaller than self)
        if not isinstance(o, BigF) and o == 0:
            return self
        if not isinstance(o, BigF) and o < 0:
            o = BigF.of(-o)
            assert o.E + 2 < self.E
            d = self.E - o.E
            return self if d > 200 else BigF(self.m - o.m * 2.0 ** (-d), self.E)
        o = BigF.of(o) if not isinstance(o, BigF) else o
        if o.E > self.E:
            return o.add(self)
        d = self.E - o.E
        return self if d > 200 else BigF(self.m + o.m * 2.0 ** (-d), self.E)

    def log2(self):
        return self.E + math.log2(self.m)

    def log10(self):
        return self.log2() * math.log10(2)

    def __repr__(self):
        return '%.15g * 2^%d' % (self.m, self.E)


def big(x):
    return isinstance(x, BigF) or (isinstance(x, int) and x.bit_length() > EXACT_BITS)


def G(K, Z, P, a, b):
    """hits into the top of [run of K blocks + region] until the region has had Z hits"""
    if K == 0:
        return Z
    if a == 1:
        r = P + b + (K - 1) * (P + b)
        return Z.add(r) if isinstance(Z, BigF) else Z + r
    e = a.bit_length() - 1
    assert a == 1 << e, "block multiplier not a power of 2"
    if not big(Z) and e * K <= EXACT_BITS:
        aK1 = a ** (K - 1)
        I1 = aK1 * (a * Z + b) + Fraction((a * P + b) * (aK1 - 1), a - 1)
        r = P + I1
        assert r.denominator == 1
        return int(r)
    # a^(K-1) (a Z + b) + (a P + b)(a^(K-1) - 1)/(a - 1) + P, as a BigF
    Zb = BigF.of(Z).mul(a).add(b)
    return Zb.add(Fraction(a * P + b, a - 1)).shl(e * (K - 1))


def chain_sym(levels, H):
    """hits into the top of the levels until H hits reached the region below (an affine map of H)"""
    if not big(H):
        return chain([copy.copy(L) for L in levels], H)
    for L in levels:
        tail, cyc = L.path()
        assert sum(x[2] for x in cyc) == 1, "level passes more than one hit per cycle"
    x0 = 10 ** 6
    v = [chain([copy.copy(L) for L in levels], x) for x in (x0, x0 + 1, x0 + 2, 2 * x0)]
    A = v[1] - v[0]; B = v[0] - A * x0
    assert v[2] == A * (x0 + 2) + B and v[3] == A * 2 * x0 + B and A > 0
    return H.mul(A).add(B)


def unwind(frames, z):
    for used, snap, P, a, b, K in reversed(frames):
        z = chain_sym(snap, G(K, z, P, a, b))
        z = z.add(used) if isinstance(z, BigF) else z + used
        if isinstance(z, int) and z.bit_length() > EXACT_BITS:
            z = BigF.of(z)
    return z


BMC = {}


def block_map_c(sc, E):
    if sc.get('law'):
        return [], sc['a'], 0
    key = (shape(E), tuple(sc['blk']))
    if key not in BMC:
        BMC[key] = block_map(sc, E)
    return BMC[key]


class PRegion(Region):
    depth = 0
    fine = 0

    def step(self, maxbatch=10 ** 6):
        """run batches until an event ('event', top hits from now up to and including the event hit) or until an
        eater phase starts ('phase', ph)"""
        used0 = self.used
        nb = 0
        while nb < maxbatch:
            nb += 1
            self.B = fold_front(self.B)
            bt, tail = prefix_tokens(self.B, 96)
            fi = fuel_index(bt[:HEADMAX], thr=200)
            if fi is not None:
                key = shape(bt[:fi + 1])
                seen = getattr(self, 'seen', None)
                if seen is None:
                    seen = self.seen = {}
                if (key in seen and bt[fi][1] < seen[key]) or key in PFX or self.fine:
                    ph = find_phase(bt, known_only=self.fine and getattr(self, 'fine_known', False))
                    if ph is not None:
                        ph = ph[:3] + (build(ph[3], tail),) + ph[4:]
                    if ph is not None and block_map_c(ph[0], ph[1]) is not None:
                        PFX.add(key)
                        if self.fine:
                            self.Q, self.fine = self.fine_Q, 0
                            FINEP[0] = None
                        return 'phase', ph
                    if ph is not None and LAW[0] and not INTRANS[0]:
                        # no regular block: an observed law of the cost per unit of fuel (lsa_law)
                        lk = shape(ph[1])
                        r = LAWC.get(lk)
                        if r is None:
                            r = lsa_law.detect(ph[1], ph[2]) or 'neg'
                            if not isinstance(r, tuple):
                                LAWC[lk] = r
                        if isinstance(r, tuple) and getattr(self, 'law_aligns', 0) < 4:
                            # the law holds from r[1] hits on: give the bottom exactly those, then look again
                            self.law_aligns = getattr(self, 'law_aligns', 0) + 1
                            Qs = self.Q
                            self.Q = r[1]
                            u = self.used
                            ev = self.feed(None, maxbatch=1)
                            self.Q = Qs
                            if ev != 'budget':
                                return 'event', (u - used0) + ev
                            continue
                        if isinstance(r, dict):
                            E, fi = ph[1], ph[2]
                            K = (E[fi][1] - r['mmin']) // r['dm'] + 1
                            if K >= 1:
                                LOG[0]('%s(law phase: %d units of fuel a period, x2^%d, %d hits down)' % (
                                    '  ' * min(self.depth, 20), r['dm'], r['a'].bit_length() - 1, r['c']))
                                return 'phase', (r, E, fi, ph[3], K)
                    if ph is not None:
                        k = shape(ph[1])
                        if k not in NOTREG:
                            LOG[0]('%s(block of the eater %s not regular at this hit: single hits)' % ('  ' * min(self.depth, 20), show(build(ph[1][:ph[2]], None))))
                            NOTREG.add(k)
                        # not SCNEG: whether the block is regular depends on the hit of the eater's cycle, not on the
                        # shape.  Marking the shape negative made a later eater of that shape (66,946 rungs, after
                        # phase 1,756 from visit 10^3200) unrecognised, fed 200 hits a batch for hours.
                        if not self.fine and k not in FINEDONE:
                            # the super-cycle can start at any hit of the eater's cycle; find one where the block is regular
                            FINEDONE.add(k)
                            self.fine_Q, self.Q, self.fine = self.Q, 1, 4000
                            self.fine_known = False
                            self.fine_t0 = time.time()
                            FINEP[0] = ph[0]['P'] + 1
                seen[key] = bt[fi][1]
            del bt
            if self.fine:
                self.fine -= 1
                if self.fine and time.time() - getattr(self, 'fine_t0', 0) > FINESECS and FINEP[0] is not None:
                    self.fine = 0
                if not self.fine:
                    self.Q = self.fine_Q
                    FINEP[0] = None
            if not self.fine:
                # no phase for a while: larger batches (exact either way; the levels above cost the same per batch,
                # after phase 13,010 from visit 10^3200 there were 1.6 million hits to feed in batches of 200)
                self.nobatch = getattr(self, 'nobatch', 0) + 1
                if self.nobatch % QGROW == 0 and self.Q < getattr(self, 'qmax', QMAX):
                    self.Q *= 2
            u = self.used
            ev = self.feed(None, maxbatch=1)
            if ev != 'budget':
                return 'event', (u - used0) + ev      # feed counts from its own start
        return 'budget', None


QGROW = 64
QMAX = 1 << 16
FRAMES = []
NOTREG = set()          # eater shapes already reported as not regular (log once)


def save_state(path, R, frames, nph):
    st = dict(levels=R.levels, B=to_tokens(R.B), used=R.used, depth=R.depth, Q=R.Q, op=R.top_op,
              seen=getattr(R, 'seen', {}), qmax=getattr(R, 'qmax', QMAX), frames=frames, nph=nph, SCPOS=SCPOS, SCNEG=SCNEG, PFX=PFX, TCACHE=TCACHE)
    import gzip
    with open(path + '.tmp', 'wb') as f:     # gzip, about 13 times smaller
        f.write(gzip.compress(pickle.dumps(st, protocol=4), compresslevel=1))
    os.replace(path + '.tmp', path)


def load_state(path):
    import gzip
    with open(path, 'rb') as f:
        gz = f.read(2) == b'\x1f\x8b'
    st = pickle.load((gzip.open if gz else open)(path, 'rb'))
    R = PRegion([], Q=st['Q'], op=st['op'])
    R.levels = st['levels']; R.B = build(st['B'], None); R.used = st['used']; R.depth = st['depth']
    R.seen = st['seen']
    R.qmax = st.get('qmax', QMAX)
    SCPOS.update(st['SCPOS']); SCNEG.update(st['SCNEG']); PFX.update(st['PFX']); TCACHE.update(st.get('TCACHE', {}))
    return R, st['frames'], st['nph']


# ---------------------------------------------------------------- fast transitions between phases
# After a phase the word is E2 W: the eater with its leftover fuel, then the rest.  The way to the next phase only
# looks at the head of W up to the next big fuel F (count > BIGF); everything after F only receives hits.  So the
# transition is computed once with the part after F opaque (an ('O', r) token that counts the r hits it receives),
# checked to be the same for several values of F with the same residue mod MODF (F + d for d in SHIFTS, only the
# fuel's count moves), and then
# reused: the real tail receives its r hits with one hpow.  A transition that reads the opaque part, an event during
# the transition, or any mismatch falls back to the plain step.
TCACHE = {}
FAST = [True]
HOOK = [None]      # called with (phase number, sc, E, fuel index, rest, K) at each phase
BIGF = 10 ** 6
MODF = 4              # the transition may depend on F mod MODF (it does: the eater takes 4 units a round)
SHIFTS = (0, 4, 8, 12, 44, 4000)
TSTAT = dict(fast=0, slow=0, new=0, bad=0)
FINE_START = [int(os.environ.get('LSA_FINE', '1200'))]


WTOK = {}


def wtok(w):
    ct = WTOK.get(w)
    if ct is None:
        ct = WTOK[w] = to_tokens(geng.from_digits(list(w)))
    return ct


def _tok_digits(t, cap=4000):
    if type(t) is tuple:
        k = t[0]
        if k == 'Z':
            return [0] * t[1] if t[1] <= cap else None
        if k == 'R':
            return [1, 0] * t[1] if t[1] <= cap else None
        if k == 'P':
            return list(t[2]) * t[1] if t[1] * len(t[2]) <= cap else None
        return None
    return [t]


def fold_toks(pt, thr=200, back=48):
    """the same word, with the copies of w written out just before a run ('P', n, w), n > thr, folded into it.
    Compared digit by digit, so that a run of a rotation of w followed by the rest of a copy (left over when an
    eater stops with a little fuel next to a new run of the same word) is folded too: (t s)^a t (s t)^n = t (s t)^(a+n)."""
    out = []
    for t in pt:
        if type(t) is tuple and t[0] == 'P' and t[1] > thr:
            w = list(t[2]); L = len(w)
            D = []; j = len(out)
            while j > 0 and len(out) - j < back:
                d = _tok_digits(out[j - 1])
                if d is None:
                    break
                D = d + D; j -= 1
            r = 0
            while (r + 1) * L <= len(D) and D[len(D) - (r + 1) * L:len(D) - r * L] == w:
                r += 1
            if r:
                # keep the tokens that lie wholly before the folded digits
                need = r * L; k = len(out); got = 0
                while got < need:
                    k -= 1; got += len(_tok_digits(out[k]))
                left = D[len(D) - got:len(D) - need]
                del out[k:]
                out.extend(to_tokens(geng.from_digits(left)))
                t = ('P', t[1] + r, t[2])
            if MERGE[0] and _merge_prev(out, t, thr):
                continue
        out.append(t)
    return out


MERGE = [True]


def _merge_prev(out, t, thr, maxmid=2000):
    """if out ends with ('P', a, v), a > thr, then a few short tokens, and the digits v^a mid w^n are one periodic
    word (v a rotation of w), replace all of it in out by ('P', N // L, v) and the first N % L digits of v, and return
    True: one run instead of two.  The engine writes a long run of the rung in pieces; merged, an eater burns it in
    one phase.  Otherwise return False (out unchanged)."""
    w = t[2]; L = len(w)
    p = len(out) - 1
    mid = []
    while p >= 0:
        u = out[p]
        if type(u) is tuple and u[0] == 'P' and u[1] > thr:
            break
        d = _tok_digits(u)
        if d is None or len(mid) + len(d) > maxmid:
            return False
        mid = d + mid; p -= 1
    if p < 0:
        return False
    v = out[p][2]
    if len(v) != L:
        return False
    s = list(v) * 2 + mid + list(w) * 2
    if any(s[i] != s[i - L] for i in range(L, len(s))):
        return False
    N = out[p][1] * L + len(mid) + t[1] * L
    del out[p:]
    out.append(('P', N // L, v))
    out.extend(to_tokens(geng.from_digits(list(v[:N % L]))))
    return True


def fold_front(T, n=64):
    pt, tail = prefix_tokens(T, n)
    ft = fold_toks(pt)
    return T if ft == pt else build(ft, tail)


def head_split(W, n=400):
    """(head, F, tail): F the first big fuel of W.  Copies of F's word written out just before F (left there when a
    unit of the run is opened) are folded into F, so that the head, and with it the cache key, stays the same."""
    pt, tail = prefix_tokens(W, n)
    if MERGE[0]:
        pt = fold_toks(pt)          # pieces of one run, stored as several tokens, become one fuel
    for i, t in enumerate(pt):
        if type(t) is tuple and t[0] == 'P' and t[1] > BIGF:
            w = t[2]
            ct = WTOK.get(w)
            if ct is None:
                ct = WTOK[w] = to_tokens(geng.from_digits(list(w)))
            j, r = i, 0
            while j >= len(ct) and pt[j - len(ct):j] == ct:
                j -= len(ct); r += 1
            return pt[:j], ('P', t[1] + r, w), build(pt[i + 1:], tail)
    return None


def trans_run(E2, head, F, Q):
    INTRANS[0] = True
    try:
        R = PRegion(list(E2) + list(head) + [F], Q=Q, tail=(('O', 0), None))
        if FINE_START[0]:
            # single hits at first: the next eater can take its regular shape at any hit of its cycle
            R.fine_Q, R.Q, R.fine = Q, 1, FINE_START[0]
            R.fine_known = True
        kind, x = R.step(maxbatch=600 + FINE_START[0])
    except (geng.Opaque, MultiPassEvent):
        return None
    finally:
        INTRANS[0] = False
    if kind != 'phase':
        return None
    sc, E, fi, rest, K = x
    rt = to_tokens(rest)
    if not rt or not (type(rt[-1]) is tuple and rt[-1][0] == 'O') or any(
            type(t) is tuple and t[0] == 'O' for t in list(E) + rt[:-1]):
        return None
    lv = [L.tokens() for L in R.levels]
    return dict(used=R.used, levels=R.levels, lvt=lv, sc=sc, E=list(E), fi=fi, rt=rt, K=K)


def _template(res, F):
    """the result with the one token that carries the fuel F (count F - s) marked; None if there is not exactly one"""
    out = []; s = None
    for part in ('E', 'rt'):
        for k, t in enumerate(res[part]):
            if type(t) is tuple and t[0] == 'P' and t[1] > BIGF:
                if s is not None:
                    return None
                s = (part, k, F[1] - t[1], t[2])
    return s


def trans_entry(E2, head, F, Q):
    ref = None
    for d in SHIFTS:
        Fd = ('P', F[1] + d, F[2])
        res = trans_run(E2, head, Fd, Q)
        if res is None:
            return False
        tm = _template(res, Fd)
        if tm is None:
            return False
        norm = (res['used'], res['lvt'], res['fi'], res['sc']['P'], res['sc']['dm'], res['sc']['c'], tm[0], tm[1], tm[2], tm[3],
                [t for k, t in enumerate(res['E']) if not (tm[0] == 'E' and k == tm[1])],
                [t for k, t in enumerate(res['rt']) if not (tm[0] == 'rt' and k == tm[1])])
        if ref is None:
            ref = (norm, res, tm)
        elif norm != ref[0]:
            return False
    return ref[1], ref[2]


def fast_next(E2, W, Q):
    """the next phase straight from (E2, W), or None (then use the plain step)"""
    hs = head_split(W)
    if hs is None:
        return None
    head, F, tail = hs
    key = (tuple(E2), tuple(head), F[2], F[1] % MODF)
    ent = TCACHE.get(key)
    if ent is None:
        TSTAT['new'] += 1
        ent = TCACHE[key] = trans_entry(E2, head, F, Q)
    if not ent:
        TSTAT['bad'] += 1
        return None
    res, (part, k, sh, w) = ent
    E = list(res['E']); rt = list(res['rt'])
    if part == 'E':
        E[k] = ('P', F[1] - sh, w)
    else:
        rt[k] = ('P', F[1] - sh, w)
    sc, fi = res['sc'], res['fi']
    K = (E[fi][1] - sc['mmin']) // sc['dm'] + 1
    if K < KMIN:
        return None
    geng.C[0] = 0
    W1, done = geng.hpow(rt[-1][1], tail)
    if done is not True:
        return None
    TSTAT['fast'] += 1
    return res['used'], [copy.copy(L) for L in res['levels']], (sc, E, fi, build(rt[:-1], W1), K)


def run_to_event(R, ckpt=None, every=200, frames=None, nph=0):
    """top hits of the region R (from its present state) up to and including the hit of the next event.
    ckpt: a file to save the state to every `every` phases (resume with load_state)"""
    frames = [] if frames is None else frames
    pending = None
    Q = R.Q
    while True:
        if pending is None:
            kind, x = R.step()
            if kind == 'budget':
                raise RuntimeError('budget')
            if kind == 'event':
                z = x
                break
            used, levels, depth = R.used, [copy.copy(L) for L in R.levels], R.depth
        else:
            used, levels, x, depth = pending
            pending = None
        sc, E, fi, rest, K = x
        bl, a, b = block_map_c(sc, E)
        P = sc['P']; c = sc['c']
        nph += 1
        LOG[0]('%sPHASE %d: eater %s with fuel %s: K = %s super-cycles of %d hits (fuel -%d, %d hits down, block x%d%+d)' % (
            '  ' * min(depth, 20), nph, show(build(E[:fi], None)), short(E[fi][1]), short(K), P, sc['dm'], c, a, b))
        fr = (used, levels, P, a, b)
        if HOOK[0]:
            HOOK[0](nph, sc, E, fi, rest, K)
        # the rest gets c hits per super-cycle, whatever it does with them (the eater never looks at it)
        geng.C[0] = 0
        W, done = ladder_hpow(c * K, rest)
        del rest
        if done is not True:
            pos = pass_positions(sc, E, fi)
            j = done // c + 1; k = done % c
            LOG[0]('%s  event below the eater at its hit %d of cycle %s' % ('  ' * min(depth, 20), pos[k], short(j)))
            frames.append(fr + (j - 1,))
            z = pos[k]
            break
        E2 = list(E); E2[fi] = ('P', E[fi][1] - sc['dm'] * K, E[fi][2])
        frames.append(fr + (K,))
        R = None
        save = ckpt and (nph + 1) % every == 0
        nx = fast_next(E2, W, Q) if FAST[0] and not save else None
        if nx is not None:
            pending = (nx[0], nx[1], nx[2], depth + 1)
        else:
            TSTAT['slow'] += 1
            R = PRegion(E2, Q=Q, tail=W)
            R.depth = depth + 1
            if sc.get('law'):
                R.qmax = 1 << 200     # the fuel left after a law phase can take ~10^15 hits: let batches grow
            if save:
                save_state(ckpt, R, frames, nph)
        del W
    FRAMES[:] = frames
    return unwind(frames, z)


LADDER_MIN = 10 ** 6
LSTAT = {'ladder': 0, 'plain': 0}


LADDER_ROUNDS = 20000
LADDER_BATCH = 256
LADDER_DEPTH = 3


def ladder_hpow(q, T):
    """geng.hpow(q, T), with the front of T cut into ladder levels first when q is large: the levels count the hits
    in closed form (lsa_ladder.apply) and only the hits that get through reach the engine.  Plain hpow on a stack of
    ladders carries 10^41 hits level by level (after phase 13,008 from visit 10^3200 that took hours).  Levels whose
    count falls (fuel) are accepted too: when one runs out, the levels above it are kept, the hits it passed so far
    go below it, and one plain hit takes it through its refuel, then the rest is cut into levels again.  If the
    engine answers with an event anywhere, the plain computation is done instead (exact either way).
    With ENGINE_HOOK the engine's own large powers (h^q and G^q met inside its recursion) go this way too."""
    r = ladder_power('h', q, T)
    if r is None:
        return _power(geng.h, 'h', q, T)
    return r, True


OPF = {'h': geng.h, 'G': geng.G}
HDEPTH = [0]
HMAX = 4
_power = geng.power


def ladder_power(op, q, T):
    """op^q(T) by the ladder, or None (q small, nested too deep, or an event)"""
    if type(q) is not int or q < LADDER_MIN or HDEPTH[0] >= HMAX or T is None:
        return None
    neg0 = lsa_ladder.NEG[0]
    lsa_ladder.NEG[0] = True
    HDEPTH[0] += 1
    c0 = geng.C[0]
    try:
        r = _ladder(q, T, 0, op)
    finally:
        lsa_ladder.NEG[0] = neg0
        HDEPTH[0] -= 1
    if r is None:
        geng.C[0] = c0
        LSTAT['plain'] += 1
        return None
    LSTAT['ladder'] += 1
    return r


def _power_hook(op, name, q, T):
    if geng.Rec.cons is None and HDEPTH[0] < HMAX and type(q) is int and q >= LADDER_MIN:
        r = ladder_power(name, q, T)
        if r is not None:
            return r, True
    return _power(op, name, q, T)


ENGINE_HOOK = os.environ.get('LSA_NOHOOK') is None
if ENGINE_HOOK:
    geng.power = _power_hook


def _plain(op, k, T):
    return geng.power(OPF[op], op, k, T)


def _ladder(q, T, depth=0, op='h'):
    """the word op^q(T) as computed by ladder_power, or None on an event.  Below LADDER_DEPTH nested bottoms the
    engine gets the hits (cutting every bottom again costs more than it saves: phase 12,000 from visit 10^3200)"""
    if depth >= LADDER_DEPTH:
        T, done = _plain(op, q, T)
        return T if done is True else None
    head = []
    rounds = miss = 0
    while q:
        rounds += 1
        lv = None
        if q >= LADDER_BATCH and rounds <= LADDER_ROUNDS:
            lv, B = seg_prefix(T, op)
        if not lv and EMIT[0] and op == 'h' and q >= LADDER_MIN:
            # an eater that leaves a frozen word at every cycle (lsa_emit): its cycles at once
            r = lsa_emit.jump(q, T, lambda n, X: _plain('h', n, X))
            if r is not None:
                T, used = r
                q -= used
                continue
        if not lv:
            # not cut into levels (yet): a few plain hits, then try again (a few hits can turn a block into fuel);
            # after a second miss in a row the engine gets them all (its own rules may well jump them)
            miss += 1
            k = q if (rounds > LADDER_ROUNDS or miss > 1) else min(q, LADDER_BATCH)
            T, done = _plain(op, k, T)
            if done is not True:
                return None
            q -= k
            continue
        miss = 0
        lv = [copy.copy(L) for L in lv]
        i, rem, p, s = lsa_ladder.apply_stop(lv, q)
        geng.C[0] += s
        if i is None:
            if p:
                B = _ladder(p, B, depth + 1)
                if B is None:
                    return None
            T = lsa_ladder.word(lv, B)
            break
        LSTAT['runout'] = LSTAT.get('runout', 0) + 1
        below = lsa_ladder.word(lv[i + 1:], B)
        if p:
            below = _ladder(p, below, depth + 1)
            if below is None:
                return None
        for L in lv[:i]:
            head += L.tokens()
        T, done = _plain(lv[i].op, 1, lsa_ladder.word([lv[i]], below))
        if done is not True:
            return None
        op = lv[i].op
        q = rem - 1
    return build(head, T) if head else T


def short(n):
    s = str(n)
    return s if len(s) < 30 else '%s..(%d digits)' % (s[:10], len(s))
