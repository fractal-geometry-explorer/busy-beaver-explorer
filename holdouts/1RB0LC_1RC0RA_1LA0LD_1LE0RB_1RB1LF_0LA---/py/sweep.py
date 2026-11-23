"""One round of 1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA--- as a crossing-sequence transducer on tokens, and closures of
n-gram languages under it (the relaxed run of py/relax.py: the budget may run out at any round start).

Tokens: the tape at a round start split into maximal runs (01)^n and the cell words between them (always 1^a 0^b).
This split is canonical: a change in one place never changes how the rest of the tape splits (the old tokens of
tok.py, with | = 00110, re-read a chain of stalled "1" cursors after any change at its left end).  Abstract tokens:
runs 1..K exact and 'E'/'O' longer (by parity); words 'w' + cells, or 'W' + class + zeros for 1^a 0^b with a > A1.

The round: the head starts on the first cell in state A and the round ends at the next event (state A, reading 0,
blank to the left), which is in the blank region left of the tape (LREG).  At each token boundary the head crosses
some number of times; the crossing sequence lists its states.  A token's behaviour, for a left crossing sequence,
is the set of possible right crossing sequences (the states in which the head comes back from the right are
guessed) with the token's new cells.  A round on a language is then a product graph (language state, crossing
sequence), trimmed to the paths that end consistently at the blank right end (RREG); its outputs, put back into
canonical tokens, give the new n-grams.  Runs and long words stand for all their values: the behaviour is the union
over small values and two large ones, which must agree (else `nonuniform`).  A round can change several places and
sweep several times (after a "0" 1 "1110" collision the head bounces off a stray 0 and sweeps right again); the
crossing sequences handle that exactly.

usage: python3 sweep.py check SEEDS ROUNDS     every round of relaxed runs (relax.relaxed, seeds a-b) computed by the
                                               transducer on the exact tape (K, A1 huge) and compared with tok.round_
       python3 sweep.py closure ROUNDS [MAX]   n-gram closure (NG=6, K=4, A1=4 from the environment) from the tape of
                                               the real run at ROUNDS rounds, under rounds and cuts, until it closes,
                                               a halt or a 110/1110 before a separator appears, or MAX grams
"""
import sys, os, collections, functools, time
if len(sys.argv) > 1 and sys.argv[1] == 'check':
    os.environ.setdefault('K', str(10 ** 9)); os.environ.setdefault('A1', str(10 ** 9)); os.environ.setdefault('NG', '3000')
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
N = int(os.environ.get('NG', 6))
K = int(os.environ.get('K', 4))
MAXC = int(os.environ.get('MAXC', 8))
STATES = 'ABCDEF'
T = {('A', 0): (1, 1, 'B'), ('A', 1): (0, -1, 'C'), ('B', 0): (1, 1, 'C'), ('B', 1): (0, 1, 'A'),
     ('C', 0): (1, -1, 'A'), ('C', 1): (0, -1, 'D'), ('D', 0): (1, -1, 'E'), ('D', 1): (0, 1, 'B'),
     ('E', 0): (1, 1, 'B'), ('E', 1): (1, -1, 'F'), ('F', 0): (0, -1, 'A'), ('F', 1): None}

def isrun(t): return type(t) is int or t in ('E', 'O')
def isword(t): return type(t) is str and t[0] in 'wW'
A1 = int(os.environ.get('A1', 4))
def ab1(v): return v if v <= A1 else ('O' if v % 2 else 'E')
def par(t): return t % 2 if type(t) is int else (1 if t == 'O' else 0)
def ab(v): return v if v <= K else ('O' if v % 2 else 'E')

def reps(t):
    """concrete values a run token stands for: (small ones, large ones)"""
    if type(t) is int: return [t], []
    p = par(t); b = K + 1 if (K + 1) % 2 == p else K + 2
    return [b, b + 2, b + 4], [1000 + p, 1236 + p]

class Halt(Exception): pass
class Loop(Exception): pass

def cells_to_items(cells):
    """canonical items: maximal runs [n] and literal cells"""
    out = []; i = 0
    while i < len(cells):
        if cells[i] == 0 and i + 1 < len(cells) and cells[i + 1] == 1:
            j = i
            while j + 1 < len(cells) and cells[j] == 0 and cells[j + 1] == 1: j += 2
            out.append([(j - i) // 2]); i = j
        else:
            out.append(cells[i]); i += 1
    return out

def tsim(cells, cl, start=False):
    """Simulate one token.  cl: left crossing sequence (states).  If start, the head begins on cell 0 in state A and
    cl = [p1, q2, p2, ...]; else cl = [q1, p1, q2, p2, ...] (enter from the left, exit to the left, ...).  A cl that ends
    with an entry means the head never leaves again to the left (it halts here or further right).
    Yields (kind, cr, newcells): kind 'ok' (the head's last crossing of the left boundary is its final exit), 'open'
    (the head left to the right for good: it halts further right), 'halt' (it halts in this token)."""
    n = len(cells)
    def run(c, pos, q, i, cr):
        steps = 0
        while True:
            if pos < 0:
                if i >= len(cl) or cl[i] != q: return
                i += 1
                if i == len(cl):
                    yield ('ok', tuple(cr), tuple(c)); return
                q = cl[i]; i += 1; pos = 0; continue
            if pos >= n:
                cr2 = cr + [q]
                if i == len(cl): yield ('open', tuple(cr2), tuple(c))
                if len(cr2) + 1 > MAXC: return
                for s in STATES:
                    yield from run(list(c), n - 1, s, i, cr2 + [s])
                return
            b = c[pos]; tr = T[(q, b)]
            if tr is None:
                if i == len(cl): yield ('halt', tuple(cr), tuple(c))
                return
            w, d, q = tr; c[pos] = w; pos += d; steps += 1
            if steps > 200000: raise Loop(('steps', cl))
    if start:
        yield from run(list(cells), 0, 'A', 0, [])
    else:
        if not cl: yield ('ok', (), tuple(cells)); return
        yield from run(list(cells), 0, cl[0], 1, [])

def lreg_behaviours(maxlen=MAXC):
    """LREG: blank cells to the left.  The head enters from the right (state guessed), may leave to the right, and
    the round ends at an event here.  Returns (kind, crossing sequence at boundary 0 as t1 sees it [p1, q2, p2, ...],
    output cells from the event cell on); kind 'ok' (event), 'open' (left to the right for good), 'halt'."""
    out = []
    W = 40
    def run(c, pos, q, seq):
        steps = 0
        while True:
            if pos >= W:
                seq2 = seq + [q]
                out.append(('open', tuple(seq2), ()))
                if len(seq2) + 1 > maxlen: return
                for s in STATES: run(list(c), W - 1, s, seq2 + [s])
                return
            if pos < 0: raise Loop('lreg too small')
            if q == 'A' and c[pos] == 0 and all(x == 0 for x in c[:pos]):
                out.append(('ok', tuple(seq), tuple(c[pos:]))); return
            tr = T[(q, c[pos])]
            if tr is None: out.append(('halt', tuple(seq), ())); return
            w, d, q = tr; c[pos] = w; pos += d; steps += 1
            if steps > 10000: return
    for s in STATES: run([0] * W, W - 1, s, [s])
    return out

def rreg_halts(cl):
    return any(k == 'halt' for k, cr, c in tsim([0] * 60, list(cl)))

def rreg_ok(cl):
    """RREG: blank cells to the right.  cl = [q1, p1, q2, p2, ...]; the head must never leave to the right for good.
    Returns the new cells (trailing zeros dropped) or None."""
    W = 60
    res = list(tsim([0] * W, list(cl)))
    outs = set()
    for kind, cr, c in res:
        if kind != 'ok' or cr: continue
        c = list(c)
        while c and c[-1] == 0: c.pop()
        outs.add(tuple(c))
    return outs

# ---- abstract items and output canonicalisation ----
def aadd(a, b):
    if type(a) is int and type(b) is int:
        return ab(a + b)
    return 'O' if (par(a) + par(b)) % 2 else 'E'

def tok_cells(t, v=None):
    if t == '|': return [0, 0, 1, 1, 0]
    if type(t) is str and t[0] == 'w': return [int(ch) for ch in t[1:]]
    if type(t) is str and t[0] == 'W': return [1] * v + [0] * (len(t) - 2)
    return [0, 1] * v

def wreps(t):
    p = 1 if t[1] == 'O' else 0
    sm = [v for v in range(A1 + 1, A1 + 7) if v % 2 == p]
    return sm, [40 + p, 62 + p]

@functools.lru_cache(maxsize=None)
def behaviours(t, cl, start=False):
    """frozenset of (cr, out) where out is a tuple of abstract items (runs as ('R', value) and cells 0/1)."""
    res = set()
    if t == '|' or (type(t) is str and t[0] == 'w'):
        for k, cr, c in tsim(tok_cells(t), cl, start):
            res.add((k, cr, tuple(absitems(c, None))))
        return frozenset(res)
    small, large = wreps(t) if (type(t) is str and t[0] == 'W') else reps(t)
    for v in small:
        for k, cr, c in tsim(tok_cells(t, v), cl, start):
            res.add((k, cr, tuple(absitems(c, None))))
    if large:
        sets = []
        for v in large:
            sets.append({(k, cr, tuple(absitems(c, v))) for k, cr, c in tsim(tok_cells(t, v), cl, start)})
        if sets[0] != sets[1]: raise Loop(('nonuniform', t, cl, sets[0] ^ sets[1]))
        res |= sets[0]
    return frozenset(res)

def absitems(c, big):
    """items of the token's new cells, with runs abstracted (big: the rep, so runs within 10 of it are abstract)"""
    out = []
    for x in cells_to_items(list(c)):
        if type(x) is list: out.append(('R', ab(x[0])))
        else: out.append(x)
    # long blocks of literal 1s become ('ONES', class)
    res = []; i = 0
    while i < len(out):
        if out[i] == 1:
            j = i
            while j < len(out) and out[j] == 1: j += 1
            if j - i > A1: res.append(('ONES', ab1(j - i)))
            else: res += [1] * (j - i)
            i = j
        else: res.append(out[i]); i += 1
    return res

def norm(items):
    out = []
    for x in items:
        if type(x) is list:
            if x[0] == 0: continue
            if out and type(out[-1]) is list: out[-1] = [out[-1][0] + x[0]]
            else: out.append([x[0]])
        elif x == 1 and out and out[-1] == 0:
            out.pop()
            if out and type(out[-1]) is list: out[-1] = [out[-1][0] + 1]
            else: out.append([1])
        else: out.append(x)
    return out

def toks_of(items):
    out = []; buf = ''
    for x in items:
        if type(x) is list:
            if buf: out.append('w' + buf); buf = ''
            out.append(x[0])
        else: buf += str(x)
    if buf: out.append('w' + buf)
    return out

BADW = {'w11000', 'w111000'}

class Lang:
    def __init__(s):
        s.G = set(); s.idx = collections.defaultdict(set); s.new = 0; s.par = {}; s.bad = []
    def key(s, seq): return tuple(seq[-(N - 1):]) if len(seq) >= N - 1 else tuple(seq)
    def addg(s, g, why):
        if g in s.G: return
        s.G.add(g); s.new += 1; s.par[g] = why
        for i in range(len(g) - 2):
            if (g[i] in BADW or (type(g[i]) is str and g[i][0] == 'W' and g[i].endswith('000'))) and g[i + 1] == 1 and isword(g[i + 2]) and g[i + 2].startswith('w10'): s.bad.append(g); break
        if g[0] == '^':
            for k in range(1, len(g)): s.idx[g[:k]].add(g[k])
        if len(g) == N: s.idx[g[:-1]].add(g[-1])
    def rec(s, seq, why):
        seq = tuple(seq)
        if len(seq) >= N:
            for i in range(len(seq) - N + 1): s.addg(seq[i:i + N], why)
        else:
            if seq[0] == '^' and seq[-1] == '$': s.addg(seq, why)
            else: raise AssertionError(('short', seq))
    def nexts(s, seq): return tuple(s.idx.get(s.key(seq), ()))

def cut(L):
    for g in list(L.G):
        if g[0] == '^' and len(g) > 1 and isrun(g[1]):
            if g[2:] == ('$',): continue
            if g[-1] == '$' or len(g) < N: L.rec(('^',) + g[2:], ('cut', g))
            else:
                for t in L.nexts(list(g)): L.rec(('^',) + g[2:] + (t,), ('cut', g))

PROBS = collections.Counter()
def addones(a, b):
    if type(a) is int and type(b) is int: return ab1(a + b)
    return 'O' if (par(a) + par(b)) % 2 else 'E'

def push(pend, x):
    pend = list(pend)
    if type(x) is tuple and x[0] == 'ONES':
        if pend and pend[-1] == 0: PROBS['0 before ONES'] += 1
        if pend and type(pend[-1]) is tuple and pend[-1][0] == 'ONES': pend[-1] = ('ONES', addones(pend[-1][1], x[1]))
        else:
            k = 0
            while pend and pend[-1] == 1: pend.pop(); k += 1
            pend.append(('ONES', addones(x[1], k)))
        return pend
    if x == 1 and pend and type(pend[-1]) is tuple and pend[-1][0] == 'ONES':
        pend[-1] = ('ONES', addones(pend[-1][1], 1)); return pend
    if x == 1 and pend and pend[-1] == 1:
        k = 0
        while k < len(pend) and pend[-1 - k] == 1: k += 1
        if k + 1 > A1:
            del pend[-k:]; pend.append(('ONES', ab1(k + 1))); return pend
    if type(x) is tuple and x[0] == 'R':
        if pend and type(pend[-1]) is tuple: pend[-1] = ('R', aadd(pend[-1][1], x[1]))
        else: pend.append(x)
    elif x == 1 and pend and pend[-1] == 0:
        pend.pop()
        if pend and type(pend[-1]) is tuple: pend[-1] = ('R', aadd(pend[-1][1], 1))
        else: pend.append(('R', 1))
    else: pend.append(x)
    return pend

def word(buf):
    ones = 0; zeros = 0; n = 0
    for x in buf:
        n += 1
        if type(x) is tuple: ones = addones(ones, x[1]) if ones else x[1]
        elif x == 1:
            if zeros: PROBS['1 after 0 in word'] += 1
            ones = addones(ones, 1) if ones else 1
        else: zeros += 1
    if type(ones) is int and ones <= A1: return ('w' + '1' * ones + '0' * zeros, n)
    return ('W' + ones + '0' * zeros, n)

def tokens(items):
    out = []; buf = []
    for x in items:
        if type(x) is tuple and x[0] == 'R':
            if buf: out.append(word(buf)); buf = []
            out.append((x[1], 1))
        else: buf.append(x)
    if buf: out.append(word(buf))
    return out

class Comp:
    def __init__(s, L):
        s.L = L; s.halts = []; s.prob = []; s.nnodes = 0

    def build(s):
        """forward product graph; nodes (lkey, cs, flag); edges (node, label, node2); ACC terminal"""
        L = s.L
        succ = collections.defaultdict(set)
        firsts = [t for t in L.nexts(('^',)) if t != '$']
        for t1 in firsts:
            k1 = L.key(['^', t1])
            for kind, seq, outc in LB:
                flag = {'ok': 'n', 'open': 'o', 'halt': 'h'}[kind]
                try: bs = behaviours(t1, seq, True)
                except Loop as e: s.prob.append(('loop', t1, str(e)[:200])); continue
                for k2, cr, out in bs:
                    f2 = s.flag(flag, k2)
                    if f2 is None: continue
                    node = (k1, cr, f2)
                    lab = tuple(outc) + out
                    succ[('START',)].add((lab, node))
        seen = set(); Q = [n for _, n in succ[('START',)]]
        for n in Q: seen.add(n)
        while Q:
            node = Q.pop(); k, cs, f = node
            for t in L.nexts(k):
                if t == '$':
                    if f == 'n':
                        for c in rreg_ok(cs): succ[node].add((tuple(c), 'ACC'))
                    elif f == 'h':
                        for c in rreg_ok(cs): succ[node].add((tuple(c), 'HALT'))
                    else:
                        if rreg_halts(cs): succ[node].add(((), 'HALT'))
                    continue
                try: bs = behaviours(t, cs, False)
                except Loop as e: s.prob.append(('loop', t, str(e)[:200])); continue
                k2 = L.key(list(k) + [t])
                for kind, cr, out in bs:
                    f2 = s.flag(f, kind)
                    if f2 is None: continue
                    n2 = (k2, cr, f2)
                    succ[node].add((out, n2))
                    if n2 not in seen: seen.add(n2); Q.append(n2)
        s.nnodes = len(seen)
        return succ

    @staticmethod
    def flag(f, kind):
        if f == 'n': return {'ok': 'n', 'open': 'o', 'halt': 'h'}[kind]
        if f == 'o': return {'open': 'o', 'halt': 'h'}.get(kind)
        if f == 'h': return 'h' if kind == 'ok' else None

    def trim(s, succ):
        pred = collections.defaultdict(set)
        for a, es in succ.items():
            for lab, b in es: pred[b].add(a)
        live = set(); Q = ['ACC', 'HALT']
        live.update(Q)
        while Q:
            b = Q.pop()
            for a in pred[b]:
                if a not in live: live.add(a); Q.append(a)
        # halts: is HALT reachable from START?
        return live

    def emit(s, succ, live, out):
        """walk the trimmed graph with the output canonicaliser; record grams into out (a Lang)."""
        if 'HALT' in live and ('START',) in live:
            # find whether a START->HALT path exists
            pass
        st0 = (('START',), ('^',), ())
        seen = {st0}; Q = [st0]
        while Q:
            node, ctx, pend = Q.pop()
            for lab, b in succ.get(node, ()):
                if b not in live: continue
                if b == 'HALT':
                    s.halts.append((node, ctx)); continue
                p = list(pend)
                for x in lab: p = push(p, x)
                c = ctx
                if b == 'ACC':
                    while p and p[-1] == 0: p.pop()
                    toks = [t for t, _ in tokens(p)] + ['$']
                    out.rec(list(c) + toks, ('round',)) if len(c) + len(toks) >= N or c[0] == '^' else None
                    continue
                tk = tokens(p)
                # finalize all but the last two tokens
                if len(tk) > 2:
                    fin = tk[:-2]
                    # rebuild pend from the remaining items: drop items belonging to finalized tokens
                    # count items: runs are one item, words are len cells
                    cnt = sum(n for t, n in fin)
                    p = p[cnt:]
                    seq = list(c) + [t for t, _ in fin]
                    if len(seq) >= N or (seq and seq[0] == '^' and False): out.rec(seq, ('round',))
                    c = out.key(seq)
                stt = (b, c, tuple(p))
                if stt not in seen:
                    seen.add(stt); Q.append(stt)
                    if len(seen) > 30000000: s.prob.append(('emit too big',)); return len(seen)
        return len(seen)


def init_toks(R):
    from tok import Sim
    sim = Sim(); sim.run(max_rounds=R)
    return ['^'] + [ab(x) if type(x) is int else x for x in toks_of(sim.toks)] + ['$']

LB = lreg_behaviours()


def cmd_check(seeds, R):
    from tok import round_
    from relax import relaxed
    C = collections.Counter()
    def check(t):
        if not t or len(t) > 400: return
        T = ['^'] + toks_of(t) + ['$']
        L = Lang(); L.rec(T, 'x'); out = Lang()
        c = Comp(L); succ = c.build(); live = c.trim(succ); c.emit(succ, live, out)
        r, _ = round_(t)
        if r is None: C['halt ' + ('found' if c.halts else 'MISSED')] += 1; return
        want = tuple(['^'] + toks_of(r) + ['$'])
        C['agree' if list(out.G) == [want] else 'DISAGREE'] += 1
    for seed in seeds: relaxed(seed, R, 0, watch=check)
    print(dict(C))
    return 0 if set(C) <= {'agree', 'halt found'} else 1


def cmd_closure(R, MAX):
    L = Lang(); t0 = init_toks(R); L.rec(t0, 'init')
    it = 0
    while True:
        it += 1; a = time.time(); L.new = 0
        c = Comp(L); succ = c.build(); live = c.trim(succ); ne = c.emit(succ, live, L); cut(L)
        print(f'round {it}: {len(L.G)} grams (+{L.new}), {c.nnodes} product nodes, {len(live)} live, {ne} output '
              f'states, {len(c.halts)} halts, {len(L.bad)} with 110/1110 before a separator, {len(c.prob)} problems, '
              f'{time.time()-a:.0f}s', flush=True)
        if c.halts or L.bad or L.new == 0 or len(L.G) > MAX: break
    print('closed' if L.new == 0 else 'stopped')
    return 0


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'check'
    if cmd == 'check':
        a, b = map(int, (sys.argv[2] if len(sys.argv) > 2 else '1-2').split('-'))
        sys.exit(cmd_check(range(a, b + 1), int(sys.argv[3]) if len(sys.argv) > 3 else 400))
    if cmd == 'closure':
        sys.exit(cmd_closure(int(sys.argv[2]) if len(sys.argv) > 2 else 300, int(sys.argv[3]) if len(sys.argv) > 3 else 200000))
