"""An accelerated simulator for the 'two counters' machines.

A tick configuration: the head in state S on the first cell of a header word H; left of the head the gap G, then
the up-counter U: digits D0/D1 (W cells each, least significant next to the gap), then a sentinel 1 over blank
tape; right of H the down-counter V: pairs P0/P1 (bit 0 / bit 1), least significant first.  For each header the
tick rule (U+1, V-1) is proved for all carry/borrow lengths by bbtools.symtm (a Lean theorem), which also gives its
step count; runs of ticks are then jumped exactly.  Headers are learned from the run: when candidate ticks match
no known header, the longest common prefix of a few consecutive ones is tried.
"""
import os, sys, re, time, subprocess, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'py'))
from bbtools.machine import Machine
from bbtools.symtm import prove, ProofError

def pc(n): return bin(n).count('1')
def sum_tz(a, b):
    if b < a: return 0
    return (b - pc(b)) - ((a - 1) - pc(a - 1))

def parse_cost(expr):
    """'8 * i + 10 * j + 94' -> dict"""
    d = {'i': 0, 'j': 0, 'c': 0}
    for t in expr.replace('(', '').replace(')', '').split('+'):
        t = t.strip()
        if '*' in t:
            a, v = t.split('*'); d[v.strip()] = int(a)
        elif t in ('i', 'j'): d[t] = 1
        else: d['c'] += int(t)
    return d

def _fastdirect():
    """compile ../c/fastdirect.c into a temporary directory (once) and return the shared library's path"""
    src = os.path.join(HERE, '..', 'c', 'fastdirect.c')
    out = os.path.join(tempfile.gettempdir(), 'g12_fastdirect_%d.so' % int(os.path.getmtime(src)))
    if not os.path.exists(out):
        subprocess.run(['gcc', '-O2', '-shared', '-fPIC', '-o', out, src], check=True)
    return out


class Counter2:
    def __init__(self, text, S, W=5, D0="00000", D1="00001", G="00", P0="11", P1="01", sent="1", log=print):
        self.text = text; self.m = Machine.parse(text); self.S = "ABCDEF".index(S); self.Sn = S
        self.W, self.D0, self.D1, self.G, self.P0, self.P1 = W, D0, D1, G, P0, P1
        self.c = bytearray(1 << 14); self.off = 1 << 13
        self.pos = 0; self.state = 0; self.steps = 0; self.lo = 0; self.hi = 0; self.halted = False
        self.tab = [self.m.table[s][y] for s in range(self.m.n) for y in (0, 1)]
        self.headers = {}   # header -> (a0, b0, cu, cv, lean texts)
        self.r1 = 1; self.log = log; self.ticks = 0; self.lean = []; self.failed = set()

    # tape
    def grow(self):
        n = len(self.c); new = bytearray(3 * n); new[n:2 * n] = self.c; self.c = new; self.off += n
    def get(self, p):
        i = p + self.off
        return self.c[i] if 0 <= i < len(self.c) else 0
    def setc(self, p, v):
        while not (0 <= p + self.off < len(self.c)): self.grow()
        self.c[p + self.off] = v
        self.lo = min(self.lo, p); self.hi = max(self.hi, p)

    def tape_str(self, lo=None, hi=None):
        lo = self.lo if lo is None else lo; hi = self.hi if hi is None else hi
        out = []; i = lo
        while i <= hi:
            if i == self.pos:
                out.append("ABCDEF"[self.state] + ">" + str(self.get(i))); i += 1; continue
            v = self.get(i); j = i
            while j <= hi and j != self.pos and self.get(j) == v: j += 1
            out.append(f"{v}^{j - i}" if j - i > 1 else str(v)); i = j
        return " ".join(out)

    # decoding
    def left_counter(self, G=None):
        """(L, U, q): the maximal run of digit words left of the gap G (stopping at a sentinel 1 over blank tape or at
        the first word that is not a digit); the tick rule never looks past them while U < 2^L - 1"""
        G = self.G if G is None else G
        h = self.pos; g = self.get; ng = len(G)
        for i in range(ng):
            if g(h - ng + i) != int(G[i]): return None
        q = h - ng; L = 0; U = 0; W = self.W
        while True:
            if q - 1 < self.lo: return (L, U, q) if L else None
            if g(q - 1) == 1 and all(g(r) == 0 for r in range(self.lo, q - 1)):
                return (L, U, q) if L else None
            w = "".join(str(g(q - W + i)) for i in range(W))
            if w == self.D0: pass
            elif w == self.D1: U |= 1 << L
            else: return (L, U, q) if L else None
            L += 1; q -= W

    def right_counter(self, start):
        g = self.get; r = start; V = 0; nb = 0; n = len(self.P0)
        while r + n - 1 <= self.hi:
            w = "".join(str(g(r + i)) for i in range(n))
            if w == self.P0: pass
            elif w == self.P1: V |= 1 << nb
            else: break
            nb += 1; r += n
        return V, nb

    def candidate(self):
        """the decode of the left counter with the gap (G, G0, G00, ...) that gives the most digits: (G, lc)"""
        if self.state != self.S: return None
        best = None
        for e in range(self.W):
            G = self.G + "0" * e
            lc = self.left_counter(G)
            if lc is not None and (best is None or lc[0] > best[1][0]): best = (G, lc)
        return best

    def match(self):
        cd = self.candidate()
        if cd is None: return None
        G, lc = cd
        best = None
        for (G2, H) in self.headers:
            if G2 != G: continue
            if all(self.get(self.pos + i) == int(H[i]) for i in range(len(H))):
                if best is None or len(H) > len(best): best = H
        if best is None: return ('cand', lc, G)
        V, nb = self.right_counter(self.pos + len(best))
        if nb == 0: return ('cand', lc, G)
        return ('tick', lc, (G, best), V, nb)

    # rules
    def learn(self, key):
        """prove the two tick rules for the gap and header key = (G, H); returns True if both hold"""
        G, H = key
        D0, D1, P0, P1 = self.D0, self.D1, self.P0, self.P1
        sp = lambda w: w
        Hs = H[0] + " " + H[1:] if len(H) > 1 else H
        try:
            sA = f"L {D0} ({D1})^j {G} {self.Sn}> {Hs} {P1} R"
            eA = f"L {D1} ({D0})^j {G} {self.Sn}> {Hs} {P0} R"
            tA, fA = prove(self.text, "tickA", sA, eA, rotate=True)
            sB = f"L {D0} ({D1})^j {G} {self.Sn}> {Hs} ({P0})^i+1 {P1} R"
            eB = f"L {D1} ({D0})^j {G} {self.Sn}> {Hs} ({P1})^i+1 {P0} R"
            tB, fB = prove(self.text, "tickB", sB, eB, rotate=True)
        except ProofError as e:
            self.log(f"  gap {G} header {H}: no rule ({e})"); return False
        ca = parse_cost(re.search(r"steps \((.*?)\) ⟨", tA).group(1))
        cb = parse_cost(re.search(r"steps \((.*?)\) ⟨", tB).group(1))
        a0, cu = ca['c'], ca['j']; b0, cv = cb['c'], cb['i']
        assert cb['j'] == cu
        self.headers[key] = (a0, b0, cu, cv); self.lean.append((key, tA, tB))
        self.log(f"  learned gap {G} header {H}: cost {a0}+{cu}j (V odd), {b0}+{cv}(b-1)+{cu}j (b trailing zeros of V)")
        return True

    def jump(self, lc, key, V, nb):
        L, U, q = lc
        a0, b0, cu, cv = self.headers[key]
        G, H = key
        k = min((1 << L) - 1 - U, V)
        if k <= 0: return 0
        nbz = V // 2 - (V - k) // 2           # ticks with V even (b >= 1)
        cost = a0 * k + cu * sum_tz(U + 1, U + k) + (b0 - a0 - cv) * nbz + cv * sum_tz(V - k + 1, V)
        self._write(lc, key, U + k, V - k, nb)
        self.steps += cost; self.ticks += k
        return k

    def _write(self, lc, key, U2, V2, nb):
        G, H = key; L = lc[0]
        h = self.pos; ng = len(G); W = self.W
        for j in range(L):
            w = self.D1 if (U2 >> j) & 1 else self.D0
            base = h - ng - W * (j + 1)
            for i in range(W): self.setc(base + i, int(w[i]))
        base = h + len(H); n = len(self.P0)
        for j in range(nb):
            w = self.P1 if (V2 >> j) & 1 else self.P0
            for i in range(n): self.setc(base + n * j + i, int(w[i]))

    def direct(self, n):
        """n steps (or until halt), no checks; fast loop"""
        tab = self.tab; c = self.c; off = self.off; p = self.pos; s = self.state; k = 0
        lo = self.lo; hi = self.hi
        while k < n:
            i = p + off
            if i < 1 or i >= len(c) - 1:
                self.c = c; self.grow(); c = self.c; off = self.off; i = p + off
            tr = tab[2 * s + c[i]]
            if tr is None: self.halted = True; k += 1; break
            c[i] = tr[0]; p += tr[1]; s = tr[2]; k += 1
            if p < lo: lo = p
            elif p > hi: hi = p
        self.c = c; self.pos = p; self.state = s; self.steps += k; self.lo = lo; self.hi = hi
        return k

    def step_to_S(self, maxn):
        """direct steps until the head is in state S on a 0 again (at least one step); in C"""
        import ctypes
        if not hasattr(self, '_lib'):
            self._lib = ctypes.CDLL(_fastdirect())
            flat = []
            for tr in self.tab:
                flat += [0, 0, -1] if tr is None else [tr[0], tr[1], tr[2]]
            self._tab = (ctypes.c_int * len(flat))(*flat)
        done = 0
        while done < maxn:
            buf = (ctypes.c_ubyte * len(self.c)).from_buffer(self.c)
            io = (ctypes.c_longlong * 6)(self.pos + self.off, self.state, self.lo + self.off, self.hi + self.off, 0, 0)
            g = bytes(int(x) for x in self.G)
            self._lib.run(buf, ctypes.c_longlong(len(self.c)), self._tab, self.S, g, len(g), self.r1,
                          ctypes.c_longlong(maxn - done), io)
            del buf
            self.pos = io[0] - self.off; self.state = io[1]; self.lo = io[2] - self.off; self.hi = io[3] - self.off
            self.steps += io[4]; done += io[4]
            if io[5] == 2: self.halted = True; return done
            if io[5] == 3: self.grow(); continue
            return done
        return done

    def run(self, max_steps, max_direct=10**9, on_tick=None, on_cand=None, exact=False):
        """run until max_steps (exact=True: stop at exactly max_steps), a halt, or max_direct steps without a tick"""
        direct_since = 0; cands = []
        while self.steps < max_steps and not self.halted:
            lim = max_direct
            if exact: lim = min(lim, max_steps - self.steps)
            k = self.step_to_S(lim)
            direct_since += k
            if self.halted: return 'halt'
            if exact and self.steps >= max_steps: return 'max'
            if direct_since >= max_direct: return 'stuck'
            mt = self.match()
            if mt is None: continue
            if mt[0] == 'cand':
                cands.append((mt[2], self.get_r(300)))
                if len(cands) >= 48:
                    for G in set(g for g, _ in cands):
                        for H in learn_headers([x for g, x in cands if g == G]):
                            key = (G, H)
                            if key not in self.headers and key not in self.failed:
                                if not self.learn(key): self.failed.add(key)
                    cands = []
                if on_cand: on_cand(self, mt)
                continue
            cands = []
            _, lc, H, V, nb = mt
            if on_tick: on_tick(self, lc, H, V, nb)
            direct_since = 0
            if exact:
                L, U, q = lc
                kmax = min((1 << L) - 1 - U, V)
                lo_, hi_ = 0, kmax
                while lo_ < hi_:
                    mid = (lo_ + hi_ + 1) // 2
                    if self.cost(lc, H, V, mid) <= max_steps - self.steps: lo_ = mid
                    else: hi_ = mid - 1
                if lo_ > 0: self._jumpk(lc, H, V, nb, lo_)
            else:
                self.jump(lc, H, V, nb)
        return 'max'

    def cost(self, lc, key, V, k):
        L, U, q = lc
        a0, b0, cu, cv = self.headers[key]
        nbz = V // 2 - (V - k) // 2
        return a0 * k + cu * sum_tz(U + 1, U + k) + (b0 - a0 - cv) * nbz + cv * sum_tz(V - k + 1, V)

    def get_r(self, n):
        return "".join(str(self.get(self.pos + i)) for i in range(n))

def lcp(a):
    l = min(len(x) for x in a); i = 0
    while i < l and all(x[i] == a[0][i] for x in a): i += 1
    return i

def learn_headers(cands, k=4):
    """candidate headers: group the right-hand sides by their first k cells; in each group of at least 4 that do not
    all agree, the longest common prefix"""
    groups = {}
    for x in cands: groups.setdefault(x[:k], []).append(x)
    out = []
    for g in sorted(groups.values(), key=len, reverse=True):
        if len(g) < 4: continue
        i = lcp(g)
        if i < len(g[0]): out.append(g[0][:i])
    return out

def _jumpk(self, lc, key, V, nb, k):
    L, U, q = lc
    cost = self.cost(lc, key, V, k)
    self._write(lc, key, U + k, V - k, nb)
    self.steps += cost; self.ticks += k
Counter2._jumpk = _jumpk


# The machines of this family in holdouts/ (G12): the tick state and the digit words.
MACHINES = {
    "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB": dict(S="D"),
    "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC": dict(S="D"),
    "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---": dict(S="E"),
    "1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---": dict(S="F"),
    "1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE": dict(S="D", W=3, D0="000", D1="100", G="0"),
}


def make(machine, log=print):
    kw = dict(MACHINES[machine])
    S = kw.pop("S")
    c = Counter2(machine, S, log=log, **kw)
    c.sentw = "1"
    return c
