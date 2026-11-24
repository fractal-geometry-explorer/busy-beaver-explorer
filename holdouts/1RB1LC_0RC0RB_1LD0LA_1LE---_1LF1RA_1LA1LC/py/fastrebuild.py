"""A faster exact rebuild for 1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC, the walk that decides its halts, and checks.

The exact rebuild is the one of the family (holdouts/1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB/py/rebuild.py): tick
runs jumped by the proved tick rules, everything else simulated cell by cell.  This module only makes it faster,
with the same results (`check_speed` compares the first rebuilds from blank tape state by state):
  * the C loop (../c/stops.c) stops only where state S reads 0 with the gap on its left AND a known header on its
    right, instead of at every 0 read in state S (the run of this machine has millions of those per rebuild);
  * decoding the counters and writing them back use byte slices and regular expressions instead of cell loops;
  * no new headers are learned inside a rebuild (the two of the family are the only ones its sub-phases use).
Rebuild 7 from blank tape (V of 3,287 digits) took more than 10 minutes before and takes 15 s now.

The rebuilds come in four kinds, by header and top word of the counter (N = top word + L digits U):
  A  header 0110101, top 1      -> header 0110111, top 1000x, n+1;  delta = 2^L - U  (all digits read)
  B  header 0110111, top 1000x  -> header 0110101 (mostly), top 1, N' = 2 (all digits read)
  C  header 0110111, top 1      -> header 0110101, top 1000, N' = 2^(L-j+1): the walk below reads j digits,
                                   n + 5j/2 + 1, delta = c(U mod 2^j) + 2^(L-j) - (U >> j)  (U >> j > 0)
  D  header 0110101, top 1000x  -> top 1, N' = 2 (all digits read)
`walk` reads U from the bottom in pairs: a first pair 01 or 10 stops it (j = 2); otherwise add 1 to U if its
lowest pair is 11, and stop at the first pair 2k-1, 2k (k >= 2) whose upper digit is 1 (j = 2k).

usage: python3 fastrebuild.py run SECONDS             macro run from blank tape (one line per rebuild)
       python3 fastrebuild.py speed K                 first K rebuilds: fast = original, state by state
       python3 fastrebuild.py halting L               B and D rebuilds, all U < 2^l, l <= L: halts vs the walk
       python3 fastrebuild.py table L                 the same, every row
       python3 fastrebuild.py kinds L                 A and C rebuilds, all U < 2^L: the formulas above
"""
import os, sys, re, time, math, pickle, ctypes, subprocess, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
FAM = os.path.join(HERE, '..', '..', '1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB', 'py')
sys.path.insert(0, FAM)
import counters, rebuild as _rb
M = "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC"
C = counters.Counter2
_NAMES = ("left_counter", "right_counter", "match", "_write", "step_to_S")
_ORIG = {k: getattr(C, k) for k in _NAMES}; _ORIG_CLASSIFY = _rb.Rebuilder.classify
def left_counter(self, G=None):
    G = self.G if G is None else G
    h = self.pos; ng = len(G); off=self.off; c=self.c
    if bytes(c[h-ng+off:h+off]) != bytes(int(x) for x in G): return None
    q = h - ng; L = 0; U = 0; W = self.W
    D0=bytes(int(x) for x in self.D0); D1=bytes(int(x) for x in self.D1)
    lo=self.lo
    # position of the leftmost 1 on the tape
    first1 = c.find(1, lo+off)
    first1 = first1-off if first1>=0 else None
    while True:
        if q - 1 < lo: return (L, U, q) if L else None
        if c[q-1+off] == 1 and first1 == q-1: return (L, U, q) if L else None
        w = bytes(c[q-W+off:q+off]) if q-W>=lo else bytes(self.get(q-W+i) for i in range(W))
        if w == D0: pass
        elif w == D1: U |= 1 << L
        else: return (L, U, q) if L else None
        L += 1; q -= W
def right_counter(self, start):
    off=self.off; c=self.c; n=len(self.P0); r=start; V=0; nb=0
    P0=bytes(int(x) for x in self.P0); P1=bytes(int(x) for x in self.P1)
    bits=[]
    while r + n - 1 <= self.hi:
        w = bytes(c[r+off:r+off+n])
        if w == P0: bits.append('0')
        elif w == P1: bits.append('1')
        else: break
        r += n
    nb=len(bits)
    V=int(''.join(reversed(bits)),2) if bits else 0
    return V, nb
_orig_match=C.match
def match(self):
    if self.state != self.S: return None
    off=self.off; c=self.c; p=self.pos
    ok=False
    for (G2,H) in self.headers:
        if bytes(c[p+off:p+off+len(H)])==bytes(int(x) for x in H): ok=True; break
    if not ok and getattr(self,'known_only',False): return None
    return _orig_match(self)
C.left_counter=left_counter; C.right_counter=right_counter; C.match=match
def _write(self, lc, key, U2, V2, nb):
    G, H = key; L = lc[0]
    h = self.pos; ng = len(G); W = self.W; n = len(self.P0)
    lo_cell = h - ng - W * L; hi_cell = h + len(H) + n * nb - 1
    while not (0 <= lo_cell + self.off and hi_cell + self.off < len(self.c)): self.grow()
    D0=bytes(int(x) for x in self.D0); D1=bytes(int(x) for x in self.D1)
    bits=format(U2,'0%db'%L) if L else ''
    if len(bits)>L: bits=bits[-L:]
    left=b''.join(D1 if b=='1' else D0 for b in bits)   # most significant first = leftmost
    o=self.off
    self.c[lo_cell+o:h-ng+o]=left
    P0=bytes(int(x) for x in self.P0); P1=bytes(int(x) for x in self.P1)
    vb=format(V2,'0%db'%nb)[::-1] if nb else ''
    right=b''.join(P1 if b=='1' else P0 for b in vb)
    base=h+len(H)
    self.c[base+o:base+o+n*nb]=right
    self.lo=min(self.lo,lo_cell); self.hi=max(self.hi,hi_cell)
C._write=_write
def _stops():
    src = os.path.join(HERE, '..', 'c', 'stops.c')
    out = os.path.join(tempfile.gettempdir(), 'g12_stops_%d.so' % int(os.path.getmtime(src)))
    if not os.path.exists(out): subprocess.run(['gcc', '-O2', '-shared', '-fPIC', '-o', out, src], check=True)
    return out
_lib2 = ctypes.CDLL(_stops())
HDR_PREFIX = "01101"   # the common prefix of the two headers
_orig_step=C.step_to_S
def step_to_S(self, maxn):
    if HDR_PREFIX is None or not getattr(self,'known_only',False): return _orig_step(self, maxn)
    if not hasattr(self, '_tab2'):
        flat = []
        for tr in self.tab: flat += [0, 0, -1] if tr is None else [tr[0], tr[1], tr[2]]
        self._tab2 = (ctypes.c_int * len(flat))(*flat)
        self._g2 = bytes(int(x) for x in self.G); self._h2 = bytes(int(x) for x in HDR_PREFIX)
    done = 0
    while done < maxn:
        buf = (ctypes.c_ubyte * len(self.c)).from_buffer(self.c)
        io = (ctypes.c_longlong * 6)(self.pos + self.off, self.state, self.lo + self.off, self.hi + self.off, 0, 0)
        _lib2.run(buf, ctypes.c_longlong(len(self.c)), self._tab2, self.S, self._g2, len(self._g2), self._h2, len(self._h2),
                  ctypes.c_longlong(maxn - done), io)
        del buf
        self.pos = io[0] - self.off; self.state = io[1]; self.lo = io[2] - self.off; self.hi = io[3] - self.off
        self.steps += io[4]; done += io[4]
        if io[5] == 2: self.halted = True; return done
        if io[5] == 3: self.grow(); continue
        return done
    return done
C.step_to_S=step_to_S
def classify(self, c, lc, key, nb):
    L, U, q = lc
    if key[0] != self.G: return None
    o=c.off
    seg=bytes(c.c[max(c.lo,0-o)+o:q+o]) if q> c.lo else b''
    i=seg.find(1)
    left='' if i<0 else ''.join('1' if x else '0' for x in seg[i:])
    if left not in self.forms: return None
    r0 = c.pos + len(key[1]) + 2 * nb
    seg=bytes(c.c[r0+o:c.hi+o+1]).rstrip(b'\x00')
    return left if seg == b'\x01' else None
_rb.Rebuilder.classify=classify
_WRE={}
def left_counter2(self, G=None):
    G = self.G if G is None else G
    h = self.pos; ng = len(G); off=self.off; c=self.c; W=self.W
    if bytes(c[h-ng+off:h+off]) != bytes(int(x) for x in G): return None
    if self.D0 != "0"*(W) or self.D1 != "0"*(W-1)+"1": return left_counter(self, G)
    q = h - ng; lo=self.lo
    if q-1 < lo: return None
    seg = bytes(W) + bytes(c[lo+off:q+off])          # padded
    rx=_WRE.get(W)
    if rx is None: rx=_WRE[W]=re.compile(b'(?:[\x00\x01]' + b'\x00'*(W-1) + b')*')
    m=rx.match(seg[::-1])
    K=m.end()//W
    # words must have their last cell >= lo: last cell of word t (1-based from right) is q-1-(t-1)W
    K=min(K, (q-1-lo)//W+1)
    first1=c.find(1, lo+off); first1 = first1-off if first1>=0 else None
    if first1 is not None and first1 <= q-1 and (q-1-first1)%W==0:
        t=(q-1-first1)//W   # words right of the sentinel word
        if t < K: K=t
    if K==0: return None
    region=seg[len(seg)-K*W:]
    bits=region[W-1::W]   # last cells, most significant first
    U=int(bytes(48+x for x in bits).decode(),2)
    return (K, U, q-K*W)
C.left_counter=left_counter2
_PRE=re.compile(b'(?:[\x00\x01]\x01)*')
def right_counter2(self, start):
    if self.P0!="11" or self.P1!="01": return right_counter(self,start)
    off=self.off; c=self.c
    seg=bytes(c[start+off:self.hi+off+1])
    m=_PRE.match(seg); nb=m.end()//2
    if nb==0: return 0,0
    firsts=seg[0:2*nb:2]          # first cell of each pair: 0 -> bit 1 (P1=01), 1 -> bit 0
    V=int(bytes(49-x for x in firsts[::-1]).decode(),2)
    return V, nb
C.right_counter=right_counter2

_orig_setup = _rb.Rebuilder.setup
def _setup(self, tape, pos):
    c = _orig_setup(self, tape, pos); c.known_only = True; return c


_FAST = {k: getattr(C, k) for k in _NAMES}; _FAST_CLASSIFY = _rb.Rebuilder.classify


def fast():
    """switch the family's simulator to the fast path"""
    for k, v in _FAST.items(): setattr(C, k, v)
    _rb.Rebuilder.classify = _FAST_CLASSIFY; _rb.Rebuilder.setup = _setup


def slow():
    """back to the family's own code"""
    for k, v in _ORIG.items(): setattr(C, k, v)
    _rb.Rebuilder.classify = _ORIG_CLASSIFY; _rb.Rebuilder.setup = _orig_setup


def walk(U, L):
    """digits read by the walk of a C rebuild, None if it does not stop within the L digits of U"""
    if L >= 2 and (U & 3) in (1, 2): return 2
    V = U + 1 if (U & 3) == 3 else U
    k = 2
    while 2 * k <= L:
        if (V >> (2 * k - 1)) & 1: return 2 * k
        k += 1
    return None


def kind(H, form):
    return {("0110101", "1"): "A", ("0110111", "1000"): "B", ("0110111", "1"): "C", ("0110101", "1000"): "D"}[(H, form)]


def split(N, form):
    """(L, x, U) of a counter N with top word 1 (x = None) or 1000x"""
    if form == "1": L = N.bit_length() - 1; return L, None, N - (1 << L)
    L = N.bit_length() - 2; return L, (N >> L) & 1, N & ((1 << L) - 1)


def macro(secs, out=print, K=10 ** 9):
    fast(); rb = _rb.Rebuilder(M)
    H, n, N, form, steps = _rb.first_state(M, rb)
    out(f"first V=0 at step {steps}: H={H} n={n} N={N}")
    t0 = time.time(); hist = []
    for it in range(K):
        if time.time() - t0 > secs: break
        L, x, U = split(N, form); kd = kind(H, form)
        w = walk(U, L) if kd in "BCD" else None
        r = rb.rebuild(H, n, N, form)
        if r[0] != "OK":
            out(f"{it} {kd}: {r[0]} after {r[1]} steps of the rebuild"); return r[0], hist
        steps += r[1]
        H2, n2, N2, V2, f2, L2 = r[2]
        steps += rb.phase_cost(H2, N2, V2, f2)
        d = (1 << n2) - V2
        hist.append((it, kd, n, L, x, w, H2, n2, N2.bit_length(), d.bit_length()))
        out(f"{it} {kd} n={n} L={L} n-L={n - L}{'' if x is None else ' x=%d' % x} walk={w} -> {H2}/{f2} n'={n2} "
            f"N'~2^{N2.bit_length() - 1} delta~2^{d.bit_length()} log10(steps)={steps.bit_length() * math.log10(2):.1f} "
            f"t={time.time() - t0:.0f}s")
        H, n, N, form = H2, n2, N2 + V2, f2
    return "max", hist


def check_speed(K):
    fast(); a = []; macro(1e9, lambda s: a.append(s.split(' log10')[0].split(' t=')[0]), K)
    slow(); b = []; macro(1e9, lambda s: b.append(s.split(' log10')[0].split(' t=')[0]), K)
    fast()
    print("\n".join(a)); print("equal" if a == b else "DIFFER")
    return a == b


def halting_table(Lmax, out=print):
    """for B and D rebuilds of every U < 2^L (L = 3 .. Lmax), both x and n - L = 0 .. 3: is the set of halting U
    'walk' (exactly the U whose walk does not stop below the top, up to U = all ones), 'none', or 'other'"""
    fast(); rb = _rb.Rebuilder(M); table = {}
    for L in range(3, Lmax + 1):
        pred = set(U for U in range(1 << L) if walk(U, L) is None)
        for H in ("0110111", "0110101"):
            for x in (0, 1):
                form = "1000%d" % x
                for d in (0, 1, 2, 3):
                    hs = set(U for U in range(1 << L)
                             if rb.rebuild(H, L + d, rb.value(form, L, U), form=form, maxd=10 ** 7)[0] == "HALT")
                    v = "none" if not hs else "walk" if not (hs ^ pred) - {(1 << L) - 1} else "other"
                    table[(kind(H, "1000"), x, d, L)] = v
                    out(f"L={L} {kind(H, '1000')} x={x} n-L={d}: {len(hs)} halting U: {v}")
    return table


def check_halting(Lmax):
    """the rule stated in RULE, for every row of halting_table"""
    t = halting_table(Lmax, out=lambda s: None); bad = 0
    for (kd, x, d, L), v in sorted(t.items()):
        want = RULE(kd, x, d, L)
        if want is not None and want != v: bad += 1; print("differs:", kd, x, d, L, v, "expected", want)
    print(f"{len(t)} rows (L <= {Lmax}), {bad} differ from the rule")
    return bad == 0


def RULE(kd, x, d, L):
    """the halting rows: B with x = 0 always, B with x = 1 and D with n - L = 1 for even L, halt exactly where
    the walk runs off the top; D with n - L >= 2 and B with x = 1, L odd never halt; D with n - L = 0 is
    something else (it does not occur in the run, where n > L at every D rebuild)"""
    if kd == "B": return "walk" if x == 0 or L % 2 == 0 else "none"
    if d >= 2: return "none"
    if d == 1: return "walk" if L % 2 == 0 else "none"
    return None


def check_kinds(L):
    fast(); rb = _rb.Rebuilder(M); bad = 0; cs = {}
    for U in range(1 << L):
        N = (1 << L) + U
        for d in (0, 1, 3):
            r = rb.rebuild("0110101", L + d, N, form="1", maxd=10 ** 7)
            H2, n2, N2, V2, f2, L2 = r[2]
            if (H2, n2, N2, f2, (1 << n2) - V2) != ("0110111", L + d + 1, 1 << (L + 1), "1000", (1 << L) - U): bad += 1
            r = rb.rebuild("0110111", L + d, N, form="1", maxd=10 ** 7)
            j = walk(U, L)
            if j is None or j > L - 3 or (U >> j) == 0: continue   # the walk reaches the top digits: not covered
            H2, n2, N2, V2, f2, L2 = r[2]
            c = (1 << n2) - V2 - (1 << (L - j)) + (U >> j)
            key = (j, U & ((1 << j) - 1))
            good = (H2, n2 - L - d, N2, f2) == ("0110101", 5 * j // 2 + 1, 1 << (L - j + 1), "1000") and cs.setdefault(key, c) == c
            if not good: bad += 1
    print(f"L={L}: A and C rebuilds of all U < 2^L, n - L in (0, 1, 3): {bad} differ from the formulas; "
          f"{len(cs)} classes c(U mod 2^j)")
    return bad == 0


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "run": macro(float(sys.argv[2]), lambda s: print(s, flush=True))
    elif cmd == "speed": sys.exit(0 if check_speed(int(sys.argv[2])) else 1)
    elif cmd == "halting": sys.exit(0 if check_halting(int(sys.argv[2])) else 1)
    elif cmd == "table": halting_table(int(sys.argv[2]))
    elif cmd == "kinds": sys.exit(0 if check_kinds(int(sys.argv[2])) else 1)
