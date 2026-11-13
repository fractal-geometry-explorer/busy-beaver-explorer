"""The clock-and-word structure shared by five machines of this batch, and an exact accelerated simulator for it.

At every visit of the left end in state X the tape is `X>0 1^L 0 W`.  One step earlier it was `Y>1 1^(L-1) 0 W`
one cell to the right (Y = the state that enters X there).  Write J(L, W) for `Y>1 1^(L-1) 0 W`.  The *tick*

    0 0 J(L, W)   ->   J(L+2, W')         (two cells to the left)

is, for L = B0 + 2k, exactly 2^k applications of one word map P to W (P = the tick at L = B0): W' = P^(2^k)(W).
Its step count is the sum of the costs of the 2^k P's plus a term D(k) that depends on k only.

This file:
  P(W)          the word map, by running the machine on `0 0 J(B0, W)` (abnormal if the head leaves to the left of
                the two 0s or does not come back as J(B0+2, .));
  Q(k, W)       P^(2^k)(W), memoized on (k, the prefix of W it reads) -- a binary counter in W makes the prefixes
                repeat, so this is fast;
  Hybrid        cell-by-cell simulation, except that at `0 0 J(L, W)` with all 2^k P's normal the tick is done at
                once (time sum + D(k)).  When some P is abnormal the cell-by-cell run goes into the tick, where the
                sub-ticks (smaller L) are again done at once.
D(k) is given per machine by a closed form (checked against the plain run in `check`).

usage: python3 clock.py MACHINE check STEPS      compare with plain simulation at every visit of the left end
       python3 clock.py MACHINE run LOG10STEPS   follow the run, printing the phases
"""
import sys

# the memo that is fastest for each machine (tried for 20 s each): banded or doubling, P with nested ticks or flat
MODES = {
    "1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE": (False, False),
    "1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB": (True, False),
    "1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---": (False, True),
    "1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---": (False, True),
    "1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---": (False, False),
    "1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---": (False, True),
}

# machine: (A, s, Bp, PR) of the sweep `0^g Y> J(B0+g*j, W)` -> `A 0^(s+g*j) Bp Z> PR W` (proved by gen_clock.py)
# when it is not the default ([1], B0 + 1, [1], []) of the first five machines
SWEEP = {
    "1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---": ([0, 1], 5, [], [0]),
    # (..., pz): the P-step starts from 0^pz, the merge reads A 0^(s-pz)
    "1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF": ([0, 0, 0, 1], 6, [], [0], 6),
    # the sweep `0^3 E> 1^(4+3j) 0 W` -> `1 1 1 0^(3+3j) 1 1 A> W`; the P-step `0^3 1 1 A> W` -> `E> 1^4 0 W'`
    "1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB": ([1, 1, 1], 3, [1, 1], [], 3),
}

# machines whose clock is at the right end: simulated (and proved in Lean) as their mirror image
MIRROR = {"1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF"}

# machines whose J is written with the fixed 1s of the block before its repeat (gen_clock.py)
ONES_FIRST = {"1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF"}

# machine: v, the 0s between the head and the block at a visit of the end (default 0)
VISIT = {"1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF": 1}


def mirror(m):
    """The machine with L and R swapped."""
    return "_".join("".join({"L": "R", "R": "L"}.get(ch, ch) for ch in g) for g in m.split("_"))


def sweep_spec(m):
    """(A, s, Bp, PR, pz): the sweep `0^g Y> J(B0+g*j, W)` -> `A 0^(s+g*j) Bp Z> PR W`, the P-step starting
    from `0^pz Bp Z> PR W` (so that the merge reads ML = A 0^(s-pz))."""
    p = PARAMS[m]
    sp = SWEEP.get(m, ([1], p[2] + 1, [1], []))
    return tuple(sp[:4]) + ((sp[4] if len(sp) > 4 else sp[1] - 1),)


PARAMS = {
    # machine: (X, Y, B0)
    "1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE": ("E", "F", 3),
    "1RB0RA_0RC0LE_1LC0LD_1RA1LF_---1LD_1LD1LB": ("F", "D", 2),
    "1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---": ("E", "D", 3),
    "1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---": ("C", "D", 3),
    "1RB0RB_1LC0LE_1RD1LB_1RA0RD_1LB0LF_0LB---": ("B", "C", 3),
    # (X, Y, B0, g, h): growth g per tick, head on a 0 (h = 0) left of the block
    "1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA---": ("B", "D", 3, 3, 0),
    # mirrored (see MIRROR): the visit is C>0 0 1^(5+4j) 0 W, one step after E> 1^(6+4j) 0 W (the tick from
    # 1^2, whose P-step reads a 1 left of it, is not a tick of this form: P here is that tick and the one before)
    "1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF": ("C", "E", 6, 4, 1),
    # the block grows by 3 at the left end; E walks left over it (Y = X = E); base block 1^4
    "1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB": ("E", "E", 4, 3, 1),
}


def table(m):
    T = {}
    for s, g in enumerate(m.split("_")):
        for y in (0, 1):
            x = g[3 * y:3 * y + 3]
            T[(s, y)] = None if x == "---" else (int(x[0]), 1 if x[1] == "R" else -1, "ABCDEF".index(x[2]))
    return T


class Clock:
    def __init__(self, m):
        self.m = m
        X, Y, B0 = PARAMS[m][:3]
        self.g, self.h = PARAMS[m][3:5] if len(PARAMS[m]) > 3 else (2, 1)
        self.X, self.Y, self.B0 = "ABCDEF".index(X), "ABCDEF".index(Y), B0
        self.T = table(mirror(m) if m in MIRROR else m)
        # flat transition arrays for speed
        self.W = [0] * 12
        self.Dm = [0] * 12
        self.S = [0] * 12
        self.H = [False] * 12
        for (s, y), tr in self.T.items():
            i = 2 * s + y
            if tr is None:
                self.H[i] = True
            else:
                self.W[i], self.Dm[i], self.S[i] = tr
        A, s, Bp, PR, pz = sweep_spec(m)
        self.plc = bytearray([0] * pz + Bp)           # the cells left of the head at the start of a P-step
        self.prc = bytearray(PR)                      # and those right of it, before the word
        self.Z, self.base = self.structure(A, s, Bp, A + [0] * (s - pz))
        self.memo = {}       # k -> trie
        self.rmemo = {}      # l -> {prefix: run}
        self.pcalls = 0

    def P(self, W):
        """W: bytes (followed by 0s).  Returns (newprefix, r, cost) with r = number of cells of W read, or
        ('abn', r) when the P-step does not come back as J(B0, .).  The P-step `0^(s-1) Bp Z> PR W` ->
        `Y> J(B0, W')` is run alone, with the head forbidden left of its first cell (so that it holds for every
        left tape, as `PStep` in Clock.lean); the cost returned is that of the tick at k = 0 (the P-step plus the
        sweep and the merge)."""
        B0, g, h = self.B0, self.g, self.h
        G = 8
        off = G + len(self.plc) + len(self.prc)      # index of W[0]
        tp = bytearray(G) + self.plc + self.prc + bytearray(W) + bytearray(64)
        pos, st, t = G + len(self.plc), self.Z, self.base
        Wt, Dm, St, Ht = self.W, self.Dm, self.S, self.H
        hi = pos
        Y = self.Y
        j0 = self.jcells(B0)
        wend = off + len(W) - 1              # the last cell of W (unvisited cells up to it are W's, not 0s)
        self.pcalls += 1
        while True:
            if self.nested and st == Y and pos - g > G and tp[pos] == h and self.zeros_left(tp, pos):
                mres = self.macro_at(tp, pos, hi, wend)
                if mres is not None:
                    tp, pos, hi, c = mres
                    t += c
                    continue
            i = 2 * st + tp[pos]
            if Ht[i]:
                return ("abn", max(0, hi - off + 1))
            tp[pos] = Wt[i]
            pos += Dm[i]
            st = St[i]
            t += 1
            if pos > hi:
                hi = pos
                if hi >= len(tp) - 2:
                    tp += bytearray(len(tp))
            if pos <= G:
                if pos < G:
                    return ("abn", max(0, hi - off + 1))
                if st == Y and tp[G] == h:
                    ok = tp[G:G + len(j0)] == j0
                    if not ok:
                        return ("abn", max(0, hi - off + 1))
                    r = max(0, hi - off + 1)
                    return (bytes(tp[off:off + r]), r, t)

    banded = False
    nested = True

    def structure(self, A, s, Bp, ML):
        """(Z, the steps of the tick at k = 0 other than its P-step): the sweep `0^g Y> J(B0, W)` runs until the
        head first stands at the cell after `A 0^s Bp` (in state Z), and the merge `A 0 Y> h` until the head is in
        state Y on the first cell of A (of ML = A 0^(s-pz), the cells the merge reads)."""
        g, B0 = self.g, self.B0
        tp = bytearray(4) + bytearray(g) + self.jcells(B0) + bytearray(64)
        pos, st, t, end = 4 + g, self.Y, 0, 4 + len(A) + s + len(Bp)
        while pos != end:
            w, d, st = self.T[(st, tp[pos])]
            tp[pos] = w
            pos += d
            t += 1
        Z = st
        tp = bytearray(4) + bytearray(ML) + bytearray([self.h]) + bytearray(64)
        pos, st, t2 = 4 + len(ML), self.Y, 0
        while not (pos == 4 and st == self.Y):
            w, d, st = self.T[(st, tp[pos])]
            tp[pos] = w
            pos += d
            t2 += 1
        return Z, t + t2

    def jcells(self, n):
        """The cells of J with n 1s in the block (n = B0 + g*k), up to the 0 before the word."""
        return bytearray([] if self.h else [0]) + bytearray([1] * n) + bytearray([0])

    def zeros_left(self, tp, p):
        return all(tp[p - 1 - i] == 0 for i in range(self.g))

    def macro_at(self, tp, p, hi, wend=0):
        """The tick at `0 0 J(L, W)` with the head at p (state Y on a 1), done at once if all its P-steps come
        back.  Returns (tape, new head position, new hi, steps) or None.  The tape may be extended on the right."""
        g, h = self.g, self.h
        q = p + 1 - h                     # the first cell of the block
        L = 0
        while tp[q + L] == 1:
            L += 1
        if L < self.B0 or (L - self.B0) % g:
            return None
        k = (L - self.B0) // g
        w0 = q + L + 1
        W = bytes(tp[w0:max(hi, wend) + 1]).rstrip(b"\0")
        if self.banded:
            W2, done, cost, ok = self.advance(W, 2 ** k)
            if not ok:
                return None
            r = max(len(W), len(W2))
            pre = W2 + bytes(r - len(W2))
        else:
            res = self.Q(k, W)
            if res[0] == "abn":
                return None
            pre, r, cost = res
        while w0 + r + 2 >= len(tp):
            tp += bytearray(len(tp))
        tp[p - g:w0 - 1] = self.jcells(L + g)[:-1]
        tp[w0:w0 + r] = pre
        if r:
            hi = max(hi, w0 + r - 1)
        return tp, p - g, hi, cost + D(k, g)

    def Q(self, k, W):
        """P^(2^k)(W): (newprefix, r, cost) or ('abn', r).  Memo: per k a trie on the cells of W; a node at depth r
        holds the result of a computation that read exactly the first r cells."""
        node = self.memo.get(k)
        if node is None:
            node = self.memo[k] = [None, None, None]
        n = len(W)
        i = 0
        while True:
            if node[2] is not None:
                return node[2]
            node = node[W[i] if i < n else 0]
            if node is None:
                break
            i += 1
        if k == 0:
            res = self.P(W)
        else:
            a = self.Q(k - 1, W)
            if a[0] == "abn":
                res = a
            else:
                p1, r1, c1 = a
                W1 = p1 + W[r1:]
                b = self.Q(k - 1, W1)
                if b[0] == "abn":
                    res = ("abn", max(r1, b[1]))
                else:
                    p2, r2, c2 = b
                    r = max(r1, r2)
                    W2 = (p2 + W1[r2:])[:r]
                    if len(W2) < r:
                        W2 = W2 + bytes(r - len(W2))
                    res = (W2, r, c1 + c2)
        r = res[1]
        node = self.memo[k]
        for i in range(r):
            b = W[i] if i < n else 0
            if node[b] is None:
                node[b] = [None, None, None]
            node = node[b]
        node[2] = res
        return res

    # ---- depth-banded memo: runs of P's that each read fewer than r(l) = R0 + DL*l cells ----
    R0, DL = 8, 4

    def R(self, l, W):
        """The maximal run of P's from W in which every P reads at most r(l) cells of the word (stopping before the
        first P that reads more, or is abnormal).  Returns (newprefix, r, count, cost).  Depends on W[:r] only."""
        r = self.R0 + self.DL * l
        key = W[:r]
        if len(key) < r:
            key = key + bytes(r - len(key))
        mk = self.rmemo.setdefault(l, {})
        res = mk.get(key)
        if res is not None:
            return res
        cur, count, cost, it = key, 0, 0, 0
        while True:
            it += 1
            if it > 10 ** 6:
                raise RuntimeError("R: too many rounds")
            if l > 0:
                pre, _, n, c = self.R(l - 1, cur)
                cur = pre + cur[len(pre):]
                count += n
                cost += c
            p = self.Q(0, cur)
            if p[0] == "abn" or p[1] > r:
                break
            cur = p[0] + cur[p[1]:]
            count += 1
            cost += p[2]
        res = (cur, r, count, cost)
        mk[key] = res
        return res

    def advance(self, W, N):
        """Apply P exactly N times (or until an abnormal P).  Returns (W', done, cost, ok)."""
        done, cost = 0, 0
        while done < N:
            l = max(0, (len(W) + 8 - self.R0) // self.DL + 1)
            W, n, c = self._adv(l, W, N - done)
            done += n
            cost += c
            if done == N:
                break
            p = self.Q(0, W)                 # the next P reads beyond r(l): do it alone
            if p[0] == "abn":
                return W, done, cost, False
            W = (p[0] + W[p[1]:]).rstrip(b"\0")
            done += 1
            cost += p[2]
        return W, done, cost, True

    def _adv(self, l, W, N):
        """Apply min(N, run length of R(l, W)) P's.  Returns (W', n, cost)."""
        pre, r, n, c = self.R(l, W)
        if n <= N:
            return (pre + W[r:]).rstrip(b"\0"), n, c
        done, cost = 0, 0
        while True:
            if l > 0:
                W, n1, c1 = self._adv(l - 1, W, N - done)
                done += n1
                cost += c1
                if done == N:
                    return W, done, cost
            p = self.Q(0, W)              # inside R(l): reads at most r(l) cells and is normal
            W = (p[0] + W[p[1]:]).rstrip(b"\0")
            done += 1
            cost += p[2]
            if done == N:
                return W, done, cost


def D(k, g=2):
    """The step count of a tick at L = B0 + g*k beyond the sum of the costs of its 2^k P's (checked in `check`):
    g*(2^k - 1), from the Lean count E + C*2^k - g with P's cost E_P + C - g."""
    return g * (2 ** k - 1)


class Hybrid:
    """Cell-by-cell, with the tick `0 0 J(L, W) -> J(L+2, P^(2^k) W)` done at once when all its P's are normal."""

    def __init__(self, m, size=1 << 14):
        self.c = Clock(m)
        self.tp = bytearray(size)
        self.pos = size // 2
        self.lo = self.hi = self.pos
        self.st = 0
        self.t = 0
        self.macros = 0
        self.banded, self.c.nested = MODES.get(m, (False, False))
        self.v = VISIT.get(m, 0)

    def grow(self):
        n = len(self.tp)
        self.tp = bytearray(n) + self.tp + bytearray(n)
        self.pos += n
        self.lo += n
        self.hi += n

    def try_macro(self):
        c, tp, p = self.c, self.tp, self.pos
        if self.st != c.Y or tp[p] != c.h or not c.zeros_left(tp, p):
            return False
        c.banded = self.banded
        res = c.macro_at(tp, p, self.hi)
        if res is None:
            return False
        tp2, self.pos, self.hi, cost = res
        if len(tp2) != len(self.tp):          # extended on the right
            self.tp = tp2
        self.lo = min(self.lo, self.pos)
        if self.hi > len(self.tp) - 4:
            self.grow()
        self.t += cost
        self.macros += 1
        return True

    def step(self):
        tr = self.c.T[(self.st, self.tp[self.pos])]
        if tr is None:
            return False
        w, d, s = tr
        self.tp[self.pos] = w
        self.pos += d
        self.st = s
        self.t += 1
        if self.pos < self.lo:
            self.lo = self.pos
            if self.lo < 4:
                self.grow()
        if self.pos > self.hi:
            self.hi = self.pos
            if self.hi > len(self.tp) - 4:
                self.grow()
        return True

    def tape(self):
        """(L, W) at a visit of the left end: X>0 0^v 1^L 0 W (v = VISIT.get(m, 0))."""
        tp, p = self.tp, self.pos + self.v
        L = 0
        while tp[p + 1 + L] == 1:
            L += 1
        return L, bytes(tp[p + L + 2:self.hi + 1]).rstrip(b"\0")

    def visits(self, limit):
        """Yield (t, L, W) at every visit of the left end in state X on a 0; ('HALT', t) at a halt."""
        X = self.c.X
        while self.t < limit:
            if self.st == X and self.pos == self.lo and not any(self.tp[self.pos:self.pos + 1 + self.v]):
                L, W = self.tape()
                yield self.t, L, W
            if self.pos - 1 > self.lo and self.try_macro():   # (else the next step may be a visit: keep it)
                continue
            if not self.step():
                yield "HALT", self.t, None
                return


def rle(W):
    out, i = [], 0
    while i < len(W):
        j = i
        while j < len(W) and W[j] == W[i]:
            j += 1
        out.append(str(W[i]) if j - i == 1 else f"{W[i]}^{j - i}")
        i = j
    return " ".join(out)


def check(m, steps):
    """Compare the visits of the hybrid run with a plain cell-by-cell run (the same class without macros)."""
    h = Hybrid(m)
    p = Hybrid(m)
    p.try_macro = lambda: False
    n = 0
    for a, b in zip(h.visits(steps), p.visits(steps)):
        assert a == b, (a[:2], b[:2])
        n += 1
    return n, h.macros


def tmcheck(m, steps, tmrun="/tmp/claude-0/bin/tmrun"):
    """Compare every visit of the left end in state X (time, block, word) with tools/c/tmrun.c `at X L`."""
    import re
    import subprocess
    X = PARAMS[m][0]
    nv = VISIT.get(m, 0)
    mm = mirror(m) if m in MIRROR else m
    proc = subprocess.Popen([tmrun, mm, str(steps), "at", X, "L", "100000000"], stdout=subprocess.PIPE, text=True)

    def plain():
        for line in proc.stdout:
            if not line[0].isdigit():
                continue
            t, tape = line.split(None, 1)
            if not tape.startswith(X + ">0"):
                continue
            cells = []
            for x in re.sub(r"[A-F]>", "", tape).split():
                v, _, n = x.partition("^")
                cells += [int(v)] * int(n or 1)
            if any(cells[1:1 + nv]):
                continue
            cells = cells[nv:]
            L = 1
            while L < len(cells) and cells[L] == 1:
                L += 1
            yield int(t), L - 1, bytes(cells[L + 1:]).rstrip(b"\0")
    h = Hybrid(m)
    n = 0
    for a, b in zip(h.visits(steps), plain()):
        assert a == b, (n, a[:2], b[:2])
        n += 1
    return n, h.macros, h.c.pcalls


def sci(t):
    s = str(t)
    return s if len(s) < 8 else f"{s[0]}.{s[1:5]}e{len(s) - 1}"


def run(m, log10, out=sys.stdout):
    h = Hybrid(m)
    lastL = None
    start = None
    for t, L, W in h.visits(10 ** int(log10)):
        if t == "HALT":
            print("HALT", L, file=out)
            return
        if lastL is not None and L != lastL + h.c.g:
            print(f"phase start {sci(start[0])} L={start[1]} end {sci(prev[0])} L={prev[1]} |W|={len(prev[2])}"
                  f" P-calls={h.c.pcalls}", file=out, flush=True)
            start = (t, L)
        if start is None:
            start = (t, L)
        prev = (t, L, W)
        lastL = L


if __name__ == "__main__":
    m, cmd = sys.argv[1], sys.argv[2]
    if cmd == "tmcheck":
        print(tmcheck(m, int(float(sys.argv[3]))))
    elif cmd == "check":
        print(check(m, int(float(sys.argv[3]))))
    else:
        run(m, float(sys.argv[3]))
