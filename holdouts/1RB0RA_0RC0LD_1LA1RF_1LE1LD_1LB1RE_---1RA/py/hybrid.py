"""Exact accelerated simulator of 1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA.

Plain cell-by-cell simulation, except that whenever the head is in state B on a 0 followed by `1^(2n+1) 0 1^c`
(written K(n, c)) and one of the two recursive rules applies, the whole call is done at once:

  M_n:      0 0 K(n, c)          ->  K(n+1, c), head 2 cells further left        (needs c >= n)
  G(r, k):  0 0 (011)^r K(k, c)  ->  K(r+k+1, c+r), head 3r+2 cells further left  (needs c >= k)

with step counts TM(n), TG(r, k) from the recursions below (built from the Lean-proved rules P, M1, X, Y, Z).
The sibling 1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA (D and E swapped, C0 differs) has the same rules with the same
step counts, and uses this file with `machine=`.  Run `python3 hybrid.py STEPS [MACHINE]` to print the configuration at every visit of the left end in state B.
"""
import sys

M = "1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA"


def table(m):
    T = {}
    for s, g in enumerate(m.split("_")):
        for y in (0, 1):
            x = g[3 * y:3 * y + 3]
            T[(s, y)] = None if x == "---" else (int(x[0]), 1 if x[1] == "R" else -1, "ABCDEF".index(x[2]))
    return T


def TP(i):            # B>0 1^(2i+5) 0 1^(c+1) -> 0 1 1 0^(2i) B>0 1^3 0 1^c
    return 2 * i + 11


def TX(r):            # 0 0 (011)^r B>0 1^3 0 1^(c+1) -> B>0 1^(2r+5) 0 1^(c+r+1)
    return 2 * r * r + 11 * r + 18


_H = [0, 0]           # _H[k] = sum over k' = 2..k of TP(k'-2) + SM(k'-2)
_SM = [0]             # _SM[n] = TM(1) + ... + TM(n)


def _extend(n):
    while len(_SM) <= n:
        m = len(_SM)          # compute TM(m), using H(m) and TX(m-1)
        while len(_H) <= m:
            k = len(_H)
            _H.append(_H[-1] + TP(k - 2) + _SM[k - 2])
        tm = 18 if m == 1 else _H[m] + TX(m - 1)
        _SM.append(_SM[-1] + tm)


def TM(n):
    """0 0 K(n,c) -> K(n+1,c): TP(n-2) + TM(1..n-2) + TG(1, n-1), unrolled."""
    _extend(n)
    return _SM[n] - _SM[n - 1]


def TG(r, k):
    """0 0 (011)^r K(k,c) -> K(r+k+1, c+r): TP(k-2) + TM(1..k-2) + TG(r+1, k-1), unrolled down to TX(r+k-1)."""
    _extend(k)
    return _H[k] + TX(r + k - 1)


def _TM_rec(n):
    return 18 if n == 1 else TP(n - 2) + sum(_TM_rec(j) for j in range(1, n - 1)) + _TG_rec(1, n - 1)


def _TG_rec(r, k):
    return TX(r) if k == 1 else TP(k - 2) + sum(_TM_rec(j) for j in range(1, k - 1)) + _TG_rec(r + 1, k - 1)


class Sim:
    def __init__(self, size=1 << 16, machine=M):
        self.T = table(machine)
        self.tape = bytearray(size)
        self.pos = size // 2
        self.lo = self.hi = self.pos
        self.state = 0
        self.t = 0
        self.macros = 0

    def run_len(self, p, sym):
        n = 0
        while self.tape[p + n] == sym:
            n += 1
        return n

    def try_macro(self):
        tp, p = self.tape, self.pos
        if self.state != 1 or tp[p] != 0:
            return False
        n2 = self.run_len(p + 1, 1)
        if n2 % 2 == 0 or n2 < 3 or tp[p + n2 + 1] != 0:
            return False
        n = n2 // 2
        c = self.run_len(p + n2 + 2, 1)
        if p + n2 + 2 + c > self.hi:     # the c block must end inside the visited tape (a 0 after it)
            return False
        # left context
        if tp[p - 1] != 0 or tp[p - 2] != 0:
            # G: (011)^r directly left of K, then 0 0
            r, q = 0, p
            while tp[q - 1] == 1 and tp[q - 2] == 1 and tp[q - 3] == 0:
                r += 1
                q -= 3
            if r == 0 or tp[q - 1] != 0 or tp[q - 2] != 0 or c < n:
                return False
            k = n
            new = [0] + [1] * (2 * (r + k + 1) + 1) + [0] + [1] * (c + r)
            start = q - 2
            dt = TG(r, k)
        else:
            if c < n:
                return False
            new = [0] + [1] * (2 * n + 3) + [0] + [1] * c
            start = p - 2
            dt = TM(n)
        end = p + n2 + 2 + c          # exclusive: the cells start..end-1 are rewritten
        assert len(new) == end - start, (len(new), end - start)
        tp[start:end] = bytes(new)
        self.pos = start
        self.lo = min(self.lo, start)
        self.t += dt
        self.macros += 1
        return True

    def step(self):
        tr = self.T[(self.state, self.tape[self.pos])]
        if tr is None:
            return False
        w, d, s = tr
        self.tape[self.pos] = w
        self.pos += d
        self.state = s
        self.t += 1
        if self.pos < self.lo:
            self.lo = self.pos
        if self.pos > self.hi:
            self.hi = self.pos
        return True

    def rle(self, a=None, b=None):
        a = self.lo if a is None else a
        b = self.hi if b is None else b
        out, i = [], a
        while i <= b:
            if i == self.pos:
                out.append("ABCDEF"[self.state] + ">" + str(self.tape[i]))
                i += 1
                continue
            v, j = self.tape[i], i
            while j <= b and j != self.pos and self.tape[j] == v:
                j += 1
            out.append(str(v) if j - i == 1 else f"{v}^{j - i}")
            i = j
        return " ".join(out)


def events(limit, macro=True, machine=M):
    """Yield (t, rle) each time the head is in B on the leftmost visited cell (one step after E extended the tape)."""
    s = Sim(machine=machine)
    while s.t < limit:
        if s.state == 1 and s.pos == s.lo and s.tape[s.pos] == 0:
            yield s.t, s.rle()
        if macro and s.try_macro():
            continue
        if not s.step():
            yield s.t + 1, "HALT " + s.rle()
            return


if __name__ == "__main__":
    lim = int(float(sys.argv[1]))
    for t, x in events(lim, machine=sys.argv[2] if len(sys.argv) > 2 else M):
        print(t, x)
