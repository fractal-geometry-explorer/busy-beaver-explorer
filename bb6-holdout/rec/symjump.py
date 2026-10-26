"""Symbolic mark model: positions are a*m + b with m a large odd number (n + 2 = 2^v * m).
A swap/merge test on d = a*m + b is decided when a is an integer with a ≡ 0 or 2 (mod 4) (m is odd);
otherwise it depends on m and we stop. If a cycle finishes, the jump to the next clean tape is the same for
every large odd m. Same rules as tracecycle.round_events / clean_recurrence."""
import sys
from fractions import Fraction as Fr

class Dep(Exception): pass

class P:
    __slots__ = ("a", "b")
    def __init__(self, a, b=0): self.a = Fr(a); self.b = Fr(b)
    def __add__(s, o): o = o if isinstance(o, P) else P(0, o); return P(s.a + o.a, s.b + o.b)
    def __sub__(s, o): o = o if isinstance(o, P) else P(0, o); return P(s.a - o.a, s.b - o.b)
    def half(s): return P(s.a / 2, s.b / 2)
    def key(s): return (s.a, s.b)                       # order for large m
    def __lt__(s, o): return s.key() < o.key()
    def __gt__(s, o): return s.key() > o.key()
    def __eq__(s, o): return isinstance(o, P) and s.key() == o.key()
    def __hash__(s): return hash(s.key())
    def __repr__(s): return f"{s.a}m+{s.b}"

def mod4(d):
    if d.a.denominator != 1 or d.b.denominator != 1: raise Dep("fractional")
    a, b = int(d.a), int(d.b)
    if a % 2: raise Dep("odd coefficient")
    return (b + (2 if a % 4 == 2 else 0)) % 4

def round_events(w, marks):
    marks = sorted(([t, p] for t, p in marks), key=lambda m: m[1].key())
    gap = marks[0]
    def first_right(x):
        r = [m for m in marks if m[1] > x]
        return min(r, key=lambda m: m[1].key()) if r else None
    def shift_from(x):
        nonlocal w
        k = first_right(x)
        if k is None:
            w = w + 2; marks.append(["M", w - 2]); return packet_back(w - 2)
        if k[0] == "M": k[0] = "G"; return k
        if k[0] == "W": k[0] = "B"; return packet_back(k[1])
        if k[0] == "B": k[0] = "W"; k[1] = k[1] + 2; return packet_back(k[1])
        raise RuntimeError("shift into " + k[0])
    def packet_back(x):
        left = [m for m in marks if m[1] < x and m[0] != "M"]
        if not left: return None
        m = max(left, key=lambda m: m[1].key())
        if m[0] == "B": raise RuntimeError("halt")
        if m[0] == "G": m[1] = m[1] + 2; return m
        q = m[1]; m[0], m[1] = "M", q - 1
        g = ["G", q + 1]; marks.append(g); return g
    while gap is not None:
        g = gap[1]; m = first_right(g)
        if m is None:
            marks.remove(gap); w = w + 3; marks.append(["M", w - 2]); gap = packet_back(w - 2)
        elif m[0] == "M":
            d = m[1] - g - 3
            if mod4(d) == 0:
                m[1] = g + d.half() - 1; gap[1] = g + d.half() + 1
            else:
                marks.remove(gap); m[0], m[1] = "W", g + d.half() + 3; gap = packet_back(m[1])
        elif m[0] == "W":
            x = m[1]; marks.remove(gap); marks.remove(m); gap = shift_from(x)
        elif m[0] == "B":
            m[0], m[1] = "W", m[1] - 1; gap = shift_from(m[1])
        else:
            raise RuntimeError("gap meets " + m[0])
        marks.sort(key=lambda k: k[1].key())
    extra = 2
    if marks and marks[0][0] == "M" and marks[0][1] == P(0, 0):
        marks[0] = ["W", P(0, 1)]; extra = 4
    return w + extra, [["G", P(0, 1)]] + [[t, p + extra] for t, p in marks]

def jump(v, max_rounds=10000):
    w0 = P(2 ** (v + 1), 2)                              # w = 2n + 6 with n = 2^v m - 2
    w = w0; marks = [["G", P(0, 1)], ["M", w0 - 2]]
    for r in range(1, max_rounds):
        try:
            w, marks = round_events(w, marks)
        except Dep as e:
            return None, r
        if len(marks) == 2 and marks[1][0] == "M" and marks[1][1] == w - 2:
            dw = w - w0
            assert dw.a == 0
            return int(dw.b) // 2, r
    return "long", max_rounds

if __name__ == "__main__":
    V = int(sys.argv[1])
    fixed = []
    for v in range(1, V + 1):
        j, r = jump(v)
        if j is not None: fixed.append((v, j, r))
    print("v with a fixed jump (v: jump, rounds):")
    print("  " + ", ".join(f"{v}: +{j} ({r})" for v, j, r in fixed))
