"""Rule B: classes v = R + k that start k rounds after a virtual clean tape n* (round R of the limit process).

After round R the class is in the state  G 1,  M 2^(k+1) m,  M 2N + 2n* + 3,  w = 2N + 2n* + 5,  with N = 2^v m.
Positions are written  alpha*N + a*m + beta*n* + c  with the order N >> m >> n* >> 1:
  - N = 2^v m is divisible by a high power of 2 (R large), so alpha*N drops out of every mod-4 test;
    we record the largest denominator of alpha seen, which says how large R must be;
  - m is odd and otherwise free: a test whose m-coefficient is odd or fractional depends on m (class not fixed);
  - n* = 2^E j + rho with j free: a test that needs more digits of n* splits the class (E -> E+1).
Same mark rules as tracecycle / symjump."""
import sys
from fractions import Fraction as Fr

class DepM(Exception): pass
class NeedBit(Exception): pass

class P:
    __slots__ = ("v",)
    def __init__(self, al=0, a=0, be=0, c=0): self.v = (Fr(al), Fr(a), Fr(be), Fr(c))
    @staticmethod
    def of(t): p = P(); p.v = t; return p
    def __add__(s, o):
        if not isinstance(o, P): o = P(0, 0, 0, o)
        return P.of(tuple(x + y for x, y in zip(s.v, o.v)))
    def __sub__(s, o):
        if not isinstance(o, P): o = P(0, 0, 0, o)
        return P.of(tuple(x - y for x, y in zip(s.v, o.v)))
    def half(s): return P.of(tuple(x / 2 for x in s.v))
    def key(s): return s.v
    def __lt__(s, o): return s.v < o.v
    def __gt__(s, o): return s.v > o.v
    def __eq__(s, o): return isinstance(o, P) and s.v == o.v
    def __hash__(s): return hash(s.v)
    def __repr__(s):
        al, a, be, c = s.v; out = []
        if al: out.append(f"{al}N")
        if a: out.append(f"{a}m")
        if be: out.append(f"{be}n*")
        if c or not out: out.append(f"{c}")
        return "+".join(out)

def v2(x):
    x = Fr(x); n, d = x.numerator, x.denominator
    if n == 0: return 99
    k = 0
    while n % 2 == 0: n //= 2; k += 1
    while d % 2 == 0: d //= 2; k -= 1
    return k

class Ctx:
    def __init__(s, E, rho): s.E, s.rho, s.alpha_den = E, rho, 0
    def mod4(s, d):
        al, a, be, c = d.v
        if al: s.alpha_den = max(s.alpha_den, -v2(al))
        if a.denominator != 1 or int(a) % 2: raise DepM()
        # beta*n* = beta*(2^E j + rho): the j part must vanish mod 4 for every j
        if be and v2(be) + s.E < 2: raise NeedBit()
        rest = be * s.rho + c
        if rest.denominator != 1: raise NeedBit()
        return (int(rest) + (2 if int(a) % 4 == 2 else 0)) % 4

def round_events(ctx, w, marks):
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
            if ctx.mod4(d) == 0:
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
    if marks and marks[0][0] == "M" and marks[0][1] == P(0, 0, 0, 0):
        marks[0] = ["W", P(0, 0, 0, 1)]; extra = 4
    return w + extra, [["G", P(0, 0, 0, 1)]] + [[t, p + extra] for t, p in marks]

def run(k, E, rho, max_rounds=400):
    """Outcome for offset k and n* = rho (mod 2^E): ('fixed', jump, rounds_after_R, alpha_den) / ('depm', round) / ('bit', round)."""
    ctx = Ctx(E, rho)
    w = P(2, 0, 2, 5); marks = [["G", P(0, 0, 0, 1)], ["M", P(0, 2 ** (k + 1))], ["M", P(2, 0, 2, 3)]]
    for r in range(1, max_rounds):
        try:
            w, marks = round_events(ctx, w, marks)
        except DepM: return ("depm", r)
        except NeedBit: return ("bit", r)
        if len(marks) == 2 and marks[1][0] == "M" and marks[1][1] == w - 2:
            al, a, be, c = (w - P(2, 0, 0, 2)).v                   # w0 = 2N + 2 (clean tape n = N - 2)
            assert al == 0 and a == 0
            return ("fixed", (be / 2, (c) / 2), r, ctx.alpha_den)
    return ("long", max_rounds)

def explore(k, Emax):
    """All residue classes of n* (mod 2^E, E <= Emax) for offset k, split only where a test needs another digit."""
    out = []; stack = [(0, 0)]
    while stack:
        E, rho = stack.pop()
        res = run(k, E, rho)
        if res[0] == "bit" and E < Emax: stack += [(E + 1, rho), (E + 1, rho + 2 ** E)]
        else: out.append((E, rho, res))
    return sorted(out, key=lambda x: (x[0], x[1]))

def fmt_jump(j):
    be, c = j
    s = (f"{be}·n*" if be != 1 else "n*") if be else ""
    return (s + (f" + {c}" if c >= 0 else f" − {-c}")) if s else f"{c}"

if __name__ == "__main__":
    K, Emax = int(sys.argv[1]), int(sys.argv[2])
    for k in range(0, K + 1):
        leaves = explore(k, Emax)
        fixed = [(E, rho, r) for E, rho, r in leaves if r[0] == "fixed"]
        open_ = sum(1 for E, rho, r in leaves if r[0] == "bit")
        desc = "; ".join(f"n*≡{rho} mod {2**E}: {fmt_jump(r[1])} ({r[2]} rds, α-den 2^{r[3]})" for E, rho, r in fixed)
        print(f"k={k:2d}: {len(fixed)} fixed residue classes{', ' + str(open_) + ' still need more digits' if open_ else ''}"
              + (f"  [{desc}]" if desc else ""))
