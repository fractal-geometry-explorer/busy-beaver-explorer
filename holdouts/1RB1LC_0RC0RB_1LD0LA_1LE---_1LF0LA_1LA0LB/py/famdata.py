"""Concrete runs of one step of the walk, cut at its boundaries (pass ends and phase ends), each boundary parsed into
the counter encoding: the cells between the untouched rest X of the up-counter and the head, the header, and the
bits of the down-counter.  The generator `gen_fam.py` fits these over the run length and proves the step in Lean."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rebuild import Rebuilder

M = "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB"
rb = Rebuilder(M)
HD = ("0110101", "0110111")
SUFS = {'', '0', '1', '000', '001', '0000', '0001', '1000', '1001', '10', '11'}
X0 = [True, False, True, True, False, True, False, False, True, True, True]   # rest of the counter (low first)


def words(bits_low_first):
    return "".join("00001" if b else "00000" for b in reversed(bits_low_first))


def build(X, suf, H, V, nv):
    left = "1" + words(X) + suf
    right = H + "".join("01" if (V >> i) & 1 else "11" for i in range(nv)) + "1"
    return rb.setup(left + "00" + right, len(left) + 2)


def cells(c, a, b):
    return "".join(str(c.get(i)) for i in range(a, b))


def snap(c, xend):
    """(cells from xend to the head, header, V bits low first, what is right of V) at a D-visit on a header"""
    p = c.pos
    lit = cells(c, xend, p)
    H = cells(c, p, p + 7)
    hi = c.hi
    while c.get(hi) == 0:
        hi -= 1
    R = cells(c, p + 7, hi + 1)
    bits = []
    i = 0
    while i + 1 < len(R) and R[i:i + 2] in ("01", "11"):
        bits.append(R[i:i + 2] == "01")
        i += 2
    return dict(lit=lit, H=H, v=bits, tail=R[i:], pos=p)


def is_clean(c, X, q):
    """clean visit with the rest X[q:] untouched (suffix in SUFS)"""
    if c.state != 3:
        return None
    p = c.pos
    H = cells(c, p, p + 7)
    if H not in HD or c.get(p - 1) or c.get(p - 2):
        return None
    return H


def parse_lit(body):
    """(suffix, digits top to bottom) for cells that are digit words above a suffix in SUFS (longest suffix first)"""
    for sf in sorted(SUFS, key=len, reverse=True):
        if body.endswith(sf) and (len(body) - len(sf)) % 5 == 0:
            ws = [body[k:k + 5] for k in range(0, len(body) - len(sf), 5)]
            if all(w in ("00000", "00001") for w in ws):
                return sf, "".join('1' if w == "00001" else '0' for w in ws)
    return None


def run(digs, suf, H, V, nv, maxpass=10 ** 7, cut=False, xpre=()):
    """digs: digits read, top to bottom (a string).  Returns dict(events=[...], bounds=[...]) or a failure string.
    bounds[i] is the boundary before event i (and the last one the end); events are ('pass', steps, lo, hi) and
    ('phase', w, u, ticks)."""
    X = [d == '1' for d in reversed(digs)] + list(xpre) + X0
    c = build(X, suf, H, V, nv)
    xend = 1 + 5 * len(X0) + c.pos - (1 + 5 * len(X) + len(suf) + 2)   # absolute cell after the rest X0's words
    xend = c.pos - 2 - len(suf) - 5 * len(digs)
    x0s = xend - 5 * len(xpre)
    x0w = cells(c, x0s - 5 * len(X0), x0s)
    tab = c.tab
    bounds = [snap(c, xend)]
    events = []
    def special():
        """at a D-visit on a header: do a carry or a phase if the configuration is one; True if done"""
        mt = c.match()
        if not (mt and mt[0] == 'tick'):
            return False
        _, lc, key, VV, nb = mt
        w, u = lc[0], lc[1]
        if u == (1 << w) - 1 and VV >= 1 and c.get(c.pos - 2 - 5 * w - 1) == 0:
            i = 0
            while not (VV >> i) & 1:
                i += 1
            n = 10 * w + 34 if i == 0 else 8 * (i - 1) + 10 * w + 42
            for _ in range(n):
                c.step_to_S(1) if False else None
                j = c.pos + c.off
                if j < 1 or j >= len(c.c) - 1:
                    c.grow(); j = c.pos + c.off
                tr = tab[2 * c.state + c.c[j]]
                c.c[j] = tr[0]; c.pos += tr[1]; c.state = tr[2]; c.steps += 1
                c.lo = min(c.lo, c.pos); c.hi = max(c.hi, c.pos)
            events.append(('carry', w, i))
            bounds.append(snap(c, xend))
            return True
        k = min((1 << w) - 1 - u, VV)
        if k > 0:
            j = c.jump(lc, key, VV, nb)
            events.append(('phase', w, u, j))
            bounds.append(snap(c, xend))
            return True
        return False
    while special():
        pass
    while True:
        lo = hi = c.pos
        n = 0
        while True:
            i = c.pos + c.off
            if i < 1 or i >= len(c.c) - 1:
                c.grow(); i = c.pos + c.off
            tr = tab[2 * c.state + c.c[i]]
            if tr is None:
                return "HALT"
            c.c[i] = tr[0]; c.pos += tr[1]; c.state = tr[2]; c.steps += 1; n += 1
            c.lo = min(c.lo, c.pos); c.hi = max(c.hi, c.pos)
            lo = min(lo, c.pos); hi = max(hi, c.pos)
            if n > maxpass:
                return "LONG"
            if c.state != 3:
                continue
            Hh = cells(c, c.pos, c.pos + 7)
            if Hh in HD and not c.get(c.pos - 1) and not c.get(c.pos - 2):
                s = snap(c, xend)
                # clean end: the cells between X0 and the gap are a suffix in SUFS and V is clean
                s0 = snap(c, x0s)
                if cut and s['tail'] == "1" and s0['lit'][-2:] == "00" and cells(c, x0s - 5 * len(X0), x0s) == x0w:
                    pl = parse_lit(s0['lit'][:-2])
                    if pl and pl[0]:
                        events.append(('pass', n, lo, hi))
                        bounds.append(s0)
                        return dict(events=events, bounds=bounds, xend=xend, cut=pl)
                if s['lit'][:-2] in SUFS and s['tail'] == "1" and lo >= xend:
                    events.append(('pass', n, lo, hi))
                    bounds.append(s)
                    return dict(events=events, bounds=bounds, xend=xend)
            pos0, st0 = c.pos, c.steps
            snap0 = snap(c, xend)
            if special():
                events.insert(len(events) - 1, ('pass', n, lo, hi))
                bounds.insert(len(bounds) - 1, snap0)
                while special():
                    pass
                break


if __name__ == "__main__":
    import random
    suf = sys.argv[1]; H = HD[int(sys.argv[2])]; digs = sys.argv[3]
    V = random.getrandbits(60) | (1 << 60); nv = 64
    r = run(digs, suf, H, V, nv)
    if isinstance(r, str):
        print(r); sys.exit()
    for i, b in enumerate(r['bounds']):
        print(i, b['lit'], b['H'], "".join('1' if x else '0' for x in b['v'][:12]), len(b['v']), b['tail'][:5])
        if i < len(r['events']):
            print("   ", r['events'][i])
