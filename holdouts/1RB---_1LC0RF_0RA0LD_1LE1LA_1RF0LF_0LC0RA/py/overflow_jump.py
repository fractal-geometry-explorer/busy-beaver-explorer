"""Follow 1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA from overflow to overflow of R.

Between two overflows every event follows the layer law of lean/Layers.lean, so m events are done at once, in closed
form: N + m (with its wraps), Z + m, and the units sent down the chain added with carries (a unit adds 3 to Q, each
wrap of Q adds 3 to P, each wrap of P sends a unit on; the final words do not depend on the order).  The largest m
with no carry out of R is found by bisection.  The event after it, the overflow, is run cell by cell by
c/overflow_event.c up to the next full event in the layered layout (parsed as in py/layers_check.py); a halt there
would be printed.  Start: the first event of the layout Z2 | (Q12, R0) of the run, step 118,003 (N = 35, Z = 2).

usage (from the repository root):
  gcc -O2 -o overflow_event holdouts/1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA/c/overflow_event.c
  python3 holdouts/1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA/py/overflow_jump.py COUNT [./overflow_event]"""
import sys, os, math, subprocess, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from layers_check import parse_left, parse_right

D3 = {0: '100', 1: '110', 2: '010'}
ZD = {False: '0010', True: '1010'}; QD = {False: '0001', True: '0101'}; PD = {False: '1000', True: '1010'}
def val(w): return sum(1 << i for i, b in enumerate(w) if b)
def bits(v, k): return [bool((v >> i) & 1) for i in range(k)]
def bstr(w): return ''.join('1' if x else '0' for x in w)

def cells(n, nw, z, items):
    """The tape of an event: left part (0^inf omitted) and right part from the event cell."""
    ds = [(n // 3 ** i) % 3 for i in range(nw)]
    left = '10' + ''.join(D3[d] for d in reversed(ds))
    r = '0' + ''.join(ZD[b] for b in z)
    for i, (q, p) in enumerate(items):
        r += '11' + ''.join(QD[b] for b in q) + '01' + ''.join(PD[b] for b in p)
        if i + 1 < len(items): r += '10'
    return left, r

def advance(z, items, m):
    """m events of the layer law at once: (Z', items', units carried out of R)."""
    kz = len(z); s = val(z) + m; u = s >> kz; z2 = bits(s, kz); out = []
    for q, p in items:
        sq = val(q) + 3 * u; cq = sq >> len(q); sp = val(p) + 3 * cq; u = sp >> len(p)
        out.append((bits(sq, len(q)), bits(sp, len(p))))
    return z2, out, u

def to_overflow(z, items):
    """The largest m such that m events carry nothing out of R (the next event is an overflow)."""
    lo, hi = 0, 1
    while advance(z, items, hi)[2] == 0: hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if advance(z, items, mid)[2] == 0: lo = mid
        else: hi = mid
    return lo

def addN(n, nw, m):
    """N + m: N = 2...2 wraps to 0...0 with one digit more."""
    while n + m >= 3 ** nw:
        m -= 3 ** nw - n; n = 0; nw += 1
    return n + m, nw

def overflow_event(exe, n, nw, z, items, maxsteps=10 ** 9):
    l, r = cells(n, nw, z, items)
    pr = subprocess.Popen([exe, str(maxsteps)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    pr.stdin.write(l + ' ' + r + '\n'); pr.stdin.close()
    skipped = 0
    for line in pr.stdout:
        f = line.split()
        if f[0] != 'EV':
            pr.kill(); return (f[0], f)
        k, p, L, R = int(f[1]), int(f[2]), f[3], f[4]
        left = parse_left(L); e = parse_right(R[1:])
        if left and e:
            pr.kill(); return ('OK', k, p, left, e, skipped)
        skipped += 1
    return ('END', None)

def shape(z, items):
    return 'Z%d |' % len(z) + ''.join(' (%d, %d)' % (len(q), len(p)) for q, p in items)

if __name__ == '__main__':
    count = int(sys.argv[1]); exe = sys.argv[2] if len(sys.argv) > 2 else './overflow_event'
    n, nw, z, items = 35, 5, [False, True], [([False] * 12, [])]
    events = 0; dcount = collections.Counter()
    print('overflow, log10 of the events before it, N\'s lowest base-3 digits (lowest first), d = digits of N taken,'
          ' layout before -> after, steps of the overflow event')
    for it in range(count):
        m = to_overflow(z, items); z, items, _ = advance(z, items, m); n, nw = addN(n, nw, m); events += m
        res = overflow_event(exe, n, nw, z, items)
        if res[0] != 'OK':
            print('overflow %d: %s %s' % (it, res[0], ' '.join(res[1] or []))); break
        _, k, p, (n2, nw2), (z2, its2, l2), sk = res
        d = -p // 3; dcount[d] += 1
        assert p % 3 == 0 and p <= 0 and n2 == n // 3 ** d + 1, 'N rule'
        low = ''.join(str((n // 3 ** i) % 3) for i in range(6))
        print('%d  %.1f  %s  d=%d  %s -> %s  %d' % (it, math.log10(events + 1), low, d, shape(z, items), shape(z2, its2 + [l2]), k), flush=True)
        events += 1 + sk
        n, nw, z, items = n2, nw2, z2, its2 + [l2]
    print('overflows by d:', ', '.join('%d: %d' % x for x in sorted(dcount.items())))
    print('events: about 10^%.1f; no halt' % math.log10(events))
