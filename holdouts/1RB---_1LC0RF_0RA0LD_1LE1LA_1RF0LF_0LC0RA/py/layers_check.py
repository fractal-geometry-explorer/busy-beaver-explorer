"""Check a run against the layer law of lean/Layers.lean, with the same functions on digit lists.

Reads the events printed by cascade_events.c of 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB--- and keeps the full ones
(the tape left of the head exactly 0^inf 1 0 [N]).  Each is parsed in the layered layout

    0^inf 1 0 [N] A> 0 [Z] (11 [Q] 01 [P] 10)* 11 [Q] 01 [R] 0^inf

and for every two consecutive full events the second is compared with what `evNext` (and N + 1) gives for the
first.  Pairs where a carry leaves R (`evNext` = none, the overflows of R) are listed separately.

usage (from the repository root):
  gcc -O2 -o cascade_events holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---/c/cascade_events.c
  ./cascade_events 1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA 0 300000000 0 | python3 holdouts/1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA/py/layers_check.py"""
import sys, re, collections

# ---- the functions of Layers.lean (digit lists, lowest digit first; True = 1)
def incB(w):
    if not w: return [], True
    if not w[0]: return [True] + w[1:], False
    r, c = incB(w[1:]); return [False] + r, c
def pInc(k, p, s):
    p2, c = incB(p)
    if not c: return p2, s
    s2 = k(s); return None if s2 is None else (p2, s2)
def pUnit(k, p, s):
    x = pInc(k, p, s)
    if x is None: return None
    y = pInc(k, *x)
    return None if y is None else pInc(k, *y)
def qInc(k, q, p, s):
    q2, c = incB(q)
    if not c: return q2, p, s
    x = pUnit(k, p, s); return None if x is None else (q2, x[0], x[1])
def qUnit(k, q, p, s):
    x = qInc(k, q, p, s)
    if x is None: return None
    y = qInc(k, *x)
    return None if y is None else qInc(k, *y)
def dU(n, its, l):
    if n == 0: return None
    if not its:
        x = qUnit(lambda s: None, l[0], l[1], ())
        return None if x is None else ([], (x[0], x[1]))
    (q, p), rest = its[0], its[1:]
    x = qUnit(lambda s: dU(n - 1, s[0], s[1]), q, p, (rest, l))
    return None if x is None else ([(x[0], x[1])] + x[2][0], x[2][1])
def evNext(z, its, l):
    z2, c = incB(z)
    if not c: return z2, its, l
    r = dU(len(its) + 1, its, l)
    return None if r is None else (z2, r[0], r[1])

# ---- parsing the run's events (cells right of the event cell)
D3 = {'100': 0, '110': 1, '010': 2}
ZP = re.compile(r'(?:0010|1010)*'); QP = re.compile(r'(?:0001|0101)*'); PP = re.compile(r'(?:1000|1010)*')
def digits(s, one): return [s[i:i + 4] == one for i in range(0, len(s), 4)]
def parse_right(R):
    R = R.rstrip('0'); i = 0
    m = ZP.match(R, i); z = digits(m.group(0), '1010'); i = m.end()
    items = []
    while True:
        if R[i:i + 2] != '11': return None
        m = QP.match(R, i + 2); q = digits(m.group(0), '0101'); i = m.end()
        if R[i:i + 2] != '01': return None
        m = PP.match(R, i + 2); pw = m.group(0); i = m.end()
        rest = R[i:]
        if rest in ('', '1', '101'):  # R, the last word: its top digit may have lost trailing zeros to the strip
            pw += (rest + '000')[:4] if rest else ''; items.append((q, digits(pw, '1010'))); break
        if R[i:i + 2] != '10': return None
        items.append((q, digits(pw, '1010'))); i += 2
    if not z: return None
    return z, items[:-1], items[-1]
def parse_left(L):
    l = L.lstrip('0')
    if not l.startswith('10') or (len(l) - 2) % 3: return None
    ds = [D3.get(l[j:j + 3]) for j in range(2, len(l), 3)]
    if None in ds: return None
    n = 0
    for d in ds: n = 3 * n + d
    return n, len(ds)
def val(w): return sum(1 << i for i, b in enumerate(w) if b)
def shape(e):
    z, its, l = e
    return ' '.join(['Z%d' % len(z)] + ['Q%d P%d' % (len(q), len(p)) for q, p in its] + ['Q%d R%d' % (len(l[0]), len(l[1]))])
def show(n, e):
    z, its, l = e
    return 'N %d, Z %d, ' % (n, val(z)) + ', '.join('(%d, %d)' % (val(q), val(p)) for q, p in its + [l])

if __name__ == '__main__':
    st = collections.Counter(); prev = None; shapes = {}; over = []
    for line in sys.stdin:
        f = line.split()
        if len(f) < 5: continue
        left = parse_left(f[2])
        if left is None: st['inner turn (skipped)'] += 1; continue
        k = int(f[0]); e = parse_right(f[4])
        if e is None: st['full event of another layout'] += 1; prev = None; continue
        sh = shape(e); w = shapes.setdefault(sh, [k, k, 0]); w[1] = k; w[2] += 1
        if prev is not None:
            pk, (pn, pnw), pe = prev
            q = evNext(*pe)
            nn, nnw = pn + 1, pnw
            if nn == 3 ** pnw: nn, nnw = 0, pnw + 1
            if q is None:
                st['a carry leaves R (overflow, not covered)'] += 1; over.append((pk, pn, pe, k, left[0], e))
            elif (q[0], q[1], q[2]) == e and (nn, nnw) == left: st['follows the law'] += 1
            else:
                st['MISMATCH'] += 1
                if st['MISMATCH'] <= 5: print('mismatch at step', k, file=sys.stderr)
        prev = (k, left, e)
    for a, b in sorted(st.items()): print('%s: %d' % (a, b))
    print('layouts (widths of Z, then Q and P of each item, R last): first and last step, full events')
    for sh, (a, b, c) in sorted(shapes.items(), key=lambda x: x[1][0]):
        if c >= 20: print('  %s: steps %d to %d, %d' % (sh, a, b, c))
    print('consecutive full events where a carry leaves R (values: N, Z, then (Q, P) of each item, (Q, R) last):')
    for pk, pn, pe, k, n, e in over:
        print('  step %d: %s [%s]\n    -> step %d: %s [%s]' % (pk, show(pn, pe), shape(pe), k, show(n, e), shape(e)))
