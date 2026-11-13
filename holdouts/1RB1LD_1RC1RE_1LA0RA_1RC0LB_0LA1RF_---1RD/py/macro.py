"""The macro map of 1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD (and of its twin 1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC).

State (n, word) at a tick boundary ("P1"):

    0^inf 1110 (111110)^n 1 A> [word] 0^inf,  n even,  the word read in cell pairs: 1b -> bit b.

Every cell pair right of the head starts with 1, so the right side is a bit string.  v = 101110 is the bits 010,
and the separators r = 10, q = 1110, p = 101011, s = 11 are the bits 0, 10, 001, 1.  The word is kept as tokens
xs (blocks: copies of 010), ss (separators), tail, cut greedily from the head.

A tick is a borrow into separator 0.  At separator i (block a before it, block b after it):

    s starts with 00          drop the 00                     (p -> s)
    s = 0, b >= 1             s -> 10, b - 1                  (r -> q)
    s = 10.. , a >= 1(*)      s -> 001 + s[2:], a - 1         (q -> p; s = '10' needs b >= 1)
    s = 1, a >= 1(*), b >= 1  s -> 0, a - 1, b + 1, borrow at separator i+1      (s -> r)
    (*) a >= 2 at separator 0

It takes 72n + 6j + 182 + 4m + 10[last rule is q -> p] steps, j = bit position of the last separator touched and m
the number of s -> r; then n -> n + 2.  When this does not apply and the word is 01 + W (first block a single
010), the configuration is the other phase of a tick: it moves as W with n - 1, in 90 more steps (`shifted`;
CHECK_SHIFTED of these are compared with the machine).

Everything else is an EVENT (the borrow reaches the far end, the timer runs out, a block in the middle runs out):
the machine itself is run on a copy with every block cut to CUT copies and n to NCUT, and the result is lifted back
(each block, and n, is increased by one in a second run to read off how the result and the step count depend on
it; they are assumed affine in each size, and `VERIFY` repeats the event with other cut sizes and compares).
"""
import sys

M6 = "1RB1LD_1RC1RE_1LA0RA_1RC0LB_0LA1RF_---1RD"
M7 = "1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC"
V = '010'


def table(m):
    tr = {}
    for s, blk in enumerate(m.split('_')):
        for r in range(2):
            t = blk[3 * r:3 * r + 3]
            tr[(s, r)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return tr


TR = table(M6)


def use_machine(m):
    global TR
    TR = table(m)


def oracle(n, u, maxsteps=10 ** 8):
    """run the machine from P1 (n, bits u) to the next P1; returns (n2, bits2, steps) or ('HALT', steps) or None"""
    left = [1, 1, 1, 0] + [1, 1, 1, 1, 1, 0] * n + [1]
    tape = {}
    for i, c in enumerate(left): tape[i - len(left)] = c
    for i, b in enumerate(u): tape[2 * i] = 1; tape[2 * i + 1] = int(b)
    pos = 0; st = 0; lo = -len(left); hi = 2 * len(u) - 1
    prev = pos; dirn = 1; last = pos
    for k in range(1, maxsteps + 1):
        t = TR[(st, tape.get(pos, 0))]
        if t is None: return ('HALT', k)
        tape[pos] = t[0]; pos += t[1]; st = t[2]
        if pos < lo: lo = pos
        if pos > hi: hi = pos
        nd = 1 if pos > prev else -1
        if nd != dirn:
            if abs(prev - last) >= 30 and st == 0 and tape.get(pos - 1, 0) == 1:
                p = pos - 2; m = 0
                while [tape.get(p - j, 0) for j in range(6)] == [0, 1, 1, 1, 1, 1]: p -= 6; m += 1
                if ([tape.get(p - j, 0) for j in range(4)] == [0, 1, 1, 1] and m % 2 == 0
                        and all(tape.get(q, 0) == 0 for q in range(lo, p - 3))):
                    bits = []; q = pos
                    while q <= hi:
                        bits.append(str(tape.get(q + 1, 0)) if tape.get(q, 0) == 1 else '?'); q += 2
                    return (m, ''.join(bits), k)
            last = prev; dirn = nd
        prev = pos
    return None


def tokenize(bits):
    xs = []; ss = []; s = ''; x = 0; i = 0; L = len(bits)
    while i < L:
        if bits.startswith(V, i):
            if s: xs.append(x); ss.append(s); x = 0; s = ''
            x += 1; i += 3
        else:
            s += bits[i]; i += 1
    xs.append(x)
    return xs, ss, s


def tostr(xs, ss, tail):
    return ''.join(V * x + (ss[j] if j < len(ss) else '') for j, x in enumerate(xs)) + tail


def comp(xs, ss, tail):
    return ''.join((('<%d>' % x) if x >= 2 else V * x) + (ss[j] if j < len(ss) else '')
                   for j, x in enumerate(xs)) + tail


def retok(xs, ss, tail, lo, hi):
    """re-cut blocks lo..hi greedily (big blocks stay runs); returns the new tail"""
    K = len(xs) - 1
    while lo > 0 and xs[lo] < 3: lo -= 1
    while hi < K and xs[hi] < 3: hi += 1
    hi = min(hi, K); last = hi == K
    runs = []; parts = []
    for j in range(lo, hi + 1):
        x = xs[j]
        if x > 8: parts.append(V * 3 + '#' + V * 3); runs.append(x - 6)
        else: parts.append(V * x)
        if j < hi: parts.append(ss[j])
    if last: parts.append(tail)
    b = ''.join(parts)
    nx = []; ns = []; cur = ''; x = 0; i = 0; r = 0
    while i < len(b):
        if b[i] == '#':
            assert cur == '', 'misaligned run'
            x += runs[r]; r += 1; i += 1
        elif b.startswith(V, i):
            if cur: nx.append(x); ns.append(cur); x = 0; cur = ''
            x += 1; i += 3
        else:
            cur += b[i]; i += 1
    nx.append(x)
    if last:
        xs[lo:] = nx; ss[lo:] = ns
        return cur
    assert cur == '', 'window ends inside a separator'
    xs[lo:hi + 1] = nx; ss[lo:hi] = ns
    return tail


def tick0(st):
    n, xs, ss, tail = st
    i = 0; pos = 3 * xs[0]; ops = []
    while True:
        if i >= len(ss): return None
        s = ss[i]; a = xs[i]; b = xs[i + 1]; amin = 2 if i == 0 else 1
        if s.startswith('00'): ops.append(('d', i)); break
        if s == '0' and b >= 1: ops.append(('r', i)); break
        if a >= amin and (s.startswith('100') or (s == '10' and b >= 1)): ops.append(('q', i)); break
        if a >= amin and s == '1' and b >= 1:
            ops.append(('s', i)); pos += len(s) + 3 * b; i += 1; continue
        return None
    steps = 72 * n + 6 * pos + 182 + 4 * (len(ops) - 1) + (10 if ops[-1][0] == 'q' else 0)
    for op, j in ops:
        if op == 's': xs[j] -= 1; ss[j] = '0'; xs[j + 1] += 1
        elif op == 'd': ss[j] = ss[j][2:]
        elif op == 'r': ss[j] = '10'; xs[j + 1] -= 1
        else: xs[j] -= 1; ss[j] = '001' + ss[j][2:]
    j = ops[-1][1]; lo = j - 1
    for op, k in ops:
        if xs[k] == 0: lo = min(lo, k - 1)
    st[3] = retok(xs, ss, tail, max(lo, 0), j + 2)
    st[0] = n + 2
    return steps


def shifted(st):
    """the word 01 + W with the timer of 01 + W used up: it is the other phase of the tick, and moves as W with n - 1
    (90 more steps).  Only used when the ordinary tick does not apply and the first block is a single 010."""
    n, xs, ss, tail = st
    if len(xs) < 2 or xs[0] != 1: return None
    sub = [n - 1, [0] + xs[1:], ['0' + ss[0]] + ss[1:], tail]
    sub[3] = retok(sub[1], sub[2], sub[3], 0, 1)
    if sub[1][0] == 0: return None
    d = tick0(sub)
    if d is None: return None
    xs2 = [0] + sub[1]; ss2 = ['01'] + sub[2]
    t2 = retok(xs2, ss2, sub[3], 0, 1)
    st[0] = n + 2; st[1] = xs2; st[2] = ss2; st[3] = t2
    return d + 90


def wall(st):
    """the word 0101 + v^x (a timer of one and an s): 72n + 228 steps to <2>10<x-2>; then <2>10 -> <1>001 -> <1>1 are
    ordinary ticks, so the block after the s runs down by 2 every 3 ticks and no borrow passes it (Lean: tick_w)"""
    n, xs, ss, tail = st
    if len(xs) >= 2 and xs[0] == 1 and ss[0] == '1' and xs[1] >= 3:
        xs[0] = 2; xs[1] -= 2; ss[0] = '10'; st[0] = n + 2
        return 72 * n + 228
    return None


def tick(st):
    """the ordinary tick, else `wall`, else the tick of the other phase; None if neither applies (an event)"""
    global SHIFTED, WALL
    save = [st[0], st[1][:], st[2][:], st[3]]

    def fresh():
        return [save[0], save[1][:], save[2][:], save[3]]
    d = tick0(st)
    if d is not None: return d
    for rule in (wall, shifted):
        st[:] = fresh()
        d = rule(st)
        if d is None: continue
        if rule is wall: WALL += 1; k = WALL
        else: SHIFTED += 1; k = SHIFTED
        if k <= CHECK_SHIFTED:                # compare with the machine (cut copy), as for an event
            other = fresh()
            d2 = event(other)
            assert other == st and d2 == d, (rule.__name__ + ' disagrees with the machine', save, st, other, d, d2)
        return d
    st[:] = fresh()
    return None


SHIFTED = 0
WALL = 0
CHECK_SHIFTED = 0


CUT = 40; NCUT = 30


def lifted(n, xs, ss, tail):
    r = oracle(n, tostr(xs, ss, tail))
    if r is None or r[0] == 'HALT': return r
    return r[0], tokenize(r[1]), r[2]


def event(st, C=None, NC=None):
    C = C or CUT; NC = NC or NCUT
    n, xs, ss, tail = st
    cut = [min(x, C) for x in xs]; nc = min(n, NC)
    r0 = lifted(nc, cut, ss, tail)
    if r0 is None or r0[0] == 'HALT': return ('HALT', r0)
    n0, (nx, ns, nt), s0 = r0
    add = [0] * len(nx); steps = s0; dn = 0

    def slope(nn, cc):
        r = lifted(nn, cc, ss, tail)
        assert r is not None and r[0] != 'HALT'
        n1, (nx1, ns1, nt1), s1 = r
        assert ns1 == ns and nt1 == nt and len(nx1) == len(nx), 'structure depends on a size'
        return n1 - n0, [p - q for p, q in zip(nx1, nx)], s1 - s0
    if n > nc:
        a, d, ds = slope(nc + 2, cut); m = (n - nc) // 2
        for k in range(len(nx)): add[k] += m * d[k]
        steps += m * ds; dn = m * a
    for k, x in enumerate(xs):
        if x > C:
            c2 = cut[:]; c2[k] += 1
            a, d, ds = slope(nc, c2); assert a == 0
            for m2 in range(len(nx)): add[m2] += (x - C) * d[m2]
            steps += (x - C) * ds
    st[0] = n0 + dn; st[1] = [p + q for p, q in zip(nx, add)]; st[2] = ns; st[3] = nt
    return steps


VERIFY = False


def move(st):
    """one tick boundary to the next: returns (steps, was_event); steps is ('HALT', ...) if the cut copy halts"""
    s = tick(st)
    if s is not None: return s, False
    if VERIFY:
        other = [st[0], st[1][:], st[2][:], st[3]]
        d2 = event(other, CUT + 7, NCUT + 8)
    d = event(st)
    if VERIFY and not isinstance(d, tuple):
        assert other == st and d2 == d, ('cut sizes disagree', st, other, d, d2)
    return d, True


def state(n, bits):
    xs, ss, tail = tokenize(bits)
    return [n, xs, ss, tail]


START = (2122, 6, '0100' + V * 3 + '11')     # the first P1 row of the run from blank tape
