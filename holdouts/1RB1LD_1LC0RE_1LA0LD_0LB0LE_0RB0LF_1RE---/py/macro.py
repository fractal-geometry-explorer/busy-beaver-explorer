"""The macro map of 1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---.

State (y, word) at a tick boundary ("P1"):

    [reverse(word)] 1 0 1 0 0 E> 0 (1110)^y 1 1 1 1 1 1 0^inf

The word is the tape left of the marker 10100, read from the head outwards and cut at the last 1.  v = 0001 is a
block (1000 on the tape), and the separators are c = 010101, r = 01, z = 00 (tape 101010, 10, 00) and the irregular
1, 01101, 00101 (tape 1, 10110, 10100).  The word is kept as tokens xs (blocks), ss (separators), tail, cut greedily
from the head.  A tick is a borrow into separator 0; at separator i (block a before it, b after it; a >= 1):

    A  s starts with 01      a - 1, s -> 00 + s[2:]      (c -> r, r -> z, 01101 -> 00101)
    C  s starts with 00101   s -> s[4:]                  (00101 -> 1)
    D  s = 1, b >= 1         a - 1, b - 1, s -> 01101
    B  s = 00, b >= 1        a - 1, s -> 010101, borrow at separator i+1      (z -> c)

It takes 30y + 5j/2 + 210 + 13m + (0, 12, 6 for A, C, D) steps, j = cell position of the last separator touched
and m the number of B; then y -> y + 4.  Everything else is an EVENT (the borrow reaches the far end, the timer runs
out): the machine itself is run on a copy with every block cut to CUT copies and y to YCUT, and the result is
lifted back (each block, and y, is increased in a second run to read off how the result and the step count depend
on it; they are assumed affine in each size, and `VERIFY` repeats the event with other cut sizes and compares).
"""

M2 = "1RB1LD_1LC0RE_1LA0LD_0LB0LE_0RB0LF_1RE---"


def table(m):
    tr = {}
    for s, blk in enumerate(m.split('_')):
        for r in range(2):
            t = blk[3 * r:3 * r + 3]
            tr[(s, r)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return tr


TR = table(M2)


def oracle(y,u,maxsteps=10**8):
    left=[int(c) for c in reversed(u)]+[1,0,1,0,0]
    right=[0]+[1,1,1,0]*y+[1]*6
    tape={}
    for i,c in enumerate(left): tape[i-len(left)]=c
    for i,c in enumerate(right): tape[i]=c
    pos=0; st=4; lo=-len(left); hi=len(right)-1
    prev=pos; dirn=-1; last=pos
    for k in range(1,maxsteps+1):
        r=tape.get(pos,0); t=TR[(st,r)]
        if t is None: return ('HALT',k)
        tape[pos]=t[0]; pos+=t[1]; st=t[2]
        if pos<lo: lo=pos
        if pos>hi: hi=pos
        nd=1 if pos>prev else -1
        if nd!=dirn:
            if abs(prev-last)>=30 and st==4 and tape.get(pos,0)==0:
                p=pos+1; yy=0
                while [tape.get(p+j,0) for j in range(4)]==[1,1,1,0]: p+=4; yy+=1
                ok=all(tape.get(p+j,0)==1 for j in range(6)) and all(tape.get(q,0)==0 for q in range(p+6,hi+1))
                ok=ok and [tape.get(pos-5+j,0) for j in range(5)]==[1,0,1,0,0]
                if ok:
                    q=pos-6; first=lo
                    while first<q and tape.get(first,0)==0: first+=1
                    w=''.join(str(tape.get(c,0)) for c in range(q,first-1,-1))
                    return (yy,w,k)
            last=prev; dirn=nd
        prev=pos
    return None


V = '0001'

def tokenize(bits):
    xs = []; ss = []; s = ''; x = 0; i = 0; L = len(bits)
    while i < L:
        if bits.startswith(V, i):
            if s: xs.append(x); ss.append(s); x = 0; s = ''
            x += 1; i += 4
        else:
            s += bits[i]; i += 1
    xs.append(x)
    return xs, ss, s

def tostr(xs, ss, tail):
    return ''.join(V * x + (ss[j] if j < len(ss) else '') for j, x in enumerate(xs)) + tail

def comp(xs, ss, tail):
    return ''.join((('<%d>' % x) if x >= 2 else V * x) + (ss[j] if j < len(ss) else '') for j, x in enumerate(xs)) + tail

def retok(xs, ss, tail, lo, hi):
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
            x += 1; i += 4
        else:
            cur += b[i]; i += 1
    nx.append(x)
    if last:
        xs[lo:] = nx; ss[lo:] = ns
        return cur
    assert cur == '', 'window ends inside a separator'
    xs[lo:hi + 1] = nx; ss[lo:hi] = ns
    return tail

def tick(st):
    y, xs, ss, tail = st
    i = 0; pos = 4 * xs[0]; ops = []
    while True:
        if i >= len(ss): return None
        s = ss[i]; a = xs[i]; b = xs[i + 1]
        if a < 1: return None
        if s.startswith('01'): ops.append(('A', i)); break
        if s.startswith('00101'): ops.append(('C', i)); break
        if s == '1' and b >= 1: ops.append(('D', i)); break
        if s == '00' and b >= 1:
            ops.append(('B', i)); pos += len(s) + 4 * b; i += 1; continue
        return None
    nb = len(ops) - 1
    steps = 30 * y + (5 * pos) // 2 + 210 + 13 * nb + {'A': 0, 'C': 12, 'D': 6}[ops[-1][0]]
    assert pos % 2 == 0
    for op, j in ops:
        if op == 'B': xs[j] -= 1; ss[j] = '010101'
        elif op == 'A': xs[j] -= 1; ss[j] = '00' + ss[j][2:]
        elif op == 'C': ss[j] = ss[j][4:]
        else: xs[j] -= 1; xs[j + 1] -= 1; ss[j] = '01101'
    j = ops[-1][1]; lo = j - 1
    for op, k in ops:
        if xs[k] == 0: lo = min(lo, k - 1)
    st[3] = retok(xs, ss, tail, max(lo, 0), j + 2)
    st[0] = y + 4
    return steps

CUT = 40; YCUT = 40
def lift_run(y, xs, ss, tail):
    r = oracle(y, tostr(xs, ss, tail), 10 ** 8)
    if r is None or r[0] == 'HALT': return r
    return r[0], tokenize(r[1]), r[2]

def event(st, C=None, YC=None):
    C = C or CUT; YC = YC or YCUT
    y, xs, ss, tail = st
    cut = [min(x, C) for x in xs]
    yc = y if y <= YC else YC + (y - YC) % 4
    r0 = lift_run(yc, cut, ss, tail)
    if r0 is None or r0[0] == 'HALT': return ('HALT', r0)
    y0, (nx, ns, nt), s0 = r0
    add = [0] * len(nx); steps = s0; dy = 0
    def slope(yy, cc):
        r = lift_run(yy, cc, ss, tail)
        assert r is not None and r[0] != 'HALT'
        y1, (nx1, ns1, nt1), s1 = r
        assert ns1 == ns and nt1 == nt and len(nx1) == len(nx), 'structure depends on a size'
        return y1 - y0, [p - q for p, q in zip(nx1, nx)], s1 - s0
    if y > yc:
        a, d, ds = slope(yc + 4, cut); m = (y - yc) // 4
        for k in range(len(nx)): add[k] += m * d[k]
        steps += m * ds; dy = m * a
    for k, x in enumerate(xs):
        if x > C:
            c2 = cut[:]; c2[k] += 1
            a, d, ds = slope(yc, c2); assert a == 0
            for m2 in range(len(nx)): add[m2] += (x - C) * d[m2]
            steps += (x - C) * ds
    st[0] = y0 + dy; st[1] = [p + q for p, q in zip(nx, add)]; st[2] = ns; st[3] = nt
    return steps

def state(y, bits):
    xs, ss, tail = tokenize(bits)
    return [y, xs, ss, tail]

VERIFY = False
SHIFTED = 0


def use_machine(m):
    global TR
    TR = table(m)


def move(st):
    """one tick boundary to the next: returns (steps, was_event); steps is ('HALT', ...) if the cut copy halts"""
    s = tick(st)
    if s is not None: return s, False
    if VERIFY:
        other = [st[0], st[1][:], st[2][:], st[3]]
        d2 = event(other, CUT + 7, YCUT + 8)
    d = event(st)
    if VERIFY and not isinstance(d, tuple):
        assert other == st and d2 == d, ('cut sizes disagree', st, other, d, d2)
    return d, True


START = (910, 8, '0001000001011')     # the first tick boundary of the run from blank tape
