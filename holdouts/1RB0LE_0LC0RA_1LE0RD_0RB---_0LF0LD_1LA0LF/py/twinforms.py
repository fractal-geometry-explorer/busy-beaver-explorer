"""The twin 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC--- against the visit functions of this machine.

usage: twinforms.py [N]
1. The round law on random tapes: started in E on `0 0 0 1 0 S` (blank to the left), the twin reaches
   `0 0 0 1 0 1 0 A(S)` at its second visit of E to a new leftmost cell, for N random S, or halts exactly when
   A(S) meets E(1 1 ...).
2. The twin's entry forms (state, two cells to the left, nearest first) on random token tapes with at most one
   defect: B after 1 0 computes A, C after 1 0 computes E, B after 0 0 computes E on 0 S; C after 1 1 and A after
   0 1 give the same with a different first cell.
3. Every token rule of this machine as a run of the twin, symbolically, calling only those forms on the tail.
"""
import random, sys, itertools
sys.setrecursionlimit(100000)
TWIN = "1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---"
TW = {}
for qi, q in enumerate(TWIN.split('_')):
    for c in (0, 1):
        t = q[3 * c:3 * c + 3]
        TW[(qi, c)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, 'ABCDEF'.index(t[2]))

# the four visit functions of 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF (mirrored tape), on tuples
class Halt(Exception): pass
def A(S): return (1,) + S[1:] if S[0] == 0 else P((1,) + E(S[1:]))
def E(S):
    a, b, T = S[0], S[1], S[2:]
    if (a, b) == (0, 0): return (1, 0) + A(T)
    if (a, b) == (1, 0): return (1, 0) + E(T)
    if (a, b) == (0, 1): return P((0,) + F((1,) + T))
    raise Halt
def F(S):
    return (1, 0) + A(S[2:]) if S[1] == 0 else P((1,) + F((1,) + S[2:]))
def P(S): return (1, 0) + E(S[2:]) if S[1] == 0 else (0, 0) + S[2:]

def pad(S, n=60): return tuple(S) + (0,) * n
def norm(S):
    S = list(S)
    while S and S[-1] == 0: S.pop()
    return tuple(S)

def twround(S, lim=10 ** 7):
    tape = {i: b for i, b in enumerate((0, 0, 0, 1, 0) + tuple(S))}
    pos = 0; st = 4; lo = 0; ev = 0; n = 0
    while n < lim:
        if pos < lo and st == 4:
            ev += 1
            if ev == 2: return norm(tuple(tape.get(j, 0) for j in range(pos, pos + len(S) + 200)))
        lo = min(lo, pos)
        t = TW[(st, tape.get(pos, 0))]
        if t is None: return 'H'
        tape[pos] = t[0]; pos += t[1]; st = t[2]; n += 1
    return 'L'

def cvisit(X, u, S, lim=10 ** 5):
    """Head on S[0] in state X, cells u to the left (nearest first); until the head leaves u to the left."""
    tape = {i: b for i, b in enumerate(S)}
    for i, b in enumerate(u): tape[-1 - i] = b
    pos = 0; st = X; n = 0; k = len(u)
    while pos >= -k and n < lim:
        t = TW[(st, tape.get(pos, 0))]
        if t is None: return None
        tape[pos] = t[0]; pos += t[1]; st = t[2]; n += 1
    if n >= lim: return None
    return st, tuple(tape[-1 - i] for i in range(k)), norm(tuple(tape.get(i, 0) for i in range(len(S) + 5)))

W = {'L': '1010', 'O': '000', 'I': '100', 'x': '10', '1': '1', 'z': '0'}
def tb(s): return [int(c) for c in ''.join(W[t] for t in s)]

N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
random.seed(9)
ok = both = bad = 0
for _ in range(N):
    S = pad(tuple(random.randint(0, 1) for _ in range(random.randint(0, 30))))
    try: r = norm((1, 0) + A(S))
    except Halt: r = 'halt'
    v = twround(S)
    if v in ('H', 'L'):
        if v == 'H' and r == 'halt': both += 1
        else: bad += 1
    elif r != 'halt' and v == norm((0, 0, 0, 1, 0) + r): ok += 1
    else: bad += 1
print(f"1. round law: {ok} tapes agree, {both} halt in both, {bad} disagree")

random.seed(11)
def rgood():
    n = random.randint(0, 8); w = [random.choice('LOI') for _ in range(n)]
    if random.random() < 0.6: w.insert(random.randint(0, n), random.choice('x1z'))
    return w
TT = [pad(tb(rgood())) for _ in range(400)]
checks = [  # name, state, ctx, input, expected result, expected exit (state, ctx)
    ('A: B after 1 0', 1, (1, 0), lambda S: S, lambda S: A(S), lambda r: (4, (0, 0))),
    ('E: C after 1 0', 2, (1, 0), lambda S: S, lambda S: E(S), lambda r: (4, (0, 0))),
    ('E on 0 S: B after 0 0', 1, (0, 0), lambda S: (0,) + S, lambda S: E((0,) + S), lambda r: (4, (0, 0))),
    ('A on 1 S without its first cell: C after 1 1', 2, (1, 1), lambda S: S, lambda S: A((1,) + S)[1:],
     None),
    ('E on 0 S without its first cell: A after 0 1', 0, (0, 1), lambda S: S, lambda S: E((0,) + S)[1:], None),
]
for name, X, u, inp, f, ex in checks:
    good = n = 0
    for S in TT:
        try: r = norm(f(S))
        except Halt: continue
        n += 1
        v = cvisit(X, u, inp(S))
        if v is None or v[2] != r: continue
        if ex is not None and v[:2] != ex(r): continue
        good += 1
    print(f"2. {name}: {good}/{n}")

TAIL = {(1, (1, 0)): ('A', [], 4), (2, (1, 0)): ('Eh', [1, 0], 4), (2, (1, 1)): ('Eh', [0, 0], 3),
        (0, (0, 1)): ('E0', 'drop1', None)}
PRE = {(1, (0, 0)): ('E0', 4), (2, (1, 0)): ('E0', 4)}
def sym(X, u, w, maxn=500):
    k = len(u); outs = []
    def go(cells, m, pos, st, n, calls, tail, cnt):
        while pos >= -k and n < maxn:
            ctx = (cells.get(pos - 1), cells.get(pos - 2))
            if pos == m:
                if (st, ctx) not in TAIL: outs.append(('stuck', 'ABCDEF'[st], ctx)); return
                f, new, ex = TAIL[(st, ctx)]
                cnt += 1; nm = 't%d' % cnt
                if new == 'drop1':
                    for c in (0, 1):  # E0(tail) = c :: nm; the exit state depends on c
                        c2 = dict(cells); c2[pos - 1] = 0; c2[pos - 2] = 0
                        go(c2, m, pos - 3, 3 if c == 0 else 2, n + 1, calls + [f'{f}({tail})={c}{nm}'], nm, cnt)
                    return
                calls = calls + [f'{nm}={f}({tail})']; tail = nm
                for i, b in enumerate(new): cells[m + i] = b
                m += len(new); cells[pos - 1] = 0; cells[pos - 2] = 0; pos -= 3; st = ex; n += 1; continue
            if pos == m - 1 and cells[pos] == 0 and (st, ctx) in PRE:
                f, ex = PRE[(st, ctx)]
                cnt += 1; nm = 't%d' % cnt; calls = calls + [f'{nm}=E0({tail})']; tail = nm
                del cells[m - 1]; m -= 1
                cells[pos - 1] = 0; cells[pos - 2] = 0; pos -= 3; st = ex; n += 1; continue
            t = TW[(st, cells[pos])]
            if t is None: outs.append(('halt',)); return
            cells[pos] = t[0]; pos += t[1]; st = t[2]; n += 1
        if n >= maxn: outs.append(('loop',)); return
        outs.append(('exit', 'ABCDEF'[st], ''.join(str(cells[i]) for i in range(m)) + '+' + tail, ' '.join(calls)))
    cells = {-1 - i: b for i, b in enumerate(u)}
    for i, b in enumerate(w): cells[i] = b
    go(cells, len(w), 0, X, 0, [], 'T', 0)
    return outs
rules = {'A': ['L', 'O', 'I', 'z', 'xO', 'xI', 'xL', '1'], 'Eh': ['L', 'O', 'I'], 'E0': ['O', 'L', 'I']}
forms = {'A': [(1, (1, 0), False)], 'Eh': [(2, (1, 0), False), (2, (1, 1), False)],
         'E0': [(1, (0, 0), True), (0, (0, 1), False)]}
for k in rules:
    for p in rules[k]:
        for X, u, z in forms[k]:
            w = ([0] if z else []) + tb(p)
            print(f"3. {k} {p:2} {'ABCDEF'[X]} after {u}: {sym(X, u, w)}")
