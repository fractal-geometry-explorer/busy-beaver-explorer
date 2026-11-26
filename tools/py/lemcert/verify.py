"""Sampling check of a node set: run concrete instances of each node and test that every exit is covered."""
import random, re

def parse_tm(m):
    T = {}
    for i, s in enumerate(m.split('_')):
        for b in (0, 1):
            t = s[3 * b:3 * b + 3]
            T[(i, b)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return T

def inst_count(e, rnd):
    if isinstance(e[0], str):           # ('ge', c[, p])
        p = e[2] if len(e) == 3 else 1
        return e[1] + p * rnd.randint(0, 3)
    if e[1]:
        return None
    return e[0]

def inst_side(side, rnd, nany=40):
    """cells nearest first, and the term."""
    items, term = side
    out = []
    for w, e in items:
        n = inst_count(e, rnd)
        if n is None:
            return None
        out.extend(list(w) * n)
    if term == 'A':
        out.extend(rnd.randint(0, 1) for _ in range(nany))
    return out, term

def side_regex(side):
    items, term = side
    r = ''
    for w, e in items:
        ws = ''.join(map(str, w))
        if isinstance(e[0], str):
            p = e[2] if len(e) == 3 else 1
            r += f'(?:{ws}){{{e[1]}}}(?:(?:{ws}){{{p}}})*'
        else:
            if e[1]:
                return None
            r += f'(?:{ws}){{{e[0]}}}'
    if term == 'A':
        r += '[01]*'
    elif term == 'B':
        r += '0*'
    else:
        return None
    return re.compile('^' + r + '$')

def check_node(T, N, exits, rnd, samples=10, maxsteps=20000):
    q0, f, L, R = N
    bad = []
    for s in range(samples):
        li = inst_side(L, rnd); ri = inst_side(R, rnd)
        if li is None or ri is None:
            return ['symbolic']
        (lc, lt), (rc, rt) = li, ri
        if lt == 'S' and rt == 'S':
            return []
        tape = {}
        # head cell: f == 'R' -> head on first cell of R (pos 0); left cells at -1, -2...
        for i, b in enumerate(lc):
            tape[-1 - i] = b
        for i, b in enumerate(rc):
            tape[i] = b
        pos = 0 if f == 'R' else -1
        lo_bound = -len(lc) - 1 if lt == 'S' else None
        hi_bound = len(rc) if rt == 'S' else None
        q = q0
        for step in range(maxsteps):
            if lo_bound is not None and pos <= lo_bound:
                break
            if hi_bound is not None and pos >= hi_bound:
                break
            b = tape.get(pos, 0)
            t = T[(q, b)]
            if t is None:
                bad.append(('halt', s))
                break
            tape[pos] = t[0]; pos += t[1]; q = t[2]
        else:
            continue                      # ran long: no exit observed
        if bad and bad[-1][1] == s:
            continue
        # exited: other side cells
        if lo_bound is not None and pos <= lo_bound:
            hi = max(list(tape) + [pos]) + 1
            cells = ''.join(str(tape.get(x, 0)) for x in range(pos + 1, hi + 1))
            fexit = 'L'
        else:
            lo = min(list(tape) + [pos]) - 1
            cells = ''.join(str(tape.get(x, 0)) for x in range(pos - 1, lo - 1, -1))
            fexit = 'R'
        ok = False
        for (q2, f2, X) in exits:
            if q2 != q or f2 != fexit:
                continue
            rg = side_regex(X)
            if rg is None or rg.match(cells.rstrip('0') + '0' * 0) or rg.match(cells):
                ok = True
                break
        if not ok:
            bad.append(('exit', s, 'ABCDEF'[q], fexit, cells[:60]))
    return bad

def check_all(P, m, samples=10, seed=1):
    T = parse_tm(m)
    rnd = random.Random(seed)
    nbad = 0
    for i, nd in enumerate(P.nodes):
        N = nd['N']
        if N[2][1] != 'S' and N[3][1] != 'S':
            continue
        b = check_node(T, N, nd['exits'], rnd, samples)
        if b and b != ['symbolic']:
            nbad += 1
            yield i, b
