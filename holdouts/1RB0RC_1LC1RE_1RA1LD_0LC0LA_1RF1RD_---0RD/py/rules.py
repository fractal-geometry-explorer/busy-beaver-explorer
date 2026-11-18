"""rules.py: the frame map of lean/Phases.lean as a rule table with exact step counts, checked against the machine.

    python3 py/rules.py            # all checks below; exit status 1 on any failure
    python3 py/rules.py table      # the Lean cases with their step counts, read from the Lean files

The map `next` and, for each of its cases, the number of machine steps are read from the Lean files: the case list
from `def next` in lean/Phases.lean, the piece theorem(s) of each case from `next_sound` / `none_halts`, and the step
count from the statement `steps (n) ... = ...` of each piece in lean/Pieces.lean (a halting case: n steps to the
halting configuration, plus the halting step itself).  Then:

  cases   every Lean case on a grid of frames (each variable < R): run the machine exactly n steps from the frame's
          tape and compare the whole tape with the target frame (or check that step n is the halting step);
  rows    every row of the rule table (ROWS: the main cases, the sweeps as k rounds of one case, the halts) on a grid:
          the same direct check, and the same target and step count from iterating the Lean cases;
  example the worked example of the explainer page;
  run     the run from blank tape: the machine and the Lean map side by side; at every frame of the first STEPS
          steps the tapes agree and the step counts add up.
"""
import os, re, sys, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from spec import M, FR
from fm import FM

LEAN = os.path.join(HERE, '..', 'lean')
VAR = re.compile(r'\(\w+ \+ \d+\)|\w+')


def parse_lean():
    """[(frame, patterns, target or None, step expression, pieces)] in the order of `def next`."""
    P = open(os.path.join(LEAN, 'Pieces.lean')).read()
    H = open(os.path.join(LEAN, 'Phases.lean')).read()
    th = {}
    for m in re.finditer(r'theorem (\w+)((?: \([^)]*: Nat\))?) :\s*\n\s*steps \((.*?)\) ⟨', P):
        params = m.group(2).strip()[1:-1].split(':')[0].split() if m.group(2).strip() else []
        th[m.group(1)] = (params, m.group(3))
    body = re.search(r'def next : Ph → Option Ph\n(.*?)\n\n', H, re.S).group(1)
    pieces = {}
    for m in re.finditer(r'\| \.(\w+) (.*?), _, h => by piece2? (.*)', H):
        pieces[(m.group(1), tuple(VAR.findall(m.group(2))))] = [a or b for a, b in re.findall(r'\((pc_\w+(?: \w+)*)\)|(pc_\w+)', m.group(3))]
    for m in re.finditer(r'\| \.(\w+) (.*?), h => by hpiece (.*)', H):
        pieces[(m.group(1), tuple(VAR.findall(m.group(2))))] = [m.group(3).strip().strip('()')]
    out = []
    for line in body.splitlines():
        m = re.match(r'\s*\| \.(\w+) (.*?) => (.*)', line)
        n, pats, rhs = m.group(1), VAR.findall(m.group(2)), m.group(3).strip()
        tgt = None
        if rhs != 'none':
            mm = re.match(r'some \(\.(\w+) (.*)\)$', rhs)
            tgt = (mm.group(1), re.findall(r'\(([^()]*)\)', mm.group(2)))
        pcs = pieces[(n, tuple(pats))]
        ex = []
        for p in pcs:
            nm, *args = p.split()
            params, e = th[nm]
            sub = dict(zip(params, args))
            ex.append('(' + re.sub(r'\b[a-z]\w*\b', lambda q: sub.get(q.group(0), q.group(0)), e) + ')')
        st = ' + '.join(ex) + (' + 1' if tgt is None else '')
        out.append((n, pats, tgt, st, pcs))
    return out


CASES = parse_lean()


def bind(pats, vals):
    env = {}
    for p, v in zip(pats, vals):
        if p.isdigit():
            if v != int(p): return None
        elif p.startswith('('):
            nm, k = re.match(r'\((\w+) \+ (\d+)\)', p).groups()
            if v < int(k): return None
            env[nm] = v - int(k)
        else:
            env[p] = v
    return env


def lean_next(fr):
    """(next frame or None for the halt, steps, case index) by `next` of lean/Phases.lean."""
    n, vals = fr
    for i, (cn, pats, tgt, st, _) in enumerate(CASES):
        if cn != n: continue
        env = bind(pats, vals)
        if env is None: continue
        k = eval(st, {}, dict(env))
        if tgt is None: return None, k, i
        return (tgt[0], tuple(eval(e, {}, dict(env)) for e in tgt[1])), k, i
    raise KeyError(fr)


F = FM(M, FR, True)
VARS = {n: [t.split('^')[1] for t in FR[n].split() if '^' in t] for n in FR}


def tape_of(fr):
    """(cells as a dict, head, state) of a frame."""
    n, vals = fr
    return F.build(n, dict(zip(VARS[n], vals)))


def norm(tape, p, st):
    nz = [i for i, v in tape.items() if v]
    a = min(nz + [p]); b = max(nz + [p])
    return tuple(tape.get(i, 0) for i in range(a, b + 1)), p - a, st


def sim(fr, n):
    """Run the machine n steps from the frame's tape: the normalized configuration, or ('halt', k) if step k halts."""
    tape, p, st = tape_of(fr)
    for k in range(1, n + 1):
        t = F.T[(st, tape.get(p, 0))]
        if t is None: return ('halt', k)
        tape[p] = t[0]; p += t[1]; st = t[2]
    return norm(tape, p, st)


def agrees(src, tgt, n):
    """The machine goes from frame src to frame tgt (None: the halt, at step n exactly) in exactly n steps."""
    if tgt is None:
        return sim(src, n - 1) != ('halt', n - 1) and sim(src, n) == ('halt', n) if n > 1 else sim(src, 1) == ('halt', 1)
    return sim(src, n) == norm(*tape_of(tgt))


# ---- The rule table (as on the explainer page): name, source frame, target frame (None = halt), steps, parameter
# ---- ranges.  A row with k is k rounds of one Lean case.

ROWS = [
    ('zig', 'l j r', lambda l, j, r: ('z', (l + 2, j, r + 1)), lambda l, j, r: ('y', (l, j, r + 1)),
     lambda l, j, r: 2 * j + 2),
    ('zig, bracket', 'l j r', lambda l, j, r: ('Z', (l + 2, j, r + 1)), lambda l, j, r: ('Y', (l, j, r + 1)),
     lambda l, j, r: 2 * j + 2),
    ('zag', 'l j r', lambda l, j, r: ('y', (l + 1, j, r + 2)), lambda l, j, r: ('z', (l, j + 2, r + 1)),
     lambda l, j, r: 2 * j + 3),
    ('zag, bracket', 'l j r', lambda l, j, r: ('Y', (l + 2, j, r + 2)), lambda l, j, r: ('Z', (l + 1, j + 2, r + 1)),
     lambda l, j, r: 2 * j + 3),
    ('zigzag, k rounds', 'l j r k', lambda l, j, r, k: ('z', (l + 3 * k, j, r + k + 1)),
     lambda l, j, r, k: ('z', (l, j + 2 * k, r + 1)), lambda l, j, r, k: 4 * k * k + 4 * j * k + k),
    ('w sweep', 'l j r k', lambda l, j, r, k: ('w', (l, j + 2 * k, r + 1)), lambda l, j, r, k: ('w', (l + 4 * k, j, r + 1)),
     lambda l, j, r, k: 6 * k),
    ('w sweep, bracket', 'l j r k', lambda l, j, r, k: ('W', (l, j + 2 * k, r + 1)),
     lambda l, j, r, k: ('W', (l + 4 * k, j, r + 1)), lambda l, j, r, k: 6 * k),
    ('u sweep', 'l j r k', lambda l, j, r, k: ('u', (l, j + k, r)), lambda l, j, r, k: ('u', (l, j, r + 2 * k)),
     lambda l, j, r, k: 4 * k),
    ('u sweep, bracket', 'l j r k', lambda l, j, r, k: ('U', (l + 1, j + k, r)),
     lambda l, j, r, k: ('U', (l + 1, j, r + 2 * k)), lambda l, j, r, k: 4 * k),
    ('to w', 'j r', lambda j, r: ('z', (0, j + 1, r + 1)), lambda j, r: ('w', (0, j + 1, r + 1)), lambda j, r: 2 * j + 4),
    ('to w, at the wall', 'j r', lambda j, r: ('y', (0, j, r + 2)), lambda j, r: ('z', (0, j + 1, r + 1)),
     lambda j, r: 2 * j + 3),
    ('to u', 'l j', lambda l, j: ('y', (l + 1, j, 1)), lambda l, j: ('u', (l, j + 1, 2)), lambda l, j: 2 * j + 8),
    ('to u, bracket', 'l j', lambda l, j: ('Y', (l + 2, j, 1)), lambda l, j: ('U', (l + 1, j + 1, 2)),
     lambda l, j: 2 * j + 8),
    ('new bracket', 'j r', lambda j, r: ('z', (1, j + 3, r + 1)), lambda j, r: ('W', (4, j, r + 1)),
     lambda j, r: 2 * j + 24),
    ('w back to y', 'l r', lambda l, r: ('w', (l, 0, r + 4)), lambda l, r: ('y', (l + 3, 0, r + 1)), lambda l, r: 5),
    ('w back to y, bracket', 'l r', lambda l, r: ('W', (l, 0, r + 4)), lambda l, r: ('Y', (l + 3, 0, r + 1)),
     lambda l, r: 5),
    ('w to u', 'l r', lambda l, r: ('w', (l, 1, r + 3)), lambda l, r: ('u', (l + 3, 0, r + 1)), lambda l, r: 6),
    ('w to u, bracket', 'l r', lambda l, r: ('W', (l, 1, r + 3)), lambda l, r: ('U', (l + 3, 0, r + 1)),
     lambda l, r: 6),
    ('u back to y', 'l r', lambda l, r: ('u', (l + 1, 0, r)), lambda l, r: ('y', (l, 0, r + 2)), lambda l, r: 4),
    ('u back to y, bracket', 'l r', lambda l, r: ('U', (l + 1, 0, r)), lambda l, r: ('Y', (l, 0, r + 2)),
     lambda l, r: 4),
    ('bracket dissolves', 'j r', lambda j, r: ('Z', (1, j + 1, r + 1)), lambda j, r: ('y', (5, j + 1, r + 1)),
     lambda j, r: 2 * j + 30),
    ('bracket dissolves', 'j r', lambda j, r: ('Y', (0, j, r + 2)), lambda j, r: ('w', (3, j + 1, r + 1)),
     lambda j, r: 4 * j + 7),
    ('bracket dissolves', 'j r', lambda j, r: ('Y', (1, j, r + 2)), lambda j, r: ('z', (2, j + 3, r + 1)),
     lambda j, r: 2 * j + 3),
    ('halt', '', lambda: ('z', (1, 1, 1)), lambda: None, lambda: 19),
    ('halt', 'l', lambda l: ('w', (l, 0, 1)), lambda l: None, lambda l: 5),
    ('halt', 'l', lambda l: ('w', (l, 1, 0)), lambda l: None, lambda l: 5),
    ('halt', 'l', lambda l: ('W', (l, 0, 1)), lambda l: None, lambda l: 5),
    ('halt', 'l', lambda l: ('W', (l, 1, 0)), lambda l: None, lambda l: 5),
]
START = ('z', (0, 0, 2)); START_STEPS = 2
COVERED = set()   # the Lean cases that the table's rows use


def lean_path(src, tgt, limit=10 ** 4):
    """Iterate the Lean cases from src until tgt (or the halt): (reached, steps)."""
    fr, tot = src, 0
    for _ in range(limit):
        nx, k, _ = lean_next(fr)
        tot += k
        if nx is None: return None, tot
        fr = nx
        if fr == tgt: return fr, tot
    return '?', tot


def check_cases(R):
    bad = n = 0
    for name in FR:
        for vals in itertools.product(range(R), repeat=len(VARS[name])):
            nx, k, i = lean_next((name, vals))
            n += 1
            if not agrees((name, vals), nx, k):
                bad += 1
                if bad < 10: print('case differs:', name, vals, CASES[i][:4])
    print(f'cases: {len(CASES)} Lean cases, {n} frames (variables < {R}), {bad} failures')
    return bad


def check_rows(R, K):
    bad = n = 0
    global COVERED
    for name, vs, src, tgt, steps in ROWS:
        nv = len(vs.split())
        for vals in itertools.product(*[range(1, K + 1) if v == 'k' else range(R) for v in vs.split()]):
            s, t, k = src(*vals), tgt(*vals), steps(*vals)
            ok = agrees(s, t, k) and lean_path(s, t) == (t, k)
            n += 1
            if 'k' not in vs.split() or vals[-1] == 1: COVERED.add(lean_next(s)[2])
            if not ok:
                bad += 1
                if bad < 10: print('row differs:', name, vals, s, t, k, lean_path(s, t))
    tape = {}; p = 0; st = 0
    for _ in range(START_STEPS):
        t = F.T[(st, tape.get(p, 0))]; tape[p] = t[0]; p += t[1]; st = t[2]
    if norm(tape, p, st) != norm(*tape_of(START)):
        bad += 1; print('start rule differs')
    print(f'rows: {len(ROWS)} rows + start, {n} instances (variables < {R}, k <= {K}), {bad} failures')
    return bad


def check_run(STEPS):
    """The machine from blank tape against the Lean map from START, at every frame of the first STEPS steps."""
    T = F.T
    size = 4 * int(STEPS ** 0.5) + 1000
    tape = bytearray(2 * size); off = size; p = off; st = 0
    fr, due, nfr, bad = START, START_STEPS, 0, 0
    lo = hi = p
    use = collections.Counter()
    for n in range(1, STEPS + 1):
        t = T[(st, tape[p])]
        if t is None: print('the machine halted at', n); bad += 1; break
        tape[p] = t[0]; p += t[1]; st = t[2]
        if p < lo: lo = p
        if p > hi: hi = p
        if n == due:
            a = lo
            while a < p and not tape[a]: a += 1
            b = hi
            while b > p and not tape[b]: b -= 1
            cells, q, s = norm(*tape_of(fr))
            if (bytes(tape[a:b + 1]), p - a, st) != (bytes(cells), q, s):
                bad += 1; print('run differs at step', n, fr); break
            nfr += 1
            nx, k, i = lean_next(fr)
            use[i] += 1
            if nx is None: print('the map halts at', fr); bad += 1; break
            fr, due = nx, n + k
    inrows = sum(c for i, c in use.items() if i in COVERED)
    print(f'run: {nfr} frames in the first {STEPS} steps from blank tape, tapes and step counts agree: '
          f'{"yes" if not bad else "NO"}; {inrows} of the {nfr} moves are rows of the table, '
          f'the other {nfr - inrows} use {sum(1 for i in use if i not in COVERED)} other Lean cases')
    return bad, use


def check_example():
    """The worked example of the page: u(11, 0, 3) halts after 4 + 3 + 63 + 18 + 24 + 5 = 117 steps."""
    rows = [lean_path(('u', (11, 0, 3)), ('y', (10, 0, 5))), lean_path(('y', (10, 0, 5)), ('z', (9, 2, 4))),
            lean_path(('z', (9, 2, 4)), ('z', (0, 8, 1))), lean_path(('z', (0, 8, 1)), ('w', (0, 8, 1))),
            lean_path(('w', (0, 8, 1)), ('w', (16, 0, 1))), lean_path(('w', (16, 0, 1)), None)]
    ks = [k for _, k in rows]
    ok = ks == [4, 3, 63, 18, 24, 5] and sim(('u', (11, 0, 3)), 200) == ('halt', 117)
    print(f'example: u(11, 0, 3) halts after {" + ".join(map(str, ks))} = {sum(ks)} steps by the rules; '
          f'direct simulation: {sim(("u", (11, 0, 3)), 200)}; {"ok" if ok else "FAILED"}')
    return 0 if ok else 1


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'table':
        for n, pats, tgt, st, pcs in CASES:
            print(f"{n}({', '.join(pats)}) -> {tgt[0] + '(' + ', '.join(tgt[1]) + ')' if tgt else 'HALT'}  [{st}]  {' '.join(pcs)}")
        sys.exit(0)
    bad = check_cases(int(os.environ.get('R', 9)))
    bad += check_rows(int(os.environ.get('R', 9)), 6)
    bad += check_example()
    b, use = check_run(int(float(os.environ.get('STEPS', 1e7))))
    bad += b
    sys.exit(1 if bad else 0)
