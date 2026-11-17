"""rules.py: the phase map of lean/Phases.lean of 1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE as a rule table with exact step counts,
checked against the machine.

    python3 py/rules.py            # all checks below; exit status 1 on any failure
    python3 py/rules.py table      # the Lean cases with the step counts of their piece theorems

    E(x, z)    = 0^inf E> 0 (10)^x 1^z 0^inf
    A(x, y)    = 0^inf (10)^x 1^y A> 0^inf
    Q(m, j, t) = 0^inf (10)^m 1 D> 0 0 (1010)^j 1^t 0^inf

The map `next` and the step count of each of its cases are read from the Lean files: the cases from `def next` in
lean/Phases.lean, the piece theorem(s) of each case from `next_sound` (a bounce case: `q_rounds`, that many rounds of
`pc_round`; a halt: `e_halts`, its piece plus the halting step), and the count from the statement `steps (n) ...` of
each piece in lean/Pieces.lean.  Then:

  cases   every phase with variables < R: the Lean step count equals py/phasemap.py's, and the machine run exactly
          that many steps lands on the Lean target (or halts at that step);
  rows    every row of the rule table (ROWS: the two doubling phases, made of several cases, and the cases grouped
          as on the page) on a grid: the same direct check, and the same target and steps from the Lean cases;
  example the worked example of the explainer page;
  run     the run from blank tape: the machine and the Lean map side by side, tapes equal at every phase of the
          first STEPS steps.
"""
import os, re, sys, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import phasemap as PM

LEAN = os.path.join(HERE, '..', 'lean')
TOK = re.compile(r'\(\w+ \+ \d+\)|\w+')


def args_of(s):
    """Split 'x 0 (b + 1) (min (x) (y))' into its top-level arguments, without their outer parentheses."""
    out, depth, cur = [], 0, ''
    for ch in s + ' ':
        if ch == ' ' and depth == 0:
            if cur: out.append(cur[1:-1] if cur.startswith('(') else cur)
            cur = ''
            continue
        depth += (ch == '(') - (ch == ')')
        cur += ch
    return out


def py_expr(e):
    e = re.sub(r'min \(([^()]*)\) \(\(([^()]*)\) / 2\)', r'min(\1, (\2) // 2)', e)
    return e.replace(' / ', ' // ')


def parse_lean():
    P = open(os.path.join(LEAN, 'Pieces.lean')).read()
    H = open(os.path.join(LEAN, 'Phases.lean')).read()
    th = {}
    for m in re.finditer(r'theorem (\w+)((?: \([^)]*: Nat\))?) :\s*\n\s*steps \((.*?)\) ⟨', P):
        params = m.group(2).strip()[1:-1].split(':')[0].split() if m.group(2).strip() else []
        th[m.group(1)] = (params, m.group(3))
    body = re.search(r'def next : Ph → Option Ph\n(.*?)\n\n', H, re.S).group(1)
    body = re.sub(r'=>\n\s+', '=> ', body)
    cases = []
    for line in body.splitlines():
        m = re.match(r'\s*\| \.(\w+) (.*?) => (.*)', line)
        n, pats, rhs = m.group(1), TOK.findall(m.group(2)), m.group(3).strip()
        if rhs == 'none': cases.append((n, pats, None)); continue
        mm = re.match(r'some \(\.(\w+) (.*)\)$', rhs)
        cases.append((n, pats, (mm.group(1), [py_expr(a) for a in args_of(mm.group(2))])))
    sound = re.search(r'theorem next_sound.*?\n(.*?)\n\n', H, re.S).group(1)
    pieces = []          # (frame, patterns, pieces) of `next_sound`, in order
    for line in sound.splitlines():
        m = re.match(r'  \| \.(\w+) (.*?), _, h => by(.*)', line)
        if m:
            pieces.append((m.group(1), TOK.findall(m.group(2)), []))
            rest = m.group(3)
        else:
            rest = line
        for pm in re.finditer(r'(?:piece|steps_eq_of) \((pc_\w+(?: \w+)*)\)|piece (pc_\w+)', rest):
            pieces[-1][2].append(pm.group(1) or pm.group(2))
        if 'q_rounds' in rest: pieces[-1][2].append('ROUNDS')
    assert '⟨_, _, pc_eh0 x, rfl⟩' in H and '⟨_, _, pc_eh1 x, rfl⟩' in H     # e_halts: E(x, 0) and E(x, 1)
    halts = {'0': 'pc_eh0', '1': 'pc_eh1'}
    init = re.search(r'theorem init_\w+ : (?:steps (\d+) init = some|init =) \(Ph\.(\w) (\d+) (\d+)\)\.cfg', H)
    start = ((init.group(2), int(init.group(3)), int(init.group(4))), int(init.group(1) or 0))
    return th, cases, pieces, halts, start


TH, CASES, PIECES, HALTS, START = parse_lean()


def bind(pats, vals):
    env = {}
    for p, v in zip(pats, vals):
        if p == '_': continue
        if p.isdigit():
            if v != int(p): return None
        elif p.startswith('('):
            nm, k = re.match(r'\((\w+) \+ (\d+)\)', p).groups()
            if v < int(k): return None
            env[nm] = v - int(k)
        else:
            env[p] = v
    return env


def piece_steps(call, env):
    nm, *args = call.split()
    params, e = TH[nm]
    return eval(py_expr(e), {}, {p: eval(a, {}, env) for p, a in zip(params, args)})


def lean_next(p):
    """(next phase or None for the halt, steps, case index): `next` of lean/Phases.lean; the steps are those of the
    piece theorems of lean/Pieces.lean that `next_sound` uses (a halt: `e_halts`' piece plus the halting step)."""
    n, vals = p[0], tuple(p[1:])
    for i, (cn, pats, tgt) in enumerate(CASES):
        if cn != n: continue
        env = bind(pats, vals)
        if env is None: continue
        if tgt is None:
            return None, piece_steps(HALTS[str(vals[1])] + ' x', {'x': vals[0]}) + 1, i
        nxt = (tgt[0],) + tuple(eval(a, {'min': min}, dict(env)) for a in tgt[1])
        pn, pp, pcs = next((a, b, c) for a, b, c in PIECES if a == n and bind(b, vals) is not None)
        env = bind(pp, vals)
        if pcs == ['ROUNDS']:
            # b bounces of `pc_round`, the middle count growing by `inc` each time (as `q_rounds` composes them)
            b = vals[0] - nxt[1]; inc = (nxt[2] - vals[1]) // b
            params = TH['pc_round'][0]
            st = sum(eval(py_expr(TH['pc_round'][1]), {}, {params[0]: vals[1] + inc * r, params[1]: 0, params[2]: 0})
                     for r in range(b))
        elif len(pcs) == 2:
            # a parity split: the first piece for an even remainder 2k, the second for 2k + 1
            nv = env['n']
            e2 = dict(env); e2['k'] = nv // 2
            st = piece_steps(pcs[nv % 2], e2)
        else:
            st = piece_steps(pcs[0], env)
        return nxt, st, i
    raise KeyError(p)


def tape(p):
    return PM.norm(*PM.build(p))


def agrees(src, tgt, n):
    """The machine goes from phase src to phase tgt (None: halts at step n exactly) in exactly n steps."""
    cells, pos, st = PM.build(src)
    if tgt is None:
        return PM.simulate(cells, pos, st, n - 1) is not None and PM.simulate(cells, pos, st, n) is None
    return PM.simulate(cells, pos, st, n) == tape(tgt)


def lean_path(src, tgt, limit=10 ** 4):
    """Iterate the Lean cases from src until tgt (None: the halt): (reached, steps)."""
    p, tot = src, 0
    for _ in range(limit):
        nx, k, _ = lean_next(p)
        tot += k
        if nx is None: return None, tot
        p = nx
        if p == tgt: return p, tot
    return '?', tot


def check_cases(R):
    """Every Lean case on a grid: Lean's step count equals py/phasemap.py's, and the machine agrees."""
    bad = n = 0
    used = set()
    for kind, ar in (('e', 2), (START[0][0], 2), ('q', 3)):
        for vals in itertools.product(range(R), repeat=ar):
            p = (kind,) + vals
            nx, k, i = lean_next(p)
            used.add(i)
            pm = PM.nxt(p)
            n += 1
            if (pm is None) != (nx is None) or pm is not None and pm != (nx, k) or not agrees(p, nx, k):
                bad += 1
                if bad < 10: print('case differs:', p, (nx, k), pm)
    print(f'cases: {len(CASES)} Lean cases ({len(used)} met), {n} phases (variables < {R}), {bad} failures')
    return bad


def check_rows(R, K):
    bad = n = 0
    for name, vs, src, tgt, steps in ROWS:
        names = vs.split()
        for vals in itertools.product(*[range(1, K + 1) if v == 'b' else range(R) for v in names]):
            env = dict(zip(names, vals))
            if not COND.get(name, lambda **e: True)(**env): continue
            s, t, k = src(*vals), tgt(*vals), steps(*vals)
            n += 1
            if not (agrees(s, t, k) and lean_path(s, t) == (t, k)):
                bad += 1
                if bad < 10: print('row differs:', name, vals, s, t, k, lean_path(s, t))
    cells, pos, st = [0], 0, 0
    if PM.simulate(cells, pos, st, START[1]) != tape(START[0]):
        bad += 1; print('start differs')
    print(f'rows: {len(ROWS)} rows and the start, {n} instances (variables < {R}), {bad} failures')
    return bad


def check_run(STEPS):
    """The machine from blank tape against the Lean map from its start, at every phase of the first STEPS steps."""
    T = PM.T
    size = 4 * int(STEPS ** 0.5) + 2000
    tp = bytearray(2 * size); off = size; p = off; st = 0
    ph, due, nph, bad = START[0], START[1], 0, 0
    lo = hi = p
    if due == 0:
        nph += 1; nx, k, _ = lean_next(ph); ph, due = nx, k
    for n in range(1, STEPS + 1):
        t = T[(st, tp[p])]
        if t is None: print('the machine halted at', n); bad += 1; break
        tp[p] = t[0]; p += t[1]; st = t[2]
        if p < lo: lo = p
        if p > hi: hi = p
        while n == due:
            a = lo
            while a < p and not tp[a]: a += 1
            b = hi
            while b > p and not tp[b]: b -= 1
            cells, q, s = tape(ph)
            if (tuple(tp[a:b + 1]), p - a, st) != (tuple(cells), q, s):
                bad += 1; print('run differs at step', n, ph); break
            nph += 1
            nx, k, _ = lean_next(ph)
            if nx is None: print('the map halts at', ph); bad += 1; break
            ph, due = nx, n + k
        if bad: break
    print(f'run: {nph} phases in the first {STEPS} steps from blank tape, tapes and step counts agree: '
          f'{"yes" if not bad else "NO"}')
    return bad


def check_example():
    ks = [lean_path(a, b)[1] for a, b in zip(EXAMPLE[:-1], EXAMPLE[1:])]
    ok = all(lean_path(a, b)[0] == b for a, b in zip(EXAMPLE[:-1], EXAMPLE[1:])) and ks == EXAMPLE_STEPS
    cells, pos, st = PM.build(EXAMPLE[0])
    tot = sum(ks)
    direct = PM.simulate(cells, pos, st, tot - 1) is not None and PM.simulate(cells, pos, st, tot) is None
    ok = ok and direct
    print(f'example: {EXAMPLE[0]} halts after {" + ".join(map(str, ks))} = {tot} steps by the rules; '
          f'direct simulation halts at step {tot}: {"yes" if direct else "NO"}; {"ok" if ok else "FAILED"}')
    return 0 if ok else 1


def main():
    if len(sys.argv) > 1 and sys.argv[1] == 'table':
        for (cn, pats, tgt) in CASES:
            pcs = next((c for a, b, c in PIECES if a == cn and b == pats), [])
            print(f"{cn}({', '.join(pats)}) -> {tgt[0] + '(' + ', '.join(tgt[1]) + ')' if tgt else 'HALT'}  "
                  f"{' '.join(pcs)}  [{'; '.join(TH[c.split()[0]][1] for c in pcs if c != 'ROUNDS') or 'pc_round: ' + TH['pc_round'][1] if tgt else ''}]")
        return 0
    bad = check_cases(int(os.environ.get('R', 9)))
    bad += check_rows(int(os.environ.get('R', 9)) + 3, 6)
    bad += check_example()
    bad += check_run(int(float(os.environ.get('STEPS', 3e7))))
    return 1 if bad else 0


ROWS = [
    ('left phase', 'x z', lambda x, z: ('e', x, z + 2 * x + 7), lambda x, z: ('e', 2 * x + 4, z + 1),
     lambda x, z: 4 * x * x + 24 * x + 30),
    ('right phase', 's y', lambda s, y: ('a', s + (y + 1) // 2 + 2, y), lambda s, y: ('a', s, 2 * y + 6),
     lambda s, y: y * y + (6 * y + 12 if y % 2 == 0 else 8 * y + 16)),
    ('enter', 'x z', lambda x, z: ('e', x, z + 2), lambda x, z: ('q', x, 0, z), lambda x, z: 2 * x + 3),
    ('bounces', 'm j t', lambda m, j, t: ('q', m + 1, j, t + 3),
     lambda m, j, t: ('q', m + 1 - min(m + 1, (t + 2) // 2), j + min(m + 1, (t + 2) // 2), t + 3 - 2 * min(m + 1, (t + 2) // 2)),
     lambda m, j, t: (lambda b: 8 * b * j + 4 * b * b + 6 * b)(min(m + 1, (t + 2) // 2))),
    ('left end', 'j t', lambda j, t: ('q', 0, j, t + 5), lambda j, t: ('e', 2 * j + 4, t + 1), lambda j, t: 16 * j + 27),
    ('turn right', 'j', lambda j: ('q', 0, j, 4), lambda j: ('a', 0, 4 * j + 9), lambda j: 12 * j + 19),
    ('turn right', 'j', lambda j: ('q', 0, j, 3), lambda j: ('a', 0, 4 * j + 7), lambda j: 12 * j + 17),
    ('turn right', 'm j', lambda m, j: ('q', m, j, 2), lambda m, j: ('a', m, 4 * j + 6), lambda m, j: 4 * j + 5),
    ('turn right', 'm j', lambda m, j: ('q', m, j, 1), lambda m, j: ('a', m, 4 * j + 4), lambda m, j: 4 * j + 3),
    ('no 1s left', 'm j', lambda m, j: ('q', m + 2, j, 0), lambda m, j: ('q', m, 0, 4 * j + 4), lambda m, j: 8 * j + 10),
    ('no 1s left', 'j', lambda j: ('q', 1, j, 0), lambda j: ('e', 2, 4 * j + 2), lambda j: 8 * j + 19),
    ('no 1s left', '', lambda: ('q', 0, 0, 0), lambda: ('a', 0, 7), lambda: 21),
    ('no 1s left', 'j', lambda j: ('q', 0, j + 1, 0), lambda j: ('e', 3, 4 * j + 4), lambda j: 8 * j + 35),
    ('to the bounces', 'x y', lambda x, y: ('a', x + 2, y), lambda x, y: ('q', x, 0, y + 2), lambda x, y: y + 7),
    ('one 10', '', lambda: ('a', 1, 0), lambda: ('a', 0, 5), lambda: 12),
    ('one 10', 'y', lambda y: ('a', 1, y + 1), lambda y: ('e', 2, y + 1), lambda y: y + 17),
    ('all ones', '', lambda: ('a', 0, 0), lambda: ('a', 0, 4), lambda: 8),
    ('all ones', '', lambda: ('a', 0, 1), lambda: ('e', 3, 3), lambda: 46),
    ('all ones', '', lambda: ('a', 0, 2), lambda: ('a', 0, 7), lambda: 20),
    ('all ones', 'y', lambda y: ('a', 0, y + 3), lambda y: ('e', 3, y + 1), lambda y: y + 27),
    ('halt', 'x', lambda x: ('e', x, 0), lambda x: None, lambda x: 2 * x + 2),
    ('halt', 'x', lambda x: ('e', x, 1), lambda x: None, lambda x: 2 * x + 4),
]
COND = {}
EXAMPLE = [('a', 0, 15), ('e', 3, 13), ('e', 10, 1), None]
EXAMPLE_STEPS = [39, 138, 24]

if __name__ == '__main__':
    sys.exit(main())
