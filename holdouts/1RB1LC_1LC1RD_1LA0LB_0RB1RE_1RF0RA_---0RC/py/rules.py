"""rules.py: the bbchallenge wiki's map A(a, b) of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC with exact step counts, against
the Lean frame map and the machine.

    python3 py/rules.py            # all checks below; exit status 1 on any failure
    python3 py/rules.py table      # the Lean cases with their step counts, read from the Lean files

    A(a, b) := 0^inf 1^a 0 C> 1^b 0^inf      (a >= 1; a visit is any moment the tape has this form)

`op` is the wiki's rule list (page "1RB1LC 1LC1RD 1LA0LB 0RB1RE 1RF0RA ---0RC", analysis by Racheline) and `op_steps`
the number of machine steps of each rule (fitted here, then checked).  The Lean map `next` of lean/Phases.lean, with the
step count of each case from its piece theorems in lean/Pieces.lean, is read from the Lean files.  A(a, b) is the
Lean frame b(a - 2, 1, b - 1) three steps earlier (a >= 2), or d(0, 2, b - 1) five steps earlier (a = 1).

  cases   every Lean case on a grid of frames: the machine run exactly the case's step count lands on the target
          frame (or halts at that step);
  rows    every A(a, b) of a grid in the domain of the rules: direct simulation to the next visit or the halt gives
          op and op_steps, the target is again in the domain, and the Lean cases from the frame of A(a, b) to the next
          frame of the form b(l, 1, r) or d(0, 2, r) give the same target and the same steps;
  run     the run from blank tape: every visit of the first STEPS steps, against op from A(2, 9) (cumulative step
          counts equal) and against the Lean map from e(1, 0) (the visits are exactly its frames b(l, 1, r) and
          d(0, 2, r), 3 and 5 steps earlier);
  lean    further: the Lean map from e(1, 0) for FRAMES frames, every visit against the rules.
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




# ---- The wiki's map on A(a, b), with the number of machine steps of each rule ----

def in_domain(a, b):
    return a >= 1 and b >= 2 and (a, b) not in ((1, 2), (1, 3), (2, 2), (3, 2))


def op(a, b):
    """The next visit after A(a, b), or None for the halt (the rules of the wiki page, with their conditions)."""
    if b == 3: return None                                   # a >= 2
    if b == 2: return (a - 3, 7)                             # a >= 4
    if b >= a + 3 and a % 2 == 0: return (2 * a + 4, b - a - 1)
    if b >= a + 4: return (2 * a + 3, b - a)                 # a odd
    if b == a + 3: return (2 * a + 1, 9)                     # a odd
    if b == a + 2: return (1, 2 * a + 7)                     # a >= 2
    if b == a + 1: return (4, 2 * a + 4)                     # a >= 3
    return (a - b + 1, 2 * b + 3)                            # a >= b >= 4


def op_steps(a, b):
    """Machine steps from A(a, b) to the next visit (the halt: up to and including the halting step)."""
    if b == 3: return 11
    if b == 2: return 25
    if b >= a + 3 and a % 2 == 0: return 2 * a * a + 12 * a - 1
    if b >= a + 4: return 2 * a * a + 12 * a + 13
    if b == a + 3: return 2 * a * a + 12 * a + 39
    if b == a + 2: return 2 * a * a + 9 * a + 23
    if b == a + 1: return 2 * a * a + 5 * a + 7
    return 2 * b * b + b + 5


START, START_STEPS = (2, 9), 52


def is_visit(tape, p, st, lo, hi):
    """(a, b) if the tape (a dict or bytearray, cells lo..hi) is 0^inf 1^a 0 C> 1^b 0^inf with a >= 1."""
    if st != 2 or not tape[p] or tape[p - 1]: return None
    i = p
    while tape[i]: i += 1
    if any(tape[k] for k in range(i, hi + 1)): return None
    k = p - 2
    while tape[k]: k -= 1
    if k == p - 2 or any(tape[q] for q in range(lo, k + 1)): return None
    return (p - 2 - k, i - p)


def sim_A(a, b, limit=10 ** 6):
    """Direct simulation from A(a, b) to the next visit: ((a', b') or 'halt', steps)."""
    n0 = a + b + 4
    size = n0 + 2 * limit // max(1, n0) + 4000
    tape = bytearray(2 * size); off = size // 2
    for i in range(a): tape[off + i] = 1
    for i in range(b): tape[off + a + 1 + i] = 1
    p, st, lo, hi = off + a + 1, 2, off - 1, off + a + b + 1
    for n in range(1, limit):
        t = F.T[(st, tape[p])]
        if t is None: return 'halt', n
        tape[p] = t[0]; p += t[1]; st = t[2]
        if p < lo: lo = p
        if p > hi: hi = p
        v = is_visit(tape, p, st, lo, hi) if st == 2 else None
        if v: return v, n
    return '?', limit


def frame_of(a, b):
    """The Lean frame that follows A(a, b), and how many steps later."""
    return (('b', (a - 2, 1, b - 1)), 3) if a >= 2 else (('d', (0, 2, b - 1)), 5)


def visit_of(fr):
    """The visit A(a, b) that a Lean frame follows, and how many steps earlier (None if it follows none)."""
    n, v = fr
    if n == 'b' and v[1] == 1: return (v[0] + 2, v[2] + 1), 3
    if n == 'd' and v[0] == 0 and v[1] == 2: return (1, v[2] + 1), 5
    return None


def lean_A(a, b, limit=10 ** 5):
    """The Lean cases from the frame of A(a, b) to the next frame that follows a visit: (visit or None, steps)."""
    fr, tot = frame_of(a, b)
    for _ in range(limit):
        nx, k, _ = lean_next(fr)
        tot += k
        if nx is None: return None, tot
        fr = nx
        w = visit_of(fr)
        if w: return w[0], tot - w[1]
    return '?', tot


def check_rows(R):
    bad = n = 0
    for a in range(1, R):
        for b in range(2, R):
            if not in_domain(a, b): continue
            r, k = sim_A(a, b)
            t, s = op(a, b), op_steps(a, b)
            ok = (r == 'halt' and t is None or r == t) and k == s and (t is None or in_domain(*t)) \
                and lean_A(a, b) == (t, s)
            n += 1
            if not ok:
                bad += 1
                if bad < 10: print('differs at', (a, b), 'machine', r, k, 'rules', t, s, 'Lean', lean_A(a, b))
    # the start: blank tape to A(2, 9), the first visit
    tape = bytearray(400); p = 200; st = 0; lo = hi = p; first = None
    for m in range(1, 200):
        t = F.T[(st, tape[p])]; tape[p] = t[0]; p += t[1]; st = t[2]; lo = min(lo, p); hi = max(hi, p)
        v = is_visit(tape, p, st, lo, hi)
        if v: first = (v, m); break
    if first != (START, START_STEPS): bad += 1; print('start differs', first)
    print(f'rows: {n} visits A(a, b) (a, b < {R}) and the start, {bad} failures')
    return bad


def check_run(STEPS):
    T = F.T
    size = 4 * int(STEPS ** 0.5) + 2000
    tape = bytearray(2 * size); p = size; st = 0; lo = hi = p
    s, acc, nv, bad = None, None, 0, 0
    # the Lean map from e(1, 0) (step 1): the times at which it says a visit happens
    fr, due, lean_visits = ('e', (1, 0)), 1, []
    while due <= STEPS + 10:
        w = visit_of(fr)
        if w: lean_visits.append((due - w[1], w[0]))
        nx, k, _ = lean_next(fr)
        if nx is None: break
        fr, due = nx, due + k
    seen = []
    for n in range(1, STEPS + 1):
        t = T[(st, tape[p])]
        if t is None: print('the machine halted at', n); bad += 1; break
        tape[p] = t[0]; p += t[1]; st = t[2]
        if p < lo: lo = p
        if p > hi: hi = p
        if st == 2 and tape[p] and not tape[p - 1]:
            v = is_visit(tape, p, st, lo, hi)
            if not v: continue
            seen.append((n, v))
            if s is None:
                s, acc = v, n
                if (v, n) != (START, START_STEPS): bad += 1
                continue
            acc += op_steps(*s); s = op(*s)
            nv += 1
            if s != v or acc != n:
                bad += 1; print('run differs at step', n, v, s, acc); s, acc = v, n
    lean = [x for x in lean_visits if x[0] <= STEPS]
    if lean != seen: bad += 1; print('the Lean map gives other visits', len(lean), len(seen))
    print(f'run: {len(seen)} visits in the first {STEPS} steps from blank tape; the rules from A(2, 9) and the Lean map '
          f'from e(1, 0) give the same visits and step counts: {"yes" if not bad else "NO"}')
    return bad


def check_lean_long(FRAMES):
    """Further than direct simulation goes: the Lean map from e(1, 0) for FRAMES frames against the rules."""
    fr, due, s, acc, nv, bad = ('e', (1, 0)), 1, None, None, 0, 0
    for _ in range(FRAMES):
        w = visit_of(fr)
        if w:
            v, n = w[0], due - w[1]
            if s is None: s, acc = v, n
            else:
                acc += op_steps(*s); s = op(*s); nv += 1
                if (s, acc) != (v, n): bad += 1; print('Lean map and rules differ at', fr, due); break
        nx, k, _ = lean_next(fr)
        if nx is None: bad += 1; print('the Lean map halts at', fr); break
        fr, due = nx, due + k
    print(f'lean: {FRAMES} frames of the Lean map ({due} steps), {nv + 1} visits, the same as the rules: '
          f'{"yes" if not bad else "NO"}')
    return bad


def check_example():
    """The worked example of the page."""
    path, s, tot = [], EXAMPLE, 0
    while s is not None:
        k = op_steps(*s); path.append(k); tot += k; s = op(*s)
    ok = path == EXAMPLE_STEPS and sim_total(EXAMPLE) == tot
    print(f'example: A{EXAMPLE} halts after {" + ".join(map(str, path))} = {tot} steps by the rules; direct simulation: '
          f'{sim_total(EXAMPLE)}; {"ok" if ok else "FAILED"}')
    return 0 if ok else 1


def sim_total(v, limit=10 ** 6):
    """Direct simulation from A(a, b) until the halt: the number of steps."""
    a, b = v
    tape = {i: 1 for i in range(a)}
    tape.update({a + 1 + i: 1 for i in range(b)})
    p, st = a + 1, 2
    for n in range(1, limit):
        t = F.T[(st, tape.get(p, 0))]
        if t is None: return n
        tape[p] = t[0]; p += t[1]; st = t[2]
    return None


EXAMPLE = (1, 7)
EXAMPLE_STEPS = [27, 82, 79, 176, 79, 431, 11]


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'table':
        for n, pats, tgt, st, pcs in CASES:
            print(f"{n}({', '.join(pats)}) -> {tgt[0] + '(' + ', '.join(tgt[1]) + ')' if tgt else 'HALT'}  [{st}]  {' '.join(pcs)}")
        sys.exit(0)
    bad = check_cases(int(os.environ.get('R', 9)))
    bad += check_rows(int(os.environ.get('R', 60)))
    bad += check_example()
    bad += check_run(int(float(os.environ.get('STEPS', 1e7))))
    bad += check_lean_long(int(float(os.environ.get('FRAMES', 5e5))))
    sys.exit(1 if bad else 0)
