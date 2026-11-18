"""rules.py: the bbchallenge wiki's map B(x, y) of 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE with exact step counts, against
the Lean frame map and the machine.

    python3 py/rules.py            # all checks below; exit status 1 on any failure
    python3 py/rules.py table      # the Lean cases with their step counts, read from the Lean files

    B(x, y) := 0^inf 1^(2x) F> 1^y 0^inf      (x >= 1; B(1, 1) is outside the rules and no rule leads to it)

`op` is the wiki's rule list (page "1RB1RF 0LC0RF 1RD1LC ---0LE 0RC1LF 1RA0LE", B(x, y) = A(0, 2x, y)) and `op_steps`
the number of machine steps of each rule (fitted here, then checked): from B(x, y) to the first moment the tape is the
rule's target, or to the halt.  Two rules pass another tape of the family on the way (B(x, 1) -> B(4, 2x - 4) passes
B(x - 1, 2), and B(x, 2x - 1) -> B(2, 4x - 2) passes B(2x - 1, 0)); the wiki does not count those, and neither do we.
The Lean map `next` of lean/Phases.lean, with the step count of each case from its piece theorems in lean/Pieces.lean,
is read from the Lean files.  B(x, y) is the same tape as the Lean frame f(x, y); the frames f(x, 0) are never reached
as frames (the head does not turn there), so a rule into B(x, 0) shows in the Lean map only together with the next one.

  cases   every Lean case on a grid of frames: the machine run exactly the case's step count lands on the target
          frame (or halts at that step);
  rows    every B(x, y) of a grid: direct simulation to the rule's target (or the halt) takes op_steps steps and meets
          no other tape of the family except the one named above; and the Lean cases from f(x, y) to the next frame
          f(.., ..) give the same target and steps (through B(x', 0), two rules at once);
  run     the run from blank tape: every tape of the family in the first STEPS steps, against op from B(1, 0) (step 8;
          cumulative step counts equal), and against the Lean map from g(0, 1) (its frames f are the visits with y > 0);
  lean    further: the Lean map from g(0, 1) for FRAMES frames, its frames f against the rules.
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






# ---- The wiki's map on B(x, y), with the number of machine steps of each rule ----

def op(x, y):
    """The wiki's next B after B(x, y) (x >= 1), or None for the halt."""
    if y % 2 == 0:
        h = y // 2
        if x >= h: return (2 * h + 2, 2 * x - 2 * h)
        if x < h - 1: return (2 * x + 2, 2 * h - 2 * x - 3)
        return (2 * x + 1, 0)                                    # y = 2x + 2
    h = (y - 1) // 2
    if x > h + 1: return (2 * h + 4, 2 * x - 2 * h - 4)
    if x == h + 1: return (2, 4 * x - 2)                         # y = 2x - 1, x >= 2
    if x < h: return (2 * x + 2, 2 * h - 2 * x - 2)
    return None                                                  # y = 2x + 1


def op_steps(x, y):
    """Machine steps of the rule from B(x, y) (the halt: up to and including the halting step)."""
    if y % 2 == 0:
        h = y // 2
        if x >= h: return 4 * x * h - 2 * h * h + 2 * x + 16 * h + 12
        if x < h - 1: return 2 * x * x + 10 * x + 9
        return 2 * x * x + 10 * x + 7
    h = (y - 1) // 2
    if x > h + 1: return 4 * x * h - 2 * h * h + 6 * x + 12 * h + 22
    if x == h + 1: return 2 * x * x + 14 * x + 7
    if x < h: return 2 * x * x + 10 * x + 9
    return 2 * x * x + 10 * x + 4


def passes(x, y):
    """The tape of the family that the rule from B(x, y) passes on the way, if any."""
    if y == 1 and x >= 2: return (x - 1, 2)
    if y == 2 * x - 1: return (2 * x - 1, 0)
    return None


START, START_STEPS = (1, 0), 8


def is_visit(tape, p, st, lo, hi):
    """(x, y) if the tape is 0^inf 1^(2x) F> 1^y 0^inf (x >= 0)."""
    if st != 5: return None
    i = p
    while tape[i]: i += 1
    if any(tape[k] for k in range(i, hi + 1)): return None
    k = p - 1
    while tape[k]: k -= 1
    if (p - 1 - k) % 2 or any(tape[q] for q in range(lo, k + 1)): return None
    return ((p - 1 - k) // 2, i - p)


def sim_B(x, y, target, limit=10 ** 6):
    """Direct simulation from B(x, y) to the tape B(target) or the halt: (reached, steps, tapes of the family met)."""
    n0 = 2 * x + y + 4
    size = n0 + 4000
    tape = bytearray(2 * size); off = size // 2
    for i in range(2 * x + y): tape[off + i] = 1
    p, st, lo, hi = off + 2 * x, 5, off - 1, off + 2 * x + y
    met = []
    for n in range(1, limit):
        t = F.T[(st, tape[p])]
        if t is None: return 'halt', n, met
        tape[p] = t[0]; p += t[1]; st = t[2]
        if p < lo: lo = p
        if p > hi: hi = p
        if st == 5:
            v = is_visit(tape, p, st, lo, hi)
            if v and v == target: return v, n, met
            if v: met.append(v)
    return '?', limit, met


def lean_B(x, y, limit=10 ** 5):
    """The Lean cases from f(x, y) to the next frame f: (its (x, y) or None, steps)."""
    fr, tot = ('f', (x, y)), 0
    for _ in range(limit):
        nx, k, _ = lean_next(fr)
        tot += k
        if nx is None: return None, tot
        fr = nx
        if fr[0] == 'f': return fr[1], tot
    return '?', tot


def check_rows(R):
    bad = n = 0
    for x in range(1, R):
        for y in range(0, R):
            if (x, y) == (1, 1): continue          # outside the rules, and never reached
            t, s = op(x, y), op_steps(x, y)
            if t is not None and (t == (1, 1) or t[0] < 1 or t[1] < 0): bad += 1; print('target outside', x, y)
            r, k, met = sim_B(x, y, t)
            ok = (r == 'halt' and t is None or r == t) and k == s
            pv = passes(x, y)
            ok = ok and met == ([pv] if pv else [])
            want = (t, s) if t is None or t[1] > 0 else (op(*t), s + op_steps(*t))
            ok = ok and lean_B(x, y) == want
            n += 1
            if not ok:
                bad += 1
                if bad < 10: print('differs at', (x, y), 'machine', r, k, met, 'rules', t, s, 'Lean', lean_B(x, y))
    tape = bytearray(400); p = 200; st = 0; lo = hi = p; first = None
    for m in range(1, 200):
        t = F.T[(st, tape[p])]; tape[p] = t[0]; p += t[1]; st = t[2]; lo = min(lo, p); hi = max(hi, p)
        v = is_visit(tape, p, st, lo, hi)
        if v: first = (v, m); break
    if first != (START, START_STEPS): bad += 1; print('start differs', first)
    print(f'rows: {n} tapes B(x, y) (x, y < {R}) and the start, {bad} failures')
    return bad


def check_run(STEPS):
    T = F.T
    size = 4 * int(STEPS ** 0.5) + 2000
    tape = bytearray(2 * size); p = size; st = 0; lo = hi = p
    fr, due, lean_f = ('g', (0, 1)), 6, []
    while due <= STEPS:
        if fr[0] == 'f': lean_f.append((due, fr[1]))
        nx, k, _ = lean_next(fr)
        if nx is None: break
        fr, due = nx, due + k
    seen, bad = [], 0
    for n in range(1, STEPS + 1):
        t = T[(st, tape[p])]
        if t is None: print('the machine halted at', n); bad += 1; break
        tape[p] = t[0]; p += t[1]; st = t[2]
        if p < lo: lo = p
        if p > hi: hi = p
        if st == 5:
            v = is_visit(tape, p, st, lo, hi)
            if v: seen.append((n, v))
    # the rules' orbit, with the passed tapes in between
    want, s, acc = [], START, START_STEPS
    while acc <= STEPS:
        want.append((acc, s))
        pv = passes(*s)
        if pv: want.append((None, pv))
        acc += op_steps(*s); s = op(*s)
    got = [(n if v not in [w for m, w in want if m is None] else None, v) for n, v in seen]
    if [(m, v) for m, v in want if m is None or m <= STEPS] != got: bad += 1; print('run differs')
    vis = [(m, v) for m, v in want if m is not None and v[1] > 0]
    if vis != lean_f: bad += 1; print('the Lean map gives other frames f', len(vis), len(lean_f))
    nv = sum(1 for m, v in want if m is not None)
    print(f'run: {nv} visits in the first {STEPS} steps from blank tape; the rules from B(1, 0) give them with the same '
          f'step counts, and the Lean map from g(0, 1) the same frames f: {"yes" if not bad else "NO"}')
    return bad


def check_lean_long(FRAMES):
    """Further than direct simulation goes: the Lean map from g(0, 1) for FRAMES frames against the rules."""
    fr, due, nf, bad = ('g', (0, 1)), 6, 0, 0
    s, acc = START, START_STEPS
    for _ in range(FRAMES):
        if fr[0] == 'f':
            acc += op_steps(*s); s = op(*s)
            while s[1] == 0:
                acc += op_steps(*s); s = op(*s)
            if (s, acc) != (fr[1], due): bad += 1; print('Lean map and rules differ at', fr, due, s, acc); break
            nf += 1
        nx, k, _ = lean_next(fr)
        if nx is None: bad += 1; print('the Lean map halts at', fr); break
        fr, due = nx, due + k
    print(f'lean: {FRAMES} frames of the Lean map ({due} steps), {nf} frames f, the same as the rules: '
          f'{"yes" if not bad else "NO"}')
    return bad


def sim_total(v, limit=10 ** 6):
    """Direct simulation from B(x, y) until the halt: the number of steps."""
    x, y = v
    tape = {i: 1 for i in range(2 * x + y)}
    p, st = 2 * x, 5
    for n in range(1, limit):
        t = F.T[(st, tape.get(p, 0))]
        if t is None: return n
        tape[p] = t[0]; p += t[1]; st = t[2]
    return None


def check_example():
    """The worked example of the page."""
    path, s, tot = [], EXAMPLE, 0
    while s is not None:
        k = op_steps(*s); path.append(k); tot += k; s = op(*s)
    ok = path == EXAMPLE_STEPS and sim_total(EXAMPLE) == tot
    print(f'example: B{EXAMPLE} halts after {" + ".join(map(str, path))} = {tot} steps by the rules; direct simulation: '
          f'{sim_total(EXAMPLE)}; {"ok" if ok else "FAILED"}')
    return 0 if ok else 1


EXAMPLE = (1, 16)
EXAMPLE_STEPS = [21, 81, 32, 37, 136]


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'table':
        for n, pats, tgt, st, pcs in CASES:
            print(f"{n}({', '.join(pats)}) -> {tgt[0] + '(' + ', '.join(tgt[1]) + ')' if tgt else 'HALT'}  [{st}]  {' '.join(pcs)}")
        sys.exit(0)
    bad = check_cases(int(os.environ.get('R', 8)))
    bad += check_rows(int(os.environ.get('R', 50)))
    bad += check_example()
    bad += check_run(int(float(os.environ.get('STEPS', 1e7))))
    bad += check_lean_long(int(float(os.environ.get('FRAMES', 5e5))))
    sys.exit(1 if bad else 0)
