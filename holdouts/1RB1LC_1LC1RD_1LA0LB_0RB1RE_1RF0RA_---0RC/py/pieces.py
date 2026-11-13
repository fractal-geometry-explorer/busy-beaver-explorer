"""Generate lean/Pieces.lean and lean/Phases.lean for the frame map of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC.

The map is fitted from the machine (`fitlib.py`, frames in `spec.py`), collapsed into a decision tree of patterns
(`tree.py`), and every leaf is proved by one symbolic run (`tools/py/bbtools/symtm.py`; a leaf whose frame falls
inside a shift rule is proved as two runs, the second by single steps).  A run that needs to know whether a count
is 0 splits that leaf further.

usage (from the repository root):  python3 holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC/py/pieces.py
"""
import sys, importlib, os
import re as _re
BINDERS = {}
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'tools', 'py'))
from bbtools.symtm import Config, Halted, prove, rules_file, run
from bbtools.machine import Machine
import bbtools.symtm as _S
_canon0 = _S.canon
def _prim(w):
    for d in range(1, len(w) + 1):
        if len(w) % d == 0 and w[:d] * (len(w) // d) == w: return w[:d], len(w) // d
def _canon(seq):
    out = []
    for t in seq:
        if isinstance(t, _S.Rep):
            u, k = _prim(tuple(t.word)); out.append(_S.Rep(u, k * t.n) if k > 1 else t)
        else: out.append(t)
    while len(out) >= 2 and out[0] == _S.Blank() and out[1] == 0: out.pop(1)
    while len(out) >= 2 and out[-1] == _S.Blank() and out[-2] == 0: out.pop(-2)
    return _canon0(out)
_S.canon = _canon
from fitlib import Fit
from tree import Tree

import spec
NS = spec.NS; T = spec.T; W = spec.W; K = spec.K
OUT = os.path.join(HERE, '..', 'lean')
M = spec.M; FR = spec.FR
fit = Fit(M, FR, T, W, 1, spec.TURNS, False)
assert not fit.bad, fit.bad
leaves = Tree(fit).all()
B = {'0': 'false', '1': 'true'}

def toks(n): return FR[n].split()
def vars_of(n): return [t.split('^')[1] for t in toks(n) if '^' in t]
def head_of(n): return next(t for t in toks(n) if t in 'ABCDEF')
LV = {}  # Lean var names per frame var
def lv(v): return v.lower() if v.lower() not in ('a', 'b', 'c') else v.lower() + 'v'

def sym_string(n, exprs):
    """symtm config string of frame n with var -> expression string."""
    out = ['0^inf']
    for t in toks(n):
        if '^' in t:
            u, v = t.split('^'); e = exprs[v]
            if e.isdigit(): out.extend(list(u * int(e)))
            else: out.append(f'({u})^{e}')
        elif t in 'ABCDEF': out.append(t + '>')
        else: out.extend(list(t))
    out.append('0^inf'); return ' '.join(out)

def lean_cfg(n):
    tk = toks(n); i = tk.index(head_of(n)); left, right = tk[:i], tk[i + 1:]
    def side(ts, rev):
        acc = 'blank'
        seq = ts if rev else list(reversed(ts))   # build from the far end inwards
        for t in seq:
            if '^' in t:
                u, v = t.split('^'); w = u[::-1] if rev else u
                acc = f'rep {lv(v)} [{", ".join(B[c] for c in w)}] ({acc})'
            else:
                cells = t[::-1] if rev else t
                for c in (cells if rev else reversed(cells)): acc = f'cons {B[c]} ({acc})'
        return acc
    # left tape: nearest cell first; build from far left (first token) inwards
    accl = 'blank'
    for t in left:
        if '^' in t:
            u, v = t.split('^'); accl = f'rep {lv(v)} [{", ".join(B[c] for c in u[::-1])}] ({accl})'
        else:
            for c in t: accl = f'cons {B[c]} ({accl})'
    accr = 'blank'
    for t in reversed(right):
        if '^' in t:
            u, v = t.split('^'); accr = f'rep {lv(v)} [{", ".join(B[c] for c in u)}] ({accr})'
        else:
            for c in reversed(t): accr = f'cons {B[c]} ({accr})'
    return f'⟨{accl}, {accr}, .{head_of(n)}⟩'

def sub_expr(fml, region, names):
    """affine formula in the frame's vars -> (const, {leanvar: coef}) after x_i = v_i + s_i or k."""
    c0, co = fml; c0 = Fraction(c0); out = {}
    for i, c in co.items():
        kind, s = region[i]
        if kind == 'eq': c0 += c * s
        else: c0 += c * s; out[names[i]] = out.get(names[i], 0) + Fraction(c)
    out = {k: v for k, v in out.items() if v}
    assert c0.denominator == 1 and c0 >= 0 and all(c.denominator == 1 and c > 0 for c in out.values()), (fml, region)
    return int(c0), {k: int(v) for k, v in out.items() if v}
def lean_e(e):
    c0, co = e; parts = [(f'{c} * {v}' if c != 1 else v) for v, c in co.items()]
    if c0 or not parts: parts.append(str(c0))
    return ' + '.join(parts)
def sym_e(e):
    c0, co = e; parts = [(f'{c}*{v}' if c != 1 else v) for v, c in co.items()]
    if c0 or not parts: parts.append(str(c0))
    return '+'.join(parts)

m = Machine.parse(M)
def surely_nonneg(l): return l.k >= 0 and all(a >= 0 for a in l.c.values())
def find_mid(start, target):
    """Advance as run() does, and return the last configuration before the first move that may overshoot target."""
    cur = Config.parse(start)
    for _ in range(100000):
        nxt = cur.copy()
        x = _S.try_cross(m, nxt)
        if x is None:
            c2 = nxt.copy(); rot = _S.try_rotate(c2)
            if rot is not None and _S.try_cross(m, c2) is not None: nxt = c2
            else: _S.step(m, nxt)
        if not surely_nonneg(target - nxt.steps): return cur
        cur = nxt
    raise RuntimeError('no overshoot found')
pieces = []; arms = []
def do_leaf(n, region, kd, fs, fst, tag, depth=0):
    vs = vars_of(n); names = [lv(v) for v in vs]
    pat = []; sexpr = {}
    for (kind, s), v, nm in zip(region, vs, names):
        if kind == 'eq': pat.append(str(s)); sexpr[v] = str(s)
        else: pat.append(nm if s == 0 else f'({nm} + {s})'); sexpr[v] = nm if s == 0 else f'{nm}+{s}'
    start = sym_string(n, sexpr); pname = f'pc_{n}{tag}'
    argv = sorted(set(nm for (kind, s), nm in zip(region, names) if kind == 'ge'))
    lpat = f'.{n} ' + ' '.join(pat)
    try:
        if kd == 'HALT':
            c = Config.parse(start)
            try: run(m, c, lambda c: False, max_moves=100000, rotate=True)
            except Halted: pass
            th, fin = prove(M, pname, start, repr(c), doc=f'{n}({", ".join(pat)}) runs into the halting transition.', rotate=True)
            pieces.append(th); arms.append((lpat, None, pname, argv)); return
        tgt_vs = vars_of(kd)
        tex = {v: sub_expr(f, region, names) for v, f in zip(tgt_vs, fs)}
        stp = sub_expr(fst, region, names)
        end = sym_string(kd, {v: sym_e(e) for v, e in tex.items()})
        doc = f'{n}({", ".join(pat)}) reaches {kd}({", ".join(lean_e(tex[v]) for v in tgt_vs)}).'
        target = _S.parse_lin(sym_e(stp)); extra = None
        try:
            th, fin = prove(M, pname, start, end, nsteps=target, rotate=True, doc=doc)
        except _S.ProofError:
            if not stp[1]:   # a constant number of steps: run it without shift rules
                th, fin = prove(M, pname, start, end, nsteps=stp[0], cross=False, doc=doc)
            else:
                # the frame is reached inside a shift rule: run to just before it, then single steps
                mid = find_mid(start, target); rem = target - mid.steps
                assert rem.is_const() and rem.k >= 0, (pname, rem)
                th, _ = prove(M, pname, start, repr(mid), nsteps=mid.steps, rotate=True, doc=doc + ' (first part)')
                th2, _ = prove(M, pname + 'z', repr(mid), end, nsteps=rem.k, cross=False, doc=doc + ' (second part)')
                extra = th2
    except (_S.ProofError, _S.NeedSplit) as e:
        msg = str(e) if isinstance(e, _S.ProofError) else 'NeedSplit: ' + str(e)
        assert 'NeedSplit' in msg and depth < 5, (pname, msg[:300])
        rep = msg.split('NeedSplit: ')[1]; cnt = rep.split('^')[1]
        i = next(k for k, nm in enumerate(names) if nm in _S.parse_lin(cnt).c and region[k][0] == 'ge')
        kind, s0 = region[i]
        r1 = list(region); r1[i] = ('eq', s0); r2 = list(region); r2[i] = ('ge', s0 + 1)
        print('  split', pname, 'on', names[i], file=sys.stderr)
        do_leaf(n, tuple(r1), kd, fs, fst, tag + 'a', depth + 1); do_leaf(n, tuple(r2), kd, fs, fst, tag + 'b', depth + 1)
        return
    pieces.append(th)
    if extra:
        pieces.append(extra)
        av2 = sorted(set(_S.Config.parse(end).vars()) | set(nm for nm in argv if nm in extra.split(':')[0]))
        arms.append((lpat, f'.{kd} ' + ' '.join(f'({lean_e(tex[v])})' for v in tgt_vs), (pname, pname + 'z'), argv)); return
    arms.append((lpat, f'.{kd} ' + ' '.join(f'({lean_e(tex[v])})' for v in tgt_vs), pname, argv))
    print(pname, start, '->', end, file=sys.stderr)
for n, ls in leaves.items():
    for idx, (region, (kd, fs, fst)) in enumerate(ls): do_leaf(n, region, kd, fs, fst, str(idx))


# first frame of the run from blank tape
F = fit.F; tape = {}; p = 0; st = 0
for k in range(1, 10000):
    t = F.T[(st, tape.get(p, 0))]; tape[p] = t[0]; p += t[1]; st = t[2]
    r = F.match(tape, p, st)
    if r: n0, P0, s0 = r[0], r[1], k; break
start_ph = f'Ph.{n0} ' + ' '.join(str(P0[v]) for v in vars_of(n0))
th_init, _ = prove(M, 'pc_init', '0^inf A> 0^inf', sym_string(n0, {v: str(P0[v]) for v in vars_of(n0)}), nsteps=s0,
                   doc='The run from blank tape reaches the first frame.')
pieces.append(th_init)

for th in pieces:
    hdr = th[th.index('theorem '):].split(':\n')[0]
    nm = hdr.split()[1]; mm = _re.search(r'\(([a-z ]+) : Nat\)', hdr)
    BINDERS[nm] = mm.group(1).split() if mm else []
os.makedirs(OUT, exist_ok=True)
open(os.path.join(OUT, 'Pieces.lean'), 'w').write(rules_file('Machine', NS, pieces,
    f'Pieces of the frame map of {M}, generated by `py/pieces.py`; do not edit.'))
L = []
L.append('import Pieces\nimport Norm\n')
L.append(f'''/-!
# {M}: the frame map

Configurations (blank tape around, `S>` the head in state S on the next cell):
''' + '\n'.join(f'* `{n}`: `{FR[n].replace(" ", " ")}`' for n in FR) + f'''

`next` sends each one to the next frame the machine reaches; `next_sound` proves every case for all parameters
(one symbolic run of `Pieces.lean` each, generated by `py/pieces.py`, glued by `tape_eq`).  Where `next` is `none`
the machine halts (`none_halts`).  The run from blank tape reaches `{start_ph}` after {s0} steps (`init_start`).
So the machine halts from blank tape iff the orbit of `{start_ph}` under `next` reaches a phase where `next` is
`none` (`halts_iff`); `no_halt_phases` checks the first {K} phases by `native_decide`.
-/

namespace {NS}

open TM
''')
for n in FR:
    vs = vars_of(n)
    L.append(f'/-- `{FR[n]}`. -/\ndef Fr{n} ({" ".join(lv(v) for v in vs)} : Nat) : Config := {lean_cfg(n)}\n')
L.append('/-- A frame. -/\ninductive Ph where\n' + '\n'.join(f'  | {n} ({" ".join(lv(v) for v in vars_of(n))} : Nat)' for n in FR)
         + '\n  deriving DecidableEq, Repr\n')
L.append('def Ph.cfg : Ph → Config\n' + '\n'.join(f'  | .{n} {" ".join(lv(v) for v in vars_of(n))} => Fr{n} {" ".join(lv(v) for v in vars_of(n))}' for n in FR) + '\n')
L.append('/-- The frame map. -/\ndef next : Ph → Option Ph\n' + '\n'.join(f'  | {a} => ' + ('none' if b is None else f'some ({b})') for a, b, _, _ in arms) + '\n')
L.append(f'''macro "piece" t:term:max : tactic =>
  `(tactic| focus
    simp only [next, Option.some.injEq] at *
    subst_vars
    simp only [Ph.cfg, {", ".join("Fr" + n for n in FR)}]
    refine ⟨_, ?_, steps_eq_of ($t) (cfg_eq (by tape_eq) (by tape_eq)) (cfg_eq (by tape_eq) (by tape_eq))⟩
    omega)

macro "piece2" t:term:max u:term:max : tactic =>
  `(tactic| focus
    simp only [next, Option.some.injEq] at *
    subst_vars
    simp only [Ph.cfg, {", ".join("Fr" + n for n in FR)}]
    refine ⟨_, ?_, steps_eq_of (steps_seq trans ($t) (steps_eq_of ($u) (cfg_eq (by tape_eq) (by tape_eq)) rfl))
      (cfg_eq (by tape_eq) (by tape_eq)) (cfg_eq (by tape_eq) (by tape_eq))⟩
    omega)

macro "hpiece" t:term:max : tactic =>
  `(tactic| focus
    simp only [Ph.cfg, {", ".join("Fr" + n for n in FR)}]
    exact ⟨_, _, steps_eq_of ($t) (cfg_eq (by tape_eq) (by tape_eq)) rfl, rfl⟩)
''')
import re as _re
def app(pn, argv):
    if isinstance(pn, tuple):
        return ' '.join(app(p, BINDERS[p]) for p in pn)
    return f'({pn} {" ".join(argv)})' if argv else pn
L.append('theorem next_sound : ∀ p p\', next p = some p\' → ∃ n, 0 < n ∧ steps n p.cfg = some p\'.cfg\n' +
         '\n'.join(f'  | {a}, _, h => ' + ('by simp [next] at h' if b is None else (f'by piece2 {app(pn, av)}' if isinstance(pn, tuple) else f'by piece {app(pn, av)}')) for a, b, pn, av in arms) + '\n')
L.append('/-- Where `next` is `none`, the machine halts. -/\ntheorem none_halts : ∀ p, next p = none → TM.Halts trans p.cfg\n' +
         '\n'.join(f'  | {a}, h => ' + (f'by hpiece {app(pn, av)}' if b is None else 'by simp [next] at h') for a, b, pn, av in arms) + '\n')
L.append(f'''/-- `k` steps of the frame map. -/
def iter : Nat → Ph → Option Ph
  | 0, p => some p
  | k + 1, p => (next p).bind (iter k)

theorem reach_iter : ∀ k p p', iter k p = some p' → ∃ n, k ≤ n ∧ steps n p.cfg = some p'.cfg
  | 0, p, p', h => by simp only [iter, Option.some.injEq] at h; subst h; exact ⟨0, Nat.le_refl 0, rfl⟩
  | k + 1, p, p', h => by
    simp only [iter] at h
    cases hp : next p with
    | none => simp [hp] at h
    | some q =>
      simp only [hp, Option.bind_some] at h
      obtain ⟨n1, p1, h1⟩ := next_sound p q hp
      obtain ⟨n2, p2, h2⟩ := reach_iter k q p' h
      exact ⟨n1 + n2, by omega, steps_seq trans h1 h2⟩

theorem iter_succ (k : Nat) (p p' : Ph) (h : iter k p = some p') : iter (k + 1) p = next p' := by
  induction k generalizing p with
  | zero => simp only [iter, Option.some.injEq] at h; subst h; simp [iter]
  | succ k ih =>
    simp only [iter] at h ⊢
    cases hp : next p with
    | none => simp [hp] at h
    | some q => simp only [hp, Option.bind_some] at h ⊢; exact ih q h

/-- The run from blank tape reaches the first frame. -/
theorem init_start : steps {s0} init = some ({start_ph}).cfg := by
  simp only [Ph.cfg, {", ".join("Fr" + n for n in FR)}]
  exact steps_eq_of pc_init (cfg_eq (by tape_eq) (by tape_eq)) (cfg_eq (by tape_eq) (by tape_eq))

/-- **The machine halts from blank tape if and only if the frame map, iterated from `{start_ph}`, reaches a frame
where it is `none`.** -/
theorem halts_iff :
    HaltsFromBlank ↔ ∃ k p, iter k ({start_ph}) = some p ∧ next p = none := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hno
    have hall : ∀ k, ∃ p, iter k ({start_ph}) = some p := by
      intro k
      induction k with
      | zero => exact ⟨_, rfl⟩
      | succ k ih =>
        obtain ⟨p, hp⟩ := ih
        rw [iter_succ k _ p hp]
        cases hn : next p with
        | some q => exact ⟨q, rfl⟩
        | none => exact absurd ⟨k, p, hp, hn⟩ hno
    apply TM.not_halts_of_forall trans _ hh
    apply TM.forall_of_unbounded trans (fun m => ∃ c', steps m init = some c')
    · intro n
      obtain ⟨p, hp⟩ := hall n
      obtain ⟨m, hm, h⟩ := reach_iter n _ p hp
      exact ⟨{s0} + m, by omega, p.cfg, steps_seq trans init_start h⟩
    · exact fun _ h => h
  · rintro ⟨k, p, h, hn⟩
    obtain ⟨n, -, h1⟩ := reach_iter k _ _ h
    obtain ⟨m, c', h2, h3⟩ := none_halts p hn
    exact ⟨{s0} + n + m, c', steps_seq trans (steps_seq trans init_start h1) h2, h3⟩

/-- `next` is defined `k` times in a row from `p`. -/
def okFor : Nat → Ph → Bool
  | 0, _ => true
  | k + 1, p => match next p with
    | none => false
    | some q => okFor k q

theorem okFor_sound : ∀ k p, okFor k p = true → ∀ j, j < k → ∀ q, iter j p = some q → next q ≠ none
  | 0, _, _, j, hj, _, _ => absurd hj (Nat.not_lt_zero j)
  | k + 1, p, h, j, hj, q, hi => by
    simp only [okFor] at h
    cases hp : next p with
    | none => simp [hp] at h
    | some r =>
      simp only [hp] at h
      cases j with
      | zero =>
        simp only [iter, Option.some.injEq] at hi; subst hi; simp [hp]
      | succ j =>
        simp only [iter, hp, Option.bind_some] at hi
        exact okFor_sound k r h j (by omega) q hi

/-- No halting frame among the first {K} frames of the run from blank tape. -/
theorem no_halt_phases : ∀ j, j < {K} → ∀ q, iter j ({start_ph}) = some q → next q ≠ none :=
  okFor_sound _ _ (by native_decide)

end {NS}
''')
open(os.path.join(OUT, 'Phases.lean'), 'w').write('\n'.join(L))
print('leaves', sum(len(l) for l in leaves.values()), 'start', start_ph, s0, file=sys.stderr)
