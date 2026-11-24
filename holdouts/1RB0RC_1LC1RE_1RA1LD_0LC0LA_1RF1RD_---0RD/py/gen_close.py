"""Generate lean/Close.lean: the closed pass map.  lean/Pass.lean proves the passes away from the boundary r = a / 3
(13 affine cases); here every pass within 6 of it gets its closed form too, one theorem per class
(t, a mod 3, j mod 2, r - a / 3), each a chain of the jump lemmas of lean/Jump.lean read off c/prun's jumps (mode
passv) and fitted as affine functions, as in py/gen_pass.py.  Five classes are the halting rows of lean/Jump.lean.
With them `cpass` is defined on every zigzag start, and `halts_iff_row` reduces the machine to its orbit.

usage: gcc -O2 -o prun c/prun.c && gcc -O3 -o crun c/crun.c -lm && python3 py/gen_close.py ./prun ./crun lean/Close.lean"""
import subprocess, random, sys
from fractions import Fraction as F
PRUN = sys.argv[1] if len(sys.argv) > 1 else './prun'
CRUN = sys.argv[2] if len(sys.argv) > 2 else './crun'
OUT = sys.argv[3] if len(sys.argv) > 3 else 'Close.lean'
NORB = int(__import__("os").environ.get("NORB", "100000000"))
random.seed(11)

def trace(starts):
    inp = '\n'.join(f"{t} {a} {j} {r}" for t, a, j, r in starts)
    out = subprocess.run([PRUN, 'passv'], input=inp, capture_output=True, text=True).stdout.strip().split('\n')
    res = []
    for l in out:
        lhs, rhs = l.split(' : ')
        assert 'HALT' not in rhs, l
        steps = []
        for blk in rhs.split(' -> ')[0].strip()[1:-1].split('] ['):
            c, k, t, a, j, r = blk.split()
            steps.append((int(c), int(k), t, int(a), int(j), int(r)))
        res.append(steps)
    return res

def fit(xs, ys):
    n = len(xs[0]) + 1
    rows = [[F(1)] + [F(v) for v in x] + [F(y)] for x, y in zip(xs, ys)]
    M = []
    for r in rows:   # pick n independent rows
        cand = M + [r[:]]
        if rank(cand, n) == len(cand): M = cand
        if len(M) == n: break
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0); M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]; M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    coef = [M[i][n] / M[i][i] for i in range(n)]
    for x, y in zip(xs, ys):
        assert coef[0] + sum(c * v for c, v in zip(coef[1:], x)) == y, ('fit', xs[:3], ys[:3])
    return coef

def rank(M, n):
    A = [r[:n] for r in M]; rk = 0
    for c in range(n):
        p = next((r for r in range(rk, len(A)) if A[r][c] != 0), None)
        if p is None: continue
        A[rk], A[p] = A[p], A[rk]
        for r in range(len(A)):
            if r != rk and A[r][c] != 0:
                f = A[r][c] / A[rk][c]; A[r] = [a - f * b for a, b in zip(A[r], A[rk])]
        rk += 1
    return rk

def expr(coef, names):
    assert all(c.denominator == 1 and c >= 0 for c in coef), coef
    parts = []
    for c, nm in zip(coef[1:], names):
        c = int(c)
        if c == 1: parts.append(nm)
        elif c: parts.append(f"{c} * {nm}")
    if coef[0] or not parts: parts.append(str(int(coef[0])))
    return ' + '.join(parts)

def sub(c1, c2): return [a - b for a, b in zip(c1, c2)]

HALT = {('y', 1, 0, 2): 'halt_y', ('Y', 1, 0, 3): 'halt_Y', ('y', 0, 1, 2): 'halt_y0', ('y', 2, 1, 2): 'halt_y2',
        ('Y', 0, 1, 2): 'halt_Y0'}

# a case: (t, e, jp, dl, sub); sub 'g' (q = p + q0, j = 2m + jp), 'q1' (q = 1, j = 2m + 2), 'q1j0' (q = 1, j = 0)
def special(t, e, jp, dl): return (t, e, jp) == ('y', 2, 0) and dl >= 2
def q0(t, e, jp, dl): return 2 if dl == 0 or special(t, e, jp, dl) else 1
def names(case):
    return {'g': ['p', 'm'], 'q1': ['m'], 'q1j0': []}[case[4]]
def start(case, vals):
    t, e, jp, dl, sb = case
    if sb == 'g': p, m = vals; q = p + q0(t, e, jp, dl); j = 2 * m + jp
    elif sb == 'q1': (m,) = vals; q = 1; j = 2 * m + 2
    else: q = 1; j = 0
    return (t, 3 * q + e, j, q + dl)
def subst(case):
    """the case's variables in terms of a, j"""
    t, e, jp, dl, sb = case
    if sb == 'g': return [f"(a / 3 - {q0(t, e, jp, dl)})", "(j / 2)"]
    if sb == 'q1': return ["(j / 2 - 1)"]
    return []
def cname(case):
    t, e, jp, dl, sb = case
    return f"near_{t}{e}_{'even' if jp == 0 else 'odd'}_{dl}" + ('' if sb == 'g' else '_' + sb)

def gen_case(case):
    nm = names(case)
    if nm: vals = [[random.randint(0, 3)] * 0 + [random.randint(0, 400) for _ in nm] for _ in range(14)]
    else: vals = [[]] * 2
    vals += [[0] * len(nm), [1] * len(nm)] if nm else []
    trs = trace([start(case, v) for v in vals])
    paths = set(tuple(s[0] for s in tr) for tr in trs)
    assert len(paths) == 1, (case, paths)
    L = len(trs[0])
    def fitstate(i):
        sts = [start(case, v) for v in vals] if i == 0 else [(tr[i - 1][2], tr[i - 1][3], tr[i - 1][4], tr[i - 1][5]) for tr in trs]
        assert len(set(s[0] for s in sts)) == 1
        if not nm: return sts[0][0], [[F(sts[0][c])] for c in (1, 2, 3)]
        return sts[0][0], [fit(vals, [s[c] for s in sts]) for c in (1, 2, 3)]
    S = [fitstate(i) for i in range(L + 1)]
    K = [([F(trs[0][i][1])] if not nm else fit(vals, [tr[i][1] for tr in trs])) for i in range(L)]
    tot = [sum(c) for c in zip(*K)]
    def st(i, names_=nm):
        t, cs = S[i]
        return f"(.{t} ({expr(cs[0], names_)}) ({expr(cs[1], names_)}) ({expr(cs[2], names_)}))"
    one = [F(1)] + [F(0)] * len(nm)
    E = lambda c: '(' + expr(c, nm) + ')'
    lines = []
    for i in range(L):
        code = trs[0][i][0]
        t0, c0 = S[i]; t1, c1 = S[i + 1]
        if code == 102:
            Kc = [x / 3 for x in sub(c0[0], c1[0])]
            lem = f"{t0}_zigzag {E(c1[0])} {E(sub(c1[2], one))} {E(Kc)} {E(c0[1])}"
        elif code == 100:
            Kc = [x / 4 for x in sub(c1[0], c0[0])]
            lem = f"{'w' if t0 == 'w' else 'W'}_sweep {E(c0[0])} {E(c1[1])} {E(sub(c0[2], one))} {E(Kc)}"
        elif code == 101:
            Kc = sub(c0[1], c1[1])
            if t0 == 'u': lem = f"u_sweep {E(c0[0])} {E(c1[1])} {E(Kc)} {E(c0[2])}"
            else: lem = f"U_sweep {E(sub(c0[0], one))} {E(c1[1])} {E(Kc)} {E(c0[2])}"
        else:
            lem = None
        if lem is None:
            lines.append(f"  have h{i} : iter 1 {st(i)} = some {st(i + 1)} := iter_one (by simp [next] <;> omega)")
        else:
            lines.append(f"  have h{i} : iter ({expr(K[i], nm)}) {st(i)} = some {st(i + 1)} :=\n"
                         f"    iter_cast ({lem}) (by omega) (by congr 1 <;> omega) (by congr 1 <;> omega)")
    chain = 'h0'
    for i in range(1, L): chain = f"iter_trans ({chain}) h{i}"
    args = (' (' + ' '.join(nm) + ' : Nat)') if nm else ''
    doc = f"/-- From `{st(0)}`: {L} jumps, path {', '.join(str(x[0]) for x in trs[0])}. -/"
    thm = (f"{doc}\ntheorem {cname(case)}{args} :\n    iter ({expr(tot, nm)}) {st(0)} = some {st(L)} := by\n" + '\n'.join(lines) +
           f"\n  exact iter_cast ({chain}) (by omega) rfl rfl\n")
    sb = subst(case)
    leaf = (S[L][0], [expr(c, sb) for c in S[L][1]], expr(tot, sb))
    return thm, leaf

# ---- the near map as a decision tree on (t, e, jp, dl) ----
cases = {}
thms = []
for t in 'yY':
    for e in range(3):
        for jp in (0, 1):
            for dl in range(7):
                if (t, e, jp, dl) in HALT: continue
                subs = ['g', 'q1', 'q1j0'] if special(t, e, jp, dl) else ['g']
                for sb in subs:
                    c = (t, e, jp, dl, sb)
                    thm, leaf = gen_case(c)
                    thms.append(thm); cases[c] = leaf

def leafexpr(c):
    return f".go (L{cname(c)[4:]} a j) (N{cname(c)[4:]} a j)"

def leafdefs():
    o = []
    for c, (t2, (x, jj, rr), n) in cases.items():
        k = cname(c)[4:]
        o.append(f"/-- The pass of `{cname(c)}` in terms of `a` and `j`: the next zigzag start and the frames. -/")
        o.append(f"def L{k} (a j : Nat) : Ph := .{t2} ({x}) ({jj}) ({rr})")
        o.append(f"def N{k} (a j : Nat) : Nat := {n}")
    return '\n'.join(o) + '\n'

def leafnames():
    return ', '.join(f"L{cname(c)[4:]}, N{cname(c)[4:]}" for c in cases)

# the decision tree: ('if', cond, then, else) | ('halt',) | ('off',) | ('go', case)
def build(t):
    def D(e, jp):
        node = ('off',)
        for dl in reversed(range(7)):
            c = (t, e, jp, dl)
            if c in HALT: leaf = ('halt', HALT[c])
            elif special(*c): leaf = ('if', '2 ≤ a / 3', ('go', c + ('g',)), ('if', '2 ≤ j', ('go', c + ('q1',)), ('go', c + ('q1j0',))))
            else: leaf = ('go', c + ('g',))
            node = ('if', 'r = a / 3' + ('' if dl == 0 else f' + {dl}'), leaf, node)
        return node
    J = lambda e: ('if', 'j % 2 = 0', D(e, 0), D(e, 1))
    return ('if', '3 ≤ a ∧ 2 ≤ r', ('if', 'a % 3 = 0', J(0), ('if', 'a % 3 = 1', J(1), J(2))), ('off',))

def render_def(n, ind):
    P = ' ' * ind
    if n[0] == 'if': return f"{P}if {n[1]} then\n{render_def(n[2], ind + 2)}\n{P}else\n{render_def(n[3], ind + 2)}"
    if n[0] == 'go': return P + leafexpr(n[1])
    return P + '.' + n[0]  # halt or off

def render_proof(n, ind):
    P = ' ' * ind
    if n[0] == 'if':
        return (f"{P}split at h\n{P}· " + render_proof(n[2], ind + 2).lstrip() + f"\n{P}· " + render_proof(n[3], ind + 2).lstrip())
    if n[0] == 'go':
        c = n[1]; args = ' '.join(subst(c))
        return (f"{P}simp only [Res.go.injEq] at h; obtain ⟨rfl, rfl⟩ := h\n"
                f"{P}exact iter_cast ({cname(c)}{' ' + args if args else ''}) (by simp only [N{cname(c)[4:]}]; omega) (by congr 1 <;> omega) (by simp only [L{cname(c)[4:]}]; congr 1 <;> omega)")
    return P + 'cases h'


HALTFORM = {'halt_y': ".y (3 * (a / 3) + 1) (2 * (j / 2)) (a / 3 + 2)", 'halt_y0': ".y (3 * (a / 3)) (2 * (j / 2) + 1) (a / 3 + 2)",
            'halt_y2': ".y (3 * (a / 3) + 2) (2 * (j / 2) + 1) (a / 3 + 2)", 'halt_Y': ".Y (3 * (a / 3) + 1) (2 * (j / 2)) (a / 3 + 3)",
            'halt_Y0': ".Y (3 * (a / 3)) (2 * (j / 2) + 1) (a / 3 + 2)"}

def mirror(n, ind, at, leaf, path=()):
    """by_cases on each condition of the tree, rewriting the if at h (at = ' at h') or in the goal (at = '')"""
    P = ' ' * ind
    if n[0] == 'if':
        th = mirror(n[2], ind + 2, at, leaf, path); el = mirror(n[3], ind + 2, at, leaf, path)
        return (f"{P}by_cases hc : {n[1]}\n{P}· rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]{at}\n{th}\n{P}· rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]{at}\n{el}")
    return '\n'.join(P + l for l in leaf(n))

def M(t, kind):
    tr = build(t); T = t
    def hl(n):  # the halting class of a halt leaf: find it by the leaf identity
        return n[1] if len(n) > 1 else None
    if kind == 'go':
        def lf(n):
            if n[0] != 'go': return ['cases h']
            c = n[1]; args = ' '.join(subst(c)); k = cname(c)[4:]
            return ["simp only [Res.go.injEq] at h; obtain ⟨rfl, rfl⟩ := h",
                    f"exact iter_cast ({cname(c)}{' ' + args if args else ''}) (by simp only [N{k}] <;> omega) (by congr 1 <;> omega) (by simp only [L{k}] <;> congr 1 <;> omega)"]
        return mirror(tr, 2, ' at h', lf)
    if kind == 'total':
        return mirror(tr, 2, '', lambda n: ['omega'] if n[0] == 'off' else ['intro h; cases h'])
    if kind == 'halt':
        def lf(n):
            if n[0] != 'halt': return ['cases h']
            nm = n[1]
            return [f"rw [show Ph.{T} a j r = {HALTFORM[nm]} by congr 1 <;> omega]; exact {nm} _ _"]
        return mirror(tr, 2, ' at h', lf)
    if kind == 'even':
        def lf(n):
            if n[0] != 'go': return ['cases h']
            k = cname(n[1])[4:]
            return ["simp only [Res.go.injEq] at h; obtain ⟨rfl, rfl⟩ := h", f"simp only [Ez, L{k}, N{k}, and_true, true_and]; omega"]
        return mirror(tr, 2, ' at h', lf)
    if kind == 'hif':
        return mirror(tr, 8, ' at h', lambda n: ['omega'] if n[0] == 'halt' else ['cases h'])
    if kind == 'hib':
        return mirror(tr, 6, '', lambda n: ['all_goals rfl'] if n[0] == 'halt' else ['omega'])

def tree(t, ind): return render_def(build(t), ind)
def proof_go(t): return render_proof(build(t), 2)

HEAD = '''import Pass

/-!
# 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD: the closed pass map

Generated by `py/gen_close.py`; do not edit.  `Pass.lean` gives the pass (one zigzag start `t(a, j, r)`, `t` = `y` or
`Y`, `a ≥ 3`, `r ≥ 2`, to the next) in closed form away from the line `r = a / 3`: 13 affine cases (`fast`).  Here the
passes within 6 of it get closed forms too.  Write `a = 3q + e` and `r = q + δ` with `0 ≤ δ ≤ 6`: for each `t`, `e`,
parity of `j` and `δ` the pass is one chain of zigzags, sweeps and single cases of `next`, the same for all sizes
(one theorem `near_*` each, for all `q` and `j`; `y` with `e = 2`, even `j`, `δ ≥ 2` splits into `q ≥ 2`, `q = 1`,
and `q = 1, j = 0`), except five classes, the halting rows of `Jump.lean`:
`y(3q + 1, 2m, q + 2)`, `Y(3q + 1, 2m, q + 3)`, `y(3q, 2m + 1, q + 2)`, `y(3q + 2, 2m + 1, q + 2)`, `Y(3q, 2m + 1, q + 2)`.

So the pass map is closed: `cpass` (`fast`, else `near`) is `.go q n` (the next zigzag start and the frame count) or
`.halt` on every zigzag start (`cpass_total`, `cpass_go`, `cpass_halt`), and it is `.halt` exactly on the five rows.
Every case keeps `j` even (`cpass_even`), and the run from blank tape starts at `y(3, 0, 5)` with `j = 0`, so only the
two even rows can be met:

**`halts_iff_row`: the machine halts from blank tape iff the orbit of `y(3, 0, 5)` under the closed pass map reaches
`y(a, j, r)` with `a = 1 mod 3` and `r = a / 3 + 2`, or `Y(a, j, r)` with `a = 1 mod 3` and `r = a / 3 + 3`.**

`orb_frames` runs `10^8` closed passes by `native_decide`; `no_row_before`: none of them is on a row.
-/

namespace H97525

/-! ## The passes near the boundary -/

'''

MID = '''
/-! ## The closed pass map -/

/-- The result of a pass: the next zigzag start and the frames to it, a halt, or not a zigzag start. -/
inductive Res where
  | go (q : Ph) (n : Nat)
  | halt
  | off
  deriving DecidableEq, Repr

{LEAFDEFS}
/-- A pass of `y(a, j, r)` near the boundary `a / 3 ≤ r ≤ a / 3 + 6`. -/
def nearY (a j r : Nat) : Res :=
{TY}

/-- A pass of `Y(a, j, r)` near the boundary. -/
def nearYY (a j r : Nat) : Res :=
{TYY}

def near : Ph → Res
  | .y a j r => nearY a j r
  | .Y a j r => nearYY a j r
  | _ => .off

/-- The closed pass map. -/
def cpass (p : Ph) : Res :=
  match fast p with
  | some (q, n) => .go q n
  | none => near p

theorem nearY_go (a j r q n) (h : nearY a j r = .go q n) : iter n (.y a j r) = some q := by
  unfold nearY at h
{M_go_y}

theorem nearYY_go (a j r q n) (h : nearYY a j r = .go q n) : iter n (.Y a j r) = some q := by
  unfold nearYY at h
{M_go_Y}

theorem near_go (p q : Ph) (n : Nat) (h : near p = .go q n) : iter n p = some q := by
  match p with
  | .y a j r => exact nearY_go a j r q n h
  | .Y a j r => exact nearYY_go a j r q n h
  | .z _ _ _ | .w _ _ _ | .u _ _ _ | .Z _ _ _ | .W _ _ _ | .U _ _ _ => cases h

theorem cpass_go (p q : Ph) (n : Nat) (h : cpass p = .go q n) : iter n p = some q := by
  unfold cpass at h
  cases hf : fast p with
  | some x => obtain ⟨q', n'⟩ := x; rw [hf] at h; cases h; exact fast_sound p q n hf
  | none => rw [hf] at h; exact near_go p q n h

/-- A zigzag start. -/
def Zs : Ph → Prop
  | .y a _ r => 3 ≤ a ∧ 2 ≤ r
  | .Y a _ r => 3 ≤ a ∧ 2 ≤ r
  | _ => False

/-- A zigzag start with `j` even. -/
def Ez : Ph → Prop
  | .y a j r => 3 ≤ a ∧ 2 ≤ r ∧ j % 2 = 0
  | .Y a j r => 3 ≤ a ∧ 2 ≤ r ∧ j % 2 = 0
  | _ => False

/-- The two halting rows with `j` even. -/
def Row : Ph → Prop
  | .y a _ r => a % 3 = 1 ∧ r = a / 3 + 2
  | .Y a _ r => a % 3 = 1 ∧ r = a / 3 + 3
  | _ => False

theorem fast_none_y (a j r : Nat) (h : fast (.y a j r) = none) (ha : 3 ≤ a) (hr : 2 ≤ r) :
    a / 3 ≤ r ∧ r ≤ a / 3 + 6 := by
  simp only [fast] at h
  repeat' split at h
  all_goals first | omega | (cases h)

theorem fast_none_Y (a j r : Nat) (h : fast (.Y a j r) = none) (ha : 3 ≤ a) (hr : 2 ≤ r) :
    a / 3 ≤ r ∧ r ≤ a / 3 + 6 := by
  simp only [fast] at h
  repeat' split at h
  all_goals first | omega | (cases h)

theorem nearY_total (a j r : Nat) (ha : 3 ≤ a) (hr : 2 ≤ r) (h1 : a / 3 ≤ r) (h2 : r ≤ a / 3 + 6) :
    nearY a j r ≠ .off := by
  unfold nearY
{M_total_y}

theorem nearYY_total (a j r : Nat) (ha : 3 ≤ a) (hr : 2 ≤ r) (h1 : a / 3 ≤ r) (h2 : r ≤ a / 3 + 6) :
    nearYY a j r ≠ .off := by
  unfold nearYY
{M_total_Y}

/-- **The pass map is closed**: on every zigzag start it is a pass or a halt. -/
theorem cpass_total (p : Ph) (hz : Zs p) : cpass p ≠ .off := by
  unfold cpass
  cases hf : fast p with
  | some x => obtain ⟨q, n⟩ := x; intro h; cases h
  | none =>
    match p with
    | .y a j r => obtain ⟨ha, hr⟩ := hz; have := fast_none_y a j r hf ha hr; exact nearY_total a j r ha hr this.1 this.2
    | .Y a j r => obtain ⟨ha, hr⟩ := hz; have := fast_none_Y a j r hf ha hr; exact nearYY_total a j r ha hr this.1 this.2

theorem nearY_halt (a j r : Nat) (h : nearY a j r = .halt) : ∃ n s, iter n (.y a j r) = some s ∧ next s = none := by
  unfold nearY at h
{M_halt_y}

theorem nearYY_halt (a j r : Nat) (h : nearYY a j r = .halt) : ∃ n s, iter n (.Y a j r) = some s ∧ next s = none := by
  unfold nearYY at h
{M_halt_Y}

theorem cpass_halt (p : Ph) (h : cpass p = .halt) : ∃ n s, iter n p = some s ∧ next s = none := by
  unfold cpass at h
  cases hf : fast p with
  | some x => obtain ⟨q, n⟩ := x; rw [hf] at h; cases h
  | none =>
    rw [hf] at h
    match p with
    | .y a j r => exact nearY_halt a j r h
    | .Y a j r => exact nearYY_halt a j r h
    | .z _ _ _ | .w _ _ _ | .u _ _ _ | .Z _ _ _ | .W _ _ _ | .U _ _ _ => cases h

theorem nearY_even (a j r q n) (hj : j % 2 = 0) (h : nearY a j r = .go q n) : Ez q ∧ 0 < n := by
  unfold nearY at h
{M_even_y}

theorem nearYY_even (a j r q n) (hj : j % 2 = 0) (h : nearYY a j r = .go q n) : Ez q ∧ 0 < n := by
  unfold nearYY at h
{M_even_Y}

theorem fast_even (p q : Ph) (n : Nat) (hp : Ez p) (h : fast p = some (q, n)) : Ez q ∧ 0 < n := by
  match p with
  | .y a j r =>
    simp only [Ez] at hp; simp only [fast] at h
    repeat' split at h
    all_goals first | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp only [Ez, and_true, true_and]; omega) | (cases h)
  | .Y a j r =>
    simp only [Ez] at hp; simp only [fast] at h
    repeat' split at h
    all_goals first | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp only [Ez, and_true, true_and]; omega) | (cases h)

/-- Every pass from a zigzag start with `j` even goes to one, in a positive number of frames. -/
theorem cpass_even (p q : Ph) (n : Nat) (hp : Ez p) (h : cpass p = .go q n) : Ez q ∧ 0 < n := by
  unfold cpass at h
  cases hf : fast p with
  | some x => obtain ⟨q', n'⟩ := x; rw [hf] at h; cases h; exact fast_even p q n hp hf
  | none =>
    rw [hf] at h
    match p with
    | .y a j r => exact nearY_even a j r q n hp.2.2 h
    | .Y a j r => exact nearYY_even a j r q n hp.2.2 h

/-- On zigzag starts with `j` even, the pass halts exactly on the two rows. -/
theorem cpass_halt_iff (p : Ph) (hp : Ez p) : cpass p = .halt ↔ Row p := by
  match p with
  | .y a j r =>
    simp only [Ez] at hp; simp only [cpass, Row]
    constructor
    · intro h
      cases hf : fast (.y a j r) with
      | some x => obtain ⟨q, n⟩ := x; rw [hf] at h; cases h
      | none =>
        rw [hf] at h; simp only [near] at h; unfold nearY at h
{M_hif_y}
    · intro hr
      have hf : fast (.y a j r) = none := by
        simp only [fast]; repeat' split
        all_goals first | rfl | omega
      rw [hf]; simp only [near]; unfold nearY
{M_hib_y}
  | .Y a j r =>
    simp only [Ez] at hp; simp only [cpass, Row]
    constructor
    · intro h
      cases hf : fast (.Y a j r) with
      | some x => obtain ⟨q, n⟩ := x; rw [hf] at h; cases h
      | none =>
        rw [hf] at h; simp only [near] at h; unfold nearYY at h
{M_hif_Y}
    · intro hr
      have hf : fast (.Y a j r) = none := by
        simp only [fast]; repeat' split
        all_goals first | rfl | omega
      rw [hf]; simp only [near]; unfold nearYY
{M_hib_Y}

/-! ## The orbit -/

/-- `k` closed passes from `p`, adding their frames to `f` (tail recursive, for `native_decide`). -/
def orbT : Nat → Ph → Nat → Option (Ph × Nat)
  | 0, p, f => some (p, f)
  | k + 1, p, f => match cpass p with
    | .go q n => orbT k q (f + n)
    | _ => none

/-- `k` closed passes from `p`, with the frames they take. -/
def orb (p : Ph) (k : Nat) : Option (Ph × Nat) := orbT k p 0

theorem orbT_succ : ∀ k p f, orbT (k + 1) p f = match orbT k p f with
    | some (q, f') => (match cpass q with
      | .go q' n => some (q', f' + n)
      | _ => none)
    | none => none
  | 0, p, f => by
    show (match cpass p with | .go q n => orbT 0 q (f + n) | _ => none) =
      (match cpass p with | .go q' n => some (q', f + n) | _ => none)
    cases cpass p <;> rfl
  | k + 1, p, f => by
    show (match cpass p with | .go q n => orbT (k + 1) q (f + n) | _ => none) =
      (match (match cpass p with | .go q n => orbT k q (f + n) | _ => none) with
        | some (q, f') => (match cpass q with | .go q' n => some (q', f' + n) | _ => none)
        | none => none)
    cases cpass p with
    | go q n => exact orbT_succ k q (f + n)
    | halt => rfl
    | off => rfl

theorem orb_zero (p : Ph) : orb p 0 = some (p, 0) := rfl

theorem orb_succ (p : Ph) (k : Nat) : orb p (k + 1) = match orb p k with
    | some (q, f) => (match cpass q with
      | .go q' n => some (q', f + n)
      | _ => none)
    | none => none := orbT_succ k p 0

theorem orb_sound (p : Ph) : ∀ k q f, orb p k = some (q, f) → iter f p = some q
  | 0, q, f, h => by rw [orb_zero] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | k + 1, q, f, h => by
    rw [orb_succ] at h
    cases hk : orb p k with
    | none => rw [hk] at h; cases h
    | some x =>
      obtain ⟨q0, f0⟩ := x; rw [hk] at h; simp only at h
      cases hc : cpass q0 with
      | go q' n => rw [hc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                   exact iter_trans (orb_sound p k q0 f0 hk) (cpass_go q0 q' n hc)
      | halt => rw [hc] at h; cases h
      | off => rw [hc] at h; cases h

theorem orb_even (p : Ph) (hp : Ez p) : ∀ k q f, orb p k = some (q, f) → Ez q ∧ k ≤ f
  | 0, q, f, h => by rw [orb_zero] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hp, Nat.le_refl 0⟩
  | k + 1, q, f, h => by
    rw [orb_succ] at h
    cases hk : orb p k with
    | none => rw [hk] at h; cases h
    | some x =>
      obtain ⟨q0, f0⟩ := x; rw [hk] at h; simp only at h
      cases hc : cpass q0 with
      | go q' n => rw [hc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                   have ih := orb_even p hp k q0 f0 hk
                   have := cpass_even q0 q' n ih.1 hc
                   exact ⟨this.1, by omega⟩
      | halt => rw [hc] at h; cases h
      | off => rw [hc] at h; cases h

/-- The first zigzag start of the run from blank tape. -/
theorem first_start : iter 6 (Ph.z 0 0 2) = some (.y 3 0 5) := by decide

/-- **The machine halts from blank tape iff the orbit of `y(3, 0, 5)` under the closed pass map meets a halting
row.** -/
theorem halts_iff_row : HaltsFromBlank ↔ ∃ k q f, orb (.y 3 0 5) k = some (q, f) ∧ Row q := by
  have hp0 : Ez (.y 3 0 5) := by simp [Ez]
  rw [halts_iff]
  constructor
  · intro ⟨T, s, hT, hs⟩
    apply Classical.byContradiction
    intro hno
    have hall : ∀ k, ∃ q f, orb (.y 3 0 5) k = some (q, f) := by
      intro k
      induction k with
      | zero => exact ⟨_, _, rfl⟩
      | succ k ih =>
        obtain ⟨q, f, hk⟩ := ih
        have he := orb_even _ hp0 k q f hk
        have hz : Zs q := by
          match q, he with
          | .y a j r, ⟨⟨h1, h2, _⟩, _⟩ => exact ⟨h1, h2⟩
          | .Y a j r, ⟨⟨h1, h2, _⟩, _⟩ => exact ⟨h1, h2⟩
        have hnr : ¬ Row q := fun hr => hno ⟨k, q, f, hk, hr⟩
        have hnh : cpass q ≠ .halt := fun h => hnr ((cpass_halt_iff q he.1).1 h)
        have hno' := cpass_total q hz
        cases hc : cpass q with
        | go q' n => exact ⟨q', f + n, by rw [orb_succ, hk]; simp only [hc]⟩
        | halt => exact absurd hc hnh
        | off => exact absurd hc hno'
    obtain ⟨q, f, hk⟩ := hall (T + 1)
    have hf := (orb_even _ hp0 _ q f hk).2
    have hit := iter_trans first_start (orb_sound _ _ q f hk)
    exact not_none_before _ _ _ hit T (by omega) s hT hs
  · intro ⟨k, q, f, hk, hr⟩
    have he := (orb_even _ hp0 k q f hk).1
    obtain ⟨n, s, h1, h2⟩ := cpass_halt q ((cpass_halt_iff q he).2 hr)
    exact ⟨_, s, iter_trans (iter_trans first_start (orb_sound _ _ q f hk)) h1, h2⟩

/-- No orbit point before `k` is on a row if the orbit reaches `k`. -/
theorem no_row_before (k : Nat) (q : Ph) (f : Nat) (h : orb (.y 3 0 5) k = some (q, f)) :
    ∀ i, i < k → ∀ q' f', orb (.y 3 0 5) i = some (q', f') → ¬ Row q' := by
  have hp0 : Ez (.y 3 0 5) := by simp [Ez]
  intro i hi
  induction k generalizing q f with
  | zero => omega
  | succ k ih =>
    rw [orb_succ] at h
    cases hk : orb (.y 3 0 5) k with
    | none => rw [hk] at h; cases h
    | some x =>
      obtain ⟨q0, f0⟩ := x; rw [hk] at h; simp only at h
      intro q' f' hi' hr
      by_cases hik : i = k
      · subst hik; rw [hk] at hi'; simp only [Option.some.injEq, Prod.mk.injEq] at hi'; obtain ⟨rfl, rfl⟩ := hi'
        have he := (orb_even _ hp0 _ _ _ hk).1
        rw [(cpass_halt_iff q0 he).2 hr] at h; cases h
      · exact ih q0 f0 hk (by omega) q' f' hi' hr

'''
NATIVE = '''/-- Where the first {NS} closed passes from `y(3, 0, 5)` end (`c/crun.c`, mode `lean`, prints the same). -/
theorem orb_frames : orb (.y 3 0 5) {N} = some ({st}, {F}) := by
  native_decide

/-- None of the first {NS} zigzag starts of the run from blank tape is on a halting row. -/
theorem no_row : ∀ i, i < {N} → ∀ q f, orb (.y 3 0 5) i = some (q, f) → ¬ Row q :=
  no_row_before _ _ _ orb_frames

'''
TY = tree('y', 2); TYY = tree('Y', 2)
out = [HEAD] + [t + '\n' for t in thms]
mid = MID.replace('{TY}', TY).replace('{TYY}', TYY)
mid = mid.replace('{LEAFDEFS}', leafdefs()).replace('{LEAFNAMES}', leafnames())
for t in 'yY':
    for kd in ('go', 'total', 'halt', 'even', 'hif', 'hib'): mid = mid.replace('{M_' + kd + '_' + t + '}', M(t, kd))
out.append(mid)
lean = subprocess.run([CRUN, 'lean', str(NORB)], capture_output=True, text=True).stdout.strip()
st_, fr_ = lean.split('= some (')[1].rstrip(')').rsplit(', ', 1)
out.append(NATIVE.replace('{N}', str(NORB)).replace('{NS}', f'{NORB:,}').replace('{st}', st_).replace('{F}', fr_))
out.append('end H97525\n')
open(OUT, 'w').write(''.join(out))
print(len(thms), 'near theorems;', lean)
