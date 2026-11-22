"""Generate lean/Pass.lean: the pass map (one zigzag start to the next) for all sizes, each case a chain of the
jump lemmas of lean/Jump.lean.  The chain of each case is read off c/prun's jumps (mode passv) on sample values and
fitted as affine functions of the case's variables; Lean then checks every step for all values.  The last theorem
(native_decide) states where N passes from the blank-tape frame end, as `prun lean N` computes it.

usage: gcc -O2 -o prun c/prun.c && python3 py/gen_pass.py ./prun lean/Pass.lean"""
import subprocess, random, sys
from fractions import Fraction as F
FRUN = sys.argv[1] if len(sys.argv) > 1 else './prun'
NPASS = 100000000
random.seed(7)

def trace(starts):
    inp = '\n'.join(f"{t} {a} {j} {r}" for t, a, j, r in starts)
    out = subprocess.run([FRUN, 'passv'], input=inp, capture_output=True, text=True).stdout.strip().split('\n')
    res = []
    for l in out:
        lhs, rhs = l.split(' : ')
        steps = []
        for blk in rhs.split(' -> ')[0].strip()[1:-1].split('] ['):
            c, k, t, a, j, r = blk.split()
            steps.append((int(c), int(k), t, int(a), int(j), int(r)))
        res.append(steps)
    return res

def fit(xs, ys):
    """exact affine fit ys = c0 + sum ci xi"""
    n = len(xs[0]) + 1
    rows = [[F(1)] + [F(v) for v in x] + [F(y)] for x, y in zip(xs, ys)]
    M = [r[:] for r in rows[:n]]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0); M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]; M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    coef = [M[i][n] / M[i][i] for i in range(n)]
    for x, y in zip(xs, ys):
        assert coef[0] + sum(c * v for c, v in zip(coef[1:], x)) == y, ('fit', xs[:3], ys[:3])
    return coef

def expr(coef, names):
    assert all(c.denominator == 1 and c >= 0 for c in coef), coef
    parts = []
    for c, nm in zip(coef[1:], names):
        c = int(c)
        if c == 1: parts.append(nm)
        elif c: parts.append(f"{c} * {nm}")
    if coef[0] or not parts: parts.append(str(int(coef[0])))
    return ' + '.join(parts)

def sub(c1, c2):
    return [a - b for a, b in zip(c1, c2)]

CASES = []
# growth: q = p + 1, j = 2m + jp, r = q + 7 + s
for t in 'yY':
    for e in range(3):
        for jp in ([0, 1] if (t, e) != ('Y', 2) else [None]):
            CASES.append(('grow', t, e, jp))
CASES += [('drain', 'y', None, None), ('drain', 'Y', None, None)]

def start(case, vals):
    kind, t, e, jp = case
    if kind == 'grow':
        if jp is None:
            p, j, s = vals; q = p + 1; return (t, 3 * q + e, j, q + 7 + s)
        p, m, s = vals; q = p + 1; return (t, 3 * q + e, 2 * m + jp, q + 7 + s)
    r, j, b = vals; return (t, 3 * r + 9 + b, j, r + 2)

def names(case):
    kind, t, e, jp = case
    if kind == 'grow': return ['p', 'j', 's'] if jp is None else ['p', 'm', 's']
    return ['r', 'j', 'b']

TAGS = {'z': 'z', 'y': 'y', 'w': 'w', 'u': 'u', 'Z': 'Z', 'Y': 'Y', 'W': 'W', 'U': 'U'}

def gen_case(case):
    nm = names(case)
    vals = [[random.randint(3, 400) for _ in range(3)] for _ in range(12)]
    trs = trace([start(case, v) for v in vals])
    paths = set(tuple(s[0] for s in tr) for tr in trs)
    assert len(paths) == 1, (case, paths)
    L = len(trs[0])
    # states: S0 = start, S_i after step i
    def fitstate(i):
        if i == 0:
            sts = [start(case, v) for v in vals]
        else:
            sts = [(tr[i - 1][2], tr[i - 1][3], tr[i - 1][4], tr[i - 1][5]) for tr in trs]
        tags = set(s[0] for s in sts); assert len(tags) == 1
        return sts[0][0], [fit(vals, [s[c] for s in sts]) for c in (1, 2, 3)]
    S = [fitstate(i) for i in range(L + 1)]
    K = [fit(vals, [tr[i][1] for tr in trs]) for i in range(L)]
    tot = [sum(c) for c in zip(*K)]
    def st(i):
        t, cs = S[i]
        return f"(.{t} ({expr(cs[0], nm)}) ({expr(cs[1], nm)}) ({expr(cs[2], nm)}))"
    lines = []
    one = [F(1)] + [F(0)] * 3
    for i in range(L):
        code = trs[0][i][0]
        t0, c0 = S[i]; t1, c1 = S[i + 1]
        E = lambda c: '(' + expr(c, nm) + ')'
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
            lines.append(f"  have h{i} : iter 1 {st(i)} = some {st(i + 1)} := iter_one (by simp [next])")
        else:
            lines.append(f"  have h{i} : iter ({expr(K[i], nm)}) {st(i)} = some {st(i + 1)} :=\n"
                         f"    iter_cast ({lem}) (by omega) (by congr 1 <;> omega) (by congr 1 <;> omega)")
    chain = 'h0'
    for i in range(1, L): chain = f"iter_trans ({chain}) h{i}"
    kind, t, e, jp = case
    nmz = f"{kind}_{t}{'' if e is None else e}{'' if jp is None else ('_even' if jp == 0 else '_odd')}"
    args = ' '.join(nm)
    doc = f"/-- `{kind}` from `{st(0)}`: {L} jumps, path {', '.join(str(x[0]) for x in trs[0])}. -/"
    body = '\n'.join(lines)
    thm = (f"{doc}\ntheorem {nmz} ({args} : Nat) :\n    iter ({expr(tot, nm)}) {st(0)} = some {st(L)} := by\n{body}\n"
           f"  exact iter_cast ({chain}) (by omega) rfl rfl\n")
    return nmz, thm, (S[0], S[L], tot)

TAIL = r'''/-! ## The pass map -/

/-- One pass away from the boundary `r = a / 3`, with its frame count; `none` near the boundary and off zigzag
starts. -/
def fast : Ph → Option (Ph × Nat)
  | .y a j r =>
    if 2 ≤ r ∧ r + 1 ≤ a / 3 then some (.y (a + 1 - 3 * r) 0 (4 * r + 2 * j + 2), 4 * r + j - 1)
    else if 1 ≤ a / 3 ∧ a / 3 + 7 ≤ r then
      if a % 3 = 0 then
        if j % 2 = 0 then some (.y (4 * (a / 3) + 2 * j + 2) 0 (r - a / 3 - 1), 3 * (a / 3) + j / 2 + 4)
        else some (.y (4 * (a / 3) + 2 * j + 5) 0 (r - a / 3 - 4), 3 * (a / 3) + j / 2 + 4)
      else if a % 3 = 1 then
        if j % 2 = 0 then some (.y (4 * (a / 3) + 2 * j + 7) 0 (r - a / 3 - 4), 3 * (a / 3) + j / 2 + 4)
        else some (.y (4 * (a / 3) + 2 * j + 4) 0 (r - a / 3 - 1), 3 * (a / 3) + j / 2 + 5)
      else
        if j % 2 = 0 then some (.Y (4 * (a / 3) + 2 * j + 2) 0 (r - a / 3 - 1), 3 * (a / 3) + j / 2 + 3)
        else some (.Y (4 * (a / 3) + 2 * j + 5) 0 (r - a / 3 - 4), 3 * (a / 3) + j / 2 + 3)
    else none
  | .Y a j r =>
    if 2 ≤ r ∧ r + 1 ≤ a / 3 then some (.Y (a + 1 - 3 * r) 0 (4 * r + 2 * j + 2), 4 * r + j - 1)
    else if 1 ≤ a / 3 ∧ a / 3 + 7 ≤ r then
      if a % 3 = 0 then
        if j % 2 = 0 then some (.y (4 * (a / 3) + 2 * j + 5) 0 (r - a / 3 - 1), 3 * (a / 3) + j / 2 + 3)
        else some (.y (4 * (a / 3) + 2 * j + 8) 0 (r - a / 3 - 4), 3 * (a / 3) + j / 2 + 3)
      else if a % 3 = 1 then
        if j % 2 = 0 then some (.y (4 * (a / 3) + 2 * j + 11) 0 (r - a / 3 - 5), 3 * (a / 3) + j / 2 + 7)
        else some (.y (4 * (a / 3) + 2 * j + 8) 0 (r - a / 3 - 2), 3 * (a / 3) + j / 2 + 8)
      else some (.y 5 (j + 2 * (a / 3) + 2) (r - a / 3 - 1), 2 * (a / 3) + 2)
    else none
  | _ => none

theorem fast_sound : ∀ p q n, fast p = some (q, n) → iter n p = some q := by
  intro p q n h
  match p with
  | .y a j r =>
    simp only [fast] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact iter_cast (drain_y (r - 2) j (a - 3 * r - 3)) (by omega) (by congr 1 <;> omega) (by congr 1 <;> omega)
    · split at h
      · split at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            exact iter_cast (grow_y0_even (a / 3 - 1) (j / 2) (r - a / 3 - 7)) (by omega) (by congr 1 <;> omega) (by congr 1 <;> omega)
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            exact iter_cast (grow_y0_odd (a / 3 - 1) (j / 2) (r - a / 3 - 7)) (by omega) (by congr 1 <;> omega) (by congr 1 <;> omega)
        · split at h
          · split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              exact iter_cast (grow_y1_even (a / 3 - 1) (j / 2) (r - a / 3 - 7)) (by omega) (by congr 1 <;> omega) (by congr 1 <;> omega)
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              exact iter_cast (grow_y1_odd (a / 3 - 1) (j / 2) (r - a / 3 - 7)) (by omega) (by congr 1 <;> omega) (by congr 1 <;> omega)
          · split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              exact iter_cast (grow_y2_even (a / 3 - 1) (j / 2) (r - a / 3 - 7)) (by omega) (by congr 1 <;> omega) (by congr 1 <;> omega)
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              exact iter_cast (grow_y2_odd (a / 3 - 1) (j / 2) (r - a / 3 - 7)) (by omega) (by congr 1 <;> omega) (by congr 1 <;> omega)
      · simp at h
  | .Y a j r =>
    simp only [fast] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact iter_cast (drain_Y (r - 2) j (a - 3 * r - 3)) (by omega) (by congr 1 <;> omega) (by congr 1 <;> omega)
    · split at h
      · split at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            exact iter_cast (grow_Y0_even (a / 3 - 1) (j / 2) (r - a / 3 - 7)) (by omega) (by congr 1 <;> omega) (by congr 1 <;> omega)
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            exact iter_cast (grow_Y0_odd (a / 3 - 1) (j / 2) (r - a / 3 - 7)) (by omega) (by congr 1 <;> omega) (by congr 1 <;> omega)
        · split at h
          · split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              exact iter_cast (grow_Y1_even (a / 3 - 1) (j / 2) (r - a / 3 - 7)) (by omega) (by congr 1 <;> omega) (by congr 1 <;> omega)
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              exact iter_cast (grow_Y1_odd (a / 3 - 1) (j / 2) (r - a / 3 - 7)) (by omega) (by congr 1 <;> omega) (by congr 1 <;> omega)
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            exact iter_cast (grow_Y2 (a / 3 - 1) j (r - a / 3 - 7)) (by omega) (by congr 1 <;> omega) (by congr 1 <;> omega)
      · simp at h
  | .z _ _ _ | .w _ _ _ | .u _ _ _ | .Z _ _ _ | .W _ _ _ | .U _ _ _ => simp [fast] at h

/-- A whole pass where `fast` applies, else one jump. -/
def pass (p : Ph) : Option (Ph × Nat) :=
  match fast p with
  | some x => some x
  | none => jump p

theorem pass_sound (p q : Ph) (n : Nat) (h : pass p = some (q, n)) : iter n p = some q := by
  unfold pass at h
  cases hf : fast p with
  | some x => rw [hf] at h; cases h; exact fast_sound p q n hf
  | none => rw [hf] at h; exact jump_sound p q n h

/-- `N` passes from `p`, counting frames from `f`. -/
def passes : Nat → Ph → Nat → Option (Ph × Nat)
  | 0, p, f => some (p, f)
  | N + 1, p, f => match pass p with
    | none => none
    | some (q, n) => passes N q (f + n)

theorem passes_sound : ∀ N p f q F, passes N p f = some (q, F) → iter (F - f) p = some q ∧ f ≤ F
  | 0, p, f, q, F, h => by
    simp only [passes, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [iter]
  | N + 1, p, f, q, F, h => by
    simp only [passes] at h
    cases hj : pass p with
    | none => simp [hj] at h
    | some qn =>
      obtain ⟨q1, n⟩ := qn
      simp only [hj] at h
      obtain ⟨h1, h2⟩ := passes_sound N q1 (f + n) q F h
      refine ⟨?_, by omega⟩
      have := iter_trans (pass_sound p q1 n hj) h1
      rwa [show n + (F - (f + n)) = F - f by omega] at this

'''
NATIVE = '''/-- Where the first {NS} passes from the blank-tape frame end (`c/prun.c`, mode `lean`, prints the same). -/
theorem passes_frames : passes {N} (Ph.z 0 0 2) 0 = some ({st}, {F}) := by
  native_decide

/-- **No halt in the first {FS} frames** of the run from blank tape. -/
theorem no_halt_passes : ∀ i, i < {F} → ∀ q, iter i (Ph.z 0 0 2) = some q → next q ≠ none := by
  have h := (passes_sound _ _ _ _ _ passes_frames).1
  exact not_none_before _ _ _ h

'''
HEAD = '''import Jump

/-!
# 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD: passes, from one zigzag start to the next

Generated by `py/gen_pass.py`; do not edit.  A zigzag start is `y(a, j, r)` or `Y(a, j, r)` with `a ≥ 3`, `r ≥ 2`.
Write `a = 3q + e`.  Away from the line `r = q` (where both blocks run out together) the run from one zigzag start
to the next is one affine map, for all sizes:

* drain, `r + 1 ≤ q`: `t(a, j, r)` → `t(a − 3r + 1, 0, 4r + 2j + 2)` (`drain_y`, `drain_Y`);
* growth, `q + 7 ≤ r`: `t(a, j, r)` → `t'(4q + 2j + c, 0, r − q − d)` with `(t', c, d)` by `t`, `e` and the parity of
  `j` (`grow_*`), except `Y` with `e = 2`: `Y(a, j, r)` → `y(5, j + 2q + 2, r − q − 1)` (`grow_Y2`).

Each theorem is a chain of the lemmas of `Jump.lean` (zigzags, sweeps, single cases of `next`) and states its exact
frame count.  `fast` is these 13 cases, `pass` is `fast` where it applies and `jump` elsewhere (near the boundary,
where the halting rows are, and off zigzag starts), `pass_sound`: each pass is that many frames of `next`.
`passes_frames` runs `10^8` passes from the blank-tape frame by `native_decide`; `no_halt_passes`: none of the
frames they cover halts.

In the run from blank tape almost every pass is one of the 13 cases: of the first `2 * 10^10` zigzag starts only
about 50 are within 6 of the boundary (`c/prun.c`).
-/

namespace H97525

theorem iter_cast {n n' : Nat} {p p' q q' : Ph} (h : iter n p = some q) (hn : n = n') (hp : p = p') (hq : q = q') :
    iter n' p' = some q' := by subst hn hp hq; exact h

'''
out = [HEAD]
info = []
for c in CASES:
    nmz, thm, inf = gen_case(c)
    out.append(thm + '\n')
    info.append((nmz, inf))
out.append(TAIL)
lean = subprocess.run([FRUN, 'lean', str(NPASS)], capture_output=True, text=True).stdout.strip()
st_, fr_ = lean.split('= some (')[1].rstrip(')').rsplit(', ', 1)
out.append(NATIVE.format(N=NPASS, NS=f'{NPASS:,}', st=st_, F=fr_, FS=f'{int(fr_):,}'))
out.append('end H97525\n')
open(sys.argv[2] if len(sys.argv) > 2 else 'Pass.lean', 'w').write(''.join(out))
for nmz, inf in info: print(nmz, inf[2])
