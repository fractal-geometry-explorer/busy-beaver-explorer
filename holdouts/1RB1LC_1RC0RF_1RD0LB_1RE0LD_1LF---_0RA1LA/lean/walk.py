"""Generate Walk.lean: the whole reset table of 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA as one map, and the theorem
that the machine halts from blank tape exactly when the walk of that map reaches a halting class.

usage: python3 walk.py   (writes Walk.lean next to this script)

The rows are read from the statements of the rules in NearEmpty.lean, Level3.lean and BlankRun.lean (the tail `1001`
of level 0), so the map is the proved table and nothing else.  Each rule `X (n : Nat) : steps K (cfg L r T) = some
(cfg N' m' T')` (or `X_halts (n : Nat) : Halts trans (cfg L r T)`) becomes a row: from (N, r, T) with N of the form L
the walk goes to (N', m', T'), or to `loop` when T' is the loop record `s0` with m' = 0, or to `halt`.
"""
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = ["NearEmpty.lean", "Level3.lean", "BlankRun.lean"]
SHORT = {"tl 0 s0": "t1001", "s0": "s0", "x3": "x3", "tl 0 y": "y0", "s2": "s2b", "z1": "z1", "z2": "z2",
         "x4": "x4", "z3": "z3", "z4": "z4"}
RESTRICT = {"z1": 1, "z2": 0, "z3": 1, "z4": 1, "s0": 1}   # the only m with which these tails occur
NEED = [4, 1, 4, 3, 2]


def atoms(s):
    """Split `A B C` into balanced atoms."""
    out, depth, cur = [], 0, ""
    for ch in s.strip():
        if ch == " " and depth == 0:
            if cur:
                out.append(cur)
            cur = ""
            continue
        depth += ch == "("
        depth -= ch == ")"
        cur += ch
    if cur:
        out.append(cur)
    return out


def unpar(s):
    s = s.strip()
    while s.startswith("(") and s.endswith(")"):
        d, ok = 0, True
        for i, ch in enumerate(s):
            d += ch == "("
            d -= ch == ")"
            if d == 0 and i < len(s) - 1:
                ok = False
                break
        if not ok:
            break
        s = s[1:-1].strip()
    return s


def tail_of(term, m=None):
    """('short', code) | ('long', suffix, count-expr) | ('loop',)"""
    t = unpar(term)
    if t == "s0" and m == "0":
        return ("loop",)
    if t in SHORT:
        return ("short", SHORT[t])
    mt = re.fullmatch(r"tl (\S+|\(.*\)) (s1|s2|s3)", t)
    if mt:
        return ("long", mt.group(2), unpar(mt.group(1)))
    raise ValueError(term)


def cfg_parts(s):
    a = atoms(s)
    assert a[0] == "cfg", s
    return unpar(a[1]), unpar(a[2]), a[3]


def lhs_form(L, var):
    """N = L: ('n', c) for n + c, ('a', c) for 2 * a + c."""
    if var == "n":
        m = re.fullmatch(r"n(?: \+ (\d+))?", L)
        return ("n", int(m.group(1) or 0))
    m = re.fullmatch(r"2 \* a(?: \+ (\d+))?", L)
    return ("a", int(m.group(1) or 0))


def rules():
    out = {}
    for f in SRC:
        txt = open(os.path.join(HERE, f)).read()
        found = {}
        for mt in re.finditer(r"theorem (\w+) \((n|a) : Nat\) :\s*steps \(([^()]*)\) \((cfg .*?)\) = some \((cfg .*?)\) :=",
                              txt):
            name, var, K, lhs, rhs = mt.groups()
            if name in ("loop5",):
                continue
            L, r, T = cfg_parts(lhs)
            N2, m2, T2 = cfg_parts(rhs)
            T = tail_of(T)
            if T[0] == "long" and not T[2].isdigit():
                continue
            found.setdefault((T, int(r)), []).append(("go", name, var, lhs_form(L, var), N2, m2, tail_of(T2, m2)))
        for mt in re.finditer(r"theorem (\w+)_halts \((n|a) : Nat\) : Halts trans \((cfg .*?)\) :=", txt):
            name, var, lhs = mt.groups()
            L, r, T = cfg_parts(lhs)
            found.setdefault((tail_of(T), int(r)), []).append(("halt", name + "_halts", var, lhs_form(L, var)))
        for k, v in found.items():
            if k not in out:
                out[k] = v
    return out


def expr(e, var, form):
    """The rhs expression e (in the rule's variable) in terms of the row's N."""
    _, c = form
    if var == "n":
        sub = "N" if c == 0 else f"(N - {c})"
    else:
        sub = f"((N - {c}) / 2)"
    return re.sub(r"\b" + var + r"\b", sub, e)


def tl_lean(T, var=None, form=None):
    if T[0] == "short":
        return f".short .{T[1]}"
    cnt = T[2] if var is None else expr(T[2], var, form)
    return f".long .{T[1]} ({cnt})"


def result(rule):
    if rule[0] == "halt":
        return ".halt"
    _, name, var, form, N2, m2, T2 = rule
    if T2[0] == "loop":
        return ".loop"
    return f".go ({expr(N2, var, form)}, {expr(m2, var, form)}, {tl_lean(T2, var, form)})"


def proof(rule, indent):
    """Proof of `Good (N, r, T) <result>` in the branch where N has the rule's form."""
    p = " " * indent
    var, form = rule[2], rule[3]
    c = form[1]
    lines = []
    if var == "n":
        if c:
            lines.append(f"{p}obtain ⟨n, rfl⟩ : ∃ n, N = n + {c} := ⟨N - {c}, by omega⟩")
            lines.append(f"{p}try simp only [Nat.add_sub_cancel]")
        v = "n" if c else "N"
    else:
        lines.append(f"{p}obtain ⟨a, rfl⟩ : ∃ a, N = 2 * a + {c} := ⟨(N - {c}) / 2, by omega⟩")
        lines.append(f"{p}try rw [show (2 * a + {c} - {c}) / 2 = a by omega]")
        v = "a"
    if rule[0] == "halt":
        lines.append(f"{p}exact {rule[1]} {v}")
    elif rule[6][0] == "loop":
        lines.append(f"{p}exact runs_of_reach ({rule[1]} {v}) (loop_runs' _ (by omega))")
    else:
        T2 = rule[6]
        okp = "rfl" if T2[0] == "short" and T2[1] in RESTRICT else "trivial"
        lines.append(f"{p}exact ⟨⟨_, by omega, {rule[1]} {v}⟩, by omega, {okp}⟩")
    return lines


def row(key, rs):
    """The row function and its lemma."""
    T, r = key
    nm = (f"row_{T[1]}_{T[2]}_{r}" if T[0] == "long" else f"row_{T[1]}_{r}")
    lhsT = tl_lean(T)
    d, pf = [f"def {nm} (N : Nat) : Res :="], [f"theorem {nm}_good (N : Nat) (hN : 2 ≤ N) : Good (N, {r}, {lhsT}) ({nm} N) := by",
                                               f"  unfold {nm}"]
    if len(rs) == 1:
        rule = rs[0]
        assert rule[3][0] == "n", (key, rs)
        d.append(f"  {result(rule)}")
        pf += proof(rule, 2)
    else:
        ev = [x for x in rs if x[3][1] % 2 == 0]
        od = [x for x in rs if x[3][1] % 2 == 1]
        assert len(ev) == 1 and len(od) == 1 and all(x[3][0] == "a" for x in rs), (key, rs)
        e, o = ev[0], od[0]
        d.append(f"  if N % 2 = 0 then {result(e)} else {result(o)}")
        pf.append("  split")
        for x in (e, o):
            pf.append("  · rename_i h0")
            pf += proof(x, 4)
    return nm, "\n".join(d) + "\n", "\n".join(pf) + "\n"


HEAD = """import Level3

/-!
# 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA: the whole table as one map, and halting as a question about it

Generated by `walk.py` from the statements of the rules in `NearEmpty.lean`, `Level3.lean` and `BlankRun.lean`; do not
edit by hand.

A *record* `(n, m, T)` stands for `cfg n m (tape T)`, where the tail T is a long tail `tl t s` of one of the suffixes
`s1`, `s2`, `s3` (levels 1 to 3) or one of the ten short tails of the closed list (`tl 0 s0` = `1001` of level 0,
`s0`, `x3`, `tl 0 y`, `s2` right after the d block, `z1` ... `z4`, `x4`).  `step` is the proved table: with m ≥ 5 the
periods (`periods_exact`), with m < 5 and enough words `1110` the generic reset (`reset_spec`, any suffix), and
otherwise the row of the nearly empty or short tail.  A row ends at another record (`go`), at the loop record
(`loop`: never halts) or in a halting class (`halt`); `stuck` marks what the table does not cover, and `step_good`
shows that from every record with n ≥ 2 and a short tail met with its own m (`ok`) the table covers it.

`halts_iff_walk`: **the machine halts from blank tape if and only if the walk from (17, 0, tl 6805 s1) reaches `halt`**
(the run from blank tape to that record is `blank_to_17`).  The walk is a function of numbers alone; it never
reaches `stuck`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace H66813

open TM

inductive Suf | s1 | s2 | s3
  deriving DecidableEq, Repr

inductive Sh | t1001 | s0 | x3 | y0 | s2b | z1 | z2 | x4 | z3 | z4
  deriving DecidableEq, Repr

inductive Tl | long (s : Suf) (t : Nat) | short (x : Sh)
  deriving DecidableEq, Repr

def Suf.tape : Suf → Tape
  | .s1 => H66813.s1 | .s2 => H66813.s2 | .s3 => H66813.s3

def Tl.tape : Tl → Tape
  | .long s t => tl t s.tape
  | .short .t1001 => tl 0 s0 | .short .s0 => s0 | .short .x3 => x3 | .short .y0 => tl 0 y
  | .short .s2b => s2 | .short .z1 => z1 | .short .z2 => z2 | .short .x4 => x4 | .short .z3 => z3
  | .short .z4 => z4

abbrev W := Nat × Nat × Tl

def cfgW : W → Config
  | (n, m, T) => cfg n m T.tape

inductive Res | go (w : W) | halt | loop | stuck
  deriving DecidableEq, Repr

/-- The tails that occur only with one m. -/
def allowed : Nat → Tl → Prop
  | m, .short .z1 => m = 1 | m, .short .z2 => m = 0 | m, .short .z3 => m = 1 | m, .short .z4 => m = 1
  | m, .short .s0 => m = 1 | _, _ => True

def ok : W → Prop
  | (n, m, T) => 2 ≤ n ∧ allowed m T

/-- Runs for ever. -/
def Runs (c : Config) : Prop := ∀ j, ∃ s, j ≤ s ∧ ∃ d, steps s c = some d

def Good (w : W) : Res → Prop
  | .go w' => (∃ s, 0 < s ∧ steps s (cfgW w) = some (cfgW w')) ∧ ok w'
  | .halt => Halts trans (cfgW w)
  | .loop => Runs (cfgW w)
  | .stuck => False

theorem runs_of_reach {a : Nat} {c c' : Config} (h : steps a c = some c') (hc : Runs c') : Runs c := by
  intro j
  obtain ⟨s, hs, d, hd⟩ := hc j
  exact ⟨a + s, by omega, d, steps_seq trans h hd⟩

def need : Nat → Nat
  | 0 => 4 | 1 => 1 | 2 => 4 | 3 => 3 | _ => 2

/-! ## The rows of the nearly empty and short tails -/

"""

MID = """
/-! ## The step and its proof -/

theorem resetSteps_pos (n r : Nat) : 0 < resetSteps n r := by
  unfold resetSteps
  split <;> (try split) <;> omega

theorem reset_ne_none {n r t : Nat} (hr : r < 5) (hn : 1 ≤ n) (ht : need r ≤ t) : reset (n, r, t) ≠ none := by
  match r, hr, ht with
  | 0, _, ht => simp only [need] at ht; try simp [reset, ht]
  | 1, _, ht => simp only [need] at ht; try simp [reset, ht]
  | 2, _, ht => simp only [need] at ht; try simp [reset, ht, hn]
  | 3, _, ht => simp only [need] at ht; try simp [reset, ht]
  | 4, _, ht => simp only [need] at ht; try simp [reset, ht]

theorem reset_ge {n r t n' m' t' : Nat} (h : reset (n, r, t) = some (n', m', t')) : 10 ≤ n' := by
  match r, h with
  | 0, h => simp only [reset] at h; split at h <;> simp_all <;> omega
  | 1, h => simp only [reset] at h; split at h <;> simp_all <;> omega
  | 2, h => simp only [reset] at h; split at h <;> simp_all <;> omega
  | 3, h => simp only [reset] at h; split at h <;> simp_all <;> omega
  | 4, h => simp only [reset] at h; split at h <;> simp_all <;> omega
  | r + 5, h => simp [reset] at h

def ofReset (s : Suf) : Option (Nat × Nat × Nat) → Res
  | some (n', m', t') => .go (n', m', .long s t')
  | none => .stuck

def wlong (s : Suf) (n m t : Nat) : Res := if need m ≤ t then ofReset s (reset (n, m, t)) else nearL s m t n

def wstep : W → Res
  | (n, m, .long s t) => if 5 ≤ m then .go (n + 31 * (m / 5), m % 5, .long s t) else wlong s n m t
  | (n, m, .short x) => if 5 ≤ m then .go (n + 31 * (m / 5), m % 5, .short x) else shortRow x m n

theorem periodSteps_pos {q : Nat} (n : Nat) (hq : 0 < q) : 0 < periodSteps q n := by
  have := Nat.mul_pos hq (show 0 < 448 * n + 6952 by omega)
  unfold periodSteps; omega

theorem allowed_mod {m : Nat} {T : Tl} (hm : 5 ≤ m) (h : allowed m T) : allowed (m % 5) T := by
  match T with
  | .long _ _ => trivial
  | .short .t1001 => trivial | .short .x3 => trivial | .short .y0 => trivial | .short .s2b => trivial
  | .short .x4 => trivial
  | .short .z1 => simp only [allowed] at h; omega
  | .short .z2 => simp only [allowed] at h; omega
  | .short .z3 => simp only [allowed] at h; omega
  | .short .z4 => simp only [allowed] at h; omega
  | .short .s0 => simp only [allowed] at h; omega

theorem period_good (n m : Nat) (T : Tl) (hn : 2 ≤ n) (hm : 5 ≤ m) (hal : allowed m T) :
    Good (n, m, T) (.go (n + 31 * (m / 5), m % 5, T)) := by
  refine ⟨⟨periodSteps (m / 5) n, periodSteps_pos n (by omega), ?_⟩, by omega, allowed_mod hm hal⟩
  have e := periods_exact (m / 5) n (m % 5) T.tape
  rw [show m % 5 + 5 * (m / 5) = m by omega] at e
  exact e

theorem long_good (s : Suf) (n m t : Nat) (hn : 2 ≤ n) (hm : m < 5) : Good (n, m, .long s t) (wlong s n m t) := by
  unfold wlong
  by_cases ht : need m ≤ t
  · simp only [ht, ↓reduceIte]
    cases hr : reset (n, m, t) with
    | none => exact absurd hr (reset_ne_none hm (by omega) ht)
    | some x =>
      obtain ⟨n', m', t'⟩ := x
      exact ⟨⟨resetSteps n m, resetSteps_pos n m, reset_spec hr s.tape⟩, by have := reset_ge hr; omega, trivial⟩
  · simp only [ht, ↓reduceIte]
    exact nearL_good s m t n hm (by omega) hn

/-- Every record the table can meet is covered, and each `go` is a run of at least one step to a record of the same
kind. -/
theorem wstep_good (w : W) (h : ok w) : Good w (wstep w) := by
  obtain ⟨n, m, T⟩ := w
  obtain ⟨hn, hal⟩ := h
  cases T with
  | long s t =>
    show Good _ (if 5 ≤ m then _ else _)
    by_cases hm : 5 ≤ m
    · simp only [hm, ↓reduceIte]; exact period_good n m _ hn hm hal
    · simp only [hm, ↓reduceIte]; exact long_good s n m t hn (by omega)
  | short x =>
    show Good _ (if 5 ≤ m then _ else _)
    by_cases hm : 5 ≤ m
    · simp only [hm, ↓reduceIte]; exact period_good n m _ hn hm hal
    · simp only [hm, ↓reduceIte]; exact shortRow_good x m n (by omega) hn hal

/-! ## The walk -/

def runW : Nat → W → Res
  | 0, w => .go w
  | k + 1, w =>
    match runW k w with
    | .go w' => wstep w'
    | r => r

theorem run_go (k : Nat) : ∀ {w w' : W}, ok w → runW k w = .go w' →
    (∃ s, k ≤ s ∧ steps s (cfgW w) = some (cfgW w')) ∧ ok w' := by
  induction k with
  | zero => intro w w' h e; simp only [runW, Res.go.injEq] at e; subst e; exact ⟨⟨0, Nat.le_refl _, rfl⟩, h⟩
  | succ k ih =>
    intro w w' h e
    cases hk : runW k w with
    | go v =>
      simp only [runW, hk] at e
      obtain ⟨⟨s, hs, h1⟩, hv'⟩ := ih h hk
      have g := wstep_good v hv'
      rw [e] at g
      obtain ⟨⟨s', hs', h2⟩, hw'⟩ := g
      exact ⟨⟨s + s', by omega, steps_seq trans h1 h2⟩, hw'⟩
    | halt => simp only [runW, hk] at e; cases e
    | loop => simp only [runW, hk] at e; cases e
    | stuck => simp only [runW, hk] at e; cases e

theorem run_end (k : Nat) : ∀ {w : W}, ok w →
    (runW k w = .halt → Halts trans (cfgW w)) ∧ (runW k w = .loop → Runs (cfgW w)) ∧ runW k w ≠ .stuck := by
  induction k with
  | zero => intro w _; exact ⟨(fun e => by simp [runW] at e), (fun e => by simp [runW] at e), (fun e => by simp [runW] at e)⟩
  | succ k ih =>
    intro w h
    have ihw := ih h
    cases hk : runW k w with
    | go v =>
      obtain ⟨⟨s, _, h1⟩, hv'⟩ := run_go k h hk
      have g := wstep_good v hv'
      simp only [runW, hk]
      refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
      · rw [e] at g; exact halts_of_reach h1 g
      · rw [e] at g; exact runs_of_reach h1 g
      · rw [e] at g; exact g
    | halt =>
      rw [hk] at ihw
      simp only [runW, hk]
      exact ⟨(fun _ => ihw.1 rfl), (fun e => nomatch e), (fun e => nomatch e)⟩
    | loop =>
      rw [hk] at ihw
      simp only [runW, hk]
      exact ⟨(fun e => nomatch e), (fun _ => ihw.2.1 rfl), (fun e => nomatch e)⟩
    | stuck => rw [hk] at ihw; exact absurd rfl ihw.2.2

/-- If the walk never reaches `halt`, the machine runs for ever. -/
theorem runs_of_walk {w : W} (h : ok w) (hn : ∀ k, runW k w ≠ .halt) : Runs (cfgW w) := by
  by_cases hl : ∃ k, runW k w = .loop
  · obtain ⟨k, hk⟩ := hl
    exact (run_end k h).2.1 hk
  · intro j
    have e := (run_end j h).2.2
    cases hj : runW j w with
    | go w' => obtain ⟨⟨s, hs, h1⟩, _⟩ := run_go j h hj; exact ⟨s, hs, _, h1⟩
    | halt => exact absurd hj (hn j)
    | loop => exact absurd ⟨j, hj⟩ hl
    | stuck => exact absurd hj e

/-- From a record with n ≥ 2 (and a short tail with its own m): the machine halts exactly when the walk reaches
`halt`. -/
theorem walk_iff {w : W} (h : ok w) : Halts trans (cfgW w) ↔ ∃ k, runW k w = .halt := by
  constructor
  · intro hH
    exact Classical.byContradiction fun hne =>
      never_halts_of_reach (a := 0) rfl (runs_of_walk h (fun k e => hne ⟨k, e⟩)) hH
  · rintro ⟨k, hk⟩
    exact (run_end k h).1 hk

/-- **The machine halts from blank tape if and only if the walk from (17, 0, tl 6805 s1) reaches a halting class.**
-/
theorem halts_iff_walk : Halts trans init ↔ ∃ k, runW k (17, 0, .long .s1 6805) = .halt := by
  have h0 : ok (17, 0, .long .s1 6805) := ⟨by omega, trivial⟩
  rw [← walk_iff h0]
  constructor
  · intro hH
    exact Classical.byContradiction fun hne =>
      never_halts_of_reach blank_to_17 (runs_of_walk h0 (fun k e => hne ((walk_iff h0).2 ⟨k, e⟩))) hH
  · exact halts_of_reach blank_to_17

end H66813
"""


def main():
    rs = rules()
    defs, lemmas, longs, shorts = [], [], [], []
    for key in sorted(rs, key=str):
        nm, d, pf = row(key, rs[key])
        defs.append(d)
        lemmas.append(pf)
        (longs if key[0][0] == "long" else shorts).append((key, nm))
    # dispatch
    nl = ["def nearL : Suf → Nat → Nat → Nat → Res"]
    for (T, r), nm in longs:
        nl.append(f"  | .{T[1]}, {r}, {T[2]}, N => {nm} N")
    nl.append("  | _, _, _, _ => .stuck")
    sr = ["def shortRow : Sh → Nat → Nat → Res"]
    for (T, r), nm in shorts:
        sr.append(f"  | .{T[1]}, {r}, N => {nm} N")
    sr.append("  | _, _, _ => .stuck")
    nlg = ["theorem nearL_good (s : Suf) (r t N : Nat) (hr : r < 5) (ht : t < need r) (hN : 2 ≤ N) :",
           "    Good (N, r, .long s t) (nearL s r t N) := by",
           "  match s, r, t, hr, ht with"]
    names = {(k[0][1], k[1], int(k[0][2])): nm for k, nm in longs}
    for sf in ("s1", "s2", "s3"):
        for r in range(5):
            for t in range(NEED[r]):
                nlg.append(f"  | .{sf}, {r}, {t}, _, _ => exact {names[(sf, r, t)]}_good N hN")
            nlg.append(f"  | .{sf}, {r}, t + {NEED[r]}, _, ht => simp only [need] at ht; omega")
    nlg.append("  | _, r + 5, _, hr, _ => omega")
    nlg = "\n".join(nlg) + "\n"
    snames = {(k[0][1], k[1]): nm for k, nm in shorts}
    srg = ["theorem shortRow_good (x : Sh) (r N : Nat) (hr : r < 5) (hN : 2 ≤ N) (hal : allowed r (.short x)) :",
           "    Good (N, r, .short x) (shortRow x r N) := by",
           "  match x, r, hr, hal with"]
    for x in SHORT.values():
        for r in range(5):
            if (x, r) in snames:
                srg.append(f"  | .{x}, {r}, _, _ => exact {snames[(x, r)]}_good N hN")
            else:
                srg.append(f"  | .{x}, {r}, _, hal => simp only [allowed] at hal; omega")
    srg.append("  | _, r + 5, hr, _ => omega")
    srg = "\n".join(srg) + "\n"
    covered = {(k[0][1], k[1]) for k, _ in shorts}
    print(f"{len(rs)} rows: {len(longs)} nearly empty, {len(shorts)} short")
    for T in SHORT.values():
        for r in range(5):
            if (T, r) not in covered and RESTRICT.get(T, r) == r:
                print("missing short row", T, r)
    for s in ("s1", "s2", "s3"):
        for r in range(5):
            for t in range(NEED[r]):
                if not any(k == (("long", s, str(t)), r) for k, _ in longs):
                    print("missing near row", s, r, t)
    txt = HEAD + "\n".join(defs) + "\n" + "\n".join(lemmas) + "\n" + "\n".join(nl) + "\n\n" + "\n".join(sr) + "\n\n" + \
        nlg + "\n" + srg + MID
    open(os.path.join(HERE, "Walk.lean"), "w").write(txt)


if __name__ == "__main__":
    main()
