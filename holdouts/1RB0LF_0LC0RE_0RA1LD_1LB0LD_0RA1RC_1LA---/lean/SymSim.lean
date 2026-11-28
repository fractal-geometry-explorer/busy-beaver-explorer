import TM.RLE

/-!
# The excursion simulator of `ExcSim.lean`, with symbolic counts

`ExcSim.lean` runs a tail excursion on a side of runs `(w, n)` with numbers `n`.  Here a count is a linear form
`c + Σ aᵢ·xᵢ` (`Lin`, integer coefficients) in variables `xᵢ`, so one run of the simulator stands for a whole family
of tapes.  The simulator is *concolic*: it is given the values `env₀` of one member of the family, and wherever the
run depends on a count with variables (whether a run is empty when a cell is taken from it, whether a sum of two
counts may be formed) it decides at `env₀` and records the linear condition it used (`Holds env cs`: every form of
`cs` is `≥ 0`).  Each move is proved for **every** valuation `env` that satisfies the recorded conditions, every tape
`L` on the left (never read) and every tape `R` on the right beyond the side (never read either, unless the side is
marked as ending in blank tape, `endB`).  The number of steps of a move may depend on `env`, not on `L`.

* `popB_some`, `popB_none`, `peelB_spec`, `nrm_spec`, `rc_spec`: the side operations;
* `xcrossR_spec`, `xcrossL_spec`, `xstep_spec`, `xmove_spec`, `xrun_spec`: the moves and the run;
* `exc_spec`: a checked excursion, for every `env` satisfying the conditions;
* `preL_spec`: cells written in front of a side.

As in `ExcSim.lean`, which move is tried when is unverified search; a bad choice can only make the run fail.
-/

namespace TM
namespace SX

/-! ## Linear forms -/

abbrev Terms := List (Nat × Int)

/-- `Σ a · env v`. -/
def evT (env : Nat → Int) : Terms → Int
  | [] => 0
  | (v, a) :: l => a * env v + evT env l

/-- The sum of two term lists sorted by variable (kept sorted, zero coefficients dropped). -/
def addT : Terms → Terms → Terms
  | [], b => b
  | a :: as, [] => a :: as
  | (v, x) :: a, (w, y) :: b =>
    if v < w then (v, x) :: addT a ((w, y) :: b)
    else if w < v then (w, y) :: addT ((v, x) :: a) b
    else if x + y = 0 then addT a b else (v, x + y) :: addT a b
termination_by a b => a.length + b.length

theorem evT_addT (env : Nat → Int) (a b : Terms) : evT env (addT a b) = evT env a + evT env b := by
  fun_induction addT a b with
  | case1 b => simp [evT]
  | case2 a as => simp [evT]
  | case3 v x a w y b h ih => simp only [evT, ih]; omega
  | case4 v x a w y b h1 h2 ih => simp only [evT, ih]; omega
  | case5 v x a w y b h1 h2 h3 ih =>
    have e : v = w := by omega
    subst e
    simp only [evT, ih]
    have : x * env v + y * env v = 0 := by rw [← Int.add_mul, h3, Int.zero_mul]
    omega
  | case6 v x a w y b h1 h2 h3 ih =>
    have e : v = w := by omega
    subst e
    simp only [evT, ih, Int.add_mul]
    omega

/-- A count `c + Σ a · x_v`. -/
structure Lin where
  c : Int
  t : Terms
  deriving DecidableEq, Hashable, Repr, Inhabited

namespace Lin

def ev (env : Nat → Int) (e : Lin) : Int := e.c + evT env e.t

/-- The count as a number of copies (`0` when the form is negative). -/
def cnt (env : Nat → Int) (e : Lin) : Nat := (e.ev env).toNat

def k (n : Nat) : Lin := ⟨n, []⟩
def var (i : Nat) : Lin := ⟨0, [(i, 1)]⟩
def add (a b : Lin) : Lin := ⟨a.c + b.c, addT a.t b.t⟩
def addc (a : Lin) (d : Int) : Lin := ⟨a.c + d, a.t⟩
def neg (a : Lin) : Lin := ⟨-a.c, a.t.map (fun p => (p.1, -p.2))⟩
def scale (s : Int) (a : Lin) : Lin := if s = 0 then ⟨0, []⟩ else ⟨s * a.c, a.t.map (fun p => (p.1, s * p.2))⟩

/-- Substitute the form `m v` for each variable `v`. -/
def substT (m : Nat → Lin) (c : Int) : Terms → Lin
  | [] => ⟨c, []⟩
  | (v, x) :: l => add (scale x (m v)) (substT m c l)

def subst (m : Nat → Lin) (e : Lin) : Lin := substT m e.c e.t

@[simp] theorem ev_k (env : Nat → Int) (n : Nat) : (k n).ev env = n := by simp [ev, k, evT]
@[simp] theorem cnt_k (env : Nat → Int) (n : Nat) : (k n).cnt env = n := by simp [cnt]
@[simp] theorem ev_var (env : Nat → Int) (i : Nat) : (var i).ev env = env i := by simp [ev, var, evT]
@[simp] theorem ev_add (env : Nat → Int) (a b : Lin) : (add a b).ev env = a.ev env + b.ev env := by
  simp only [ev, add, evT_addT]; omega
@[simp] theorem ev_addc (env : Nat → Int) (a : Lin) (d : Int) : (addc a d).ev env = a.ev env + d := by
  simp only [ev, addc]; omega

theorem evT_neg (env : Nat → Int) : ∀ (l : Terms), evT env (l.map (fun p => (p.1, -p.2))) = -evT env l
  | [] => by simp [evT]
  | (v, a) :: l => by simp only [List.map, evT, evT_neg env l, Int.neg_mul]; omega

@[simp] theorem ev_neg (env : Nat → Int) (a : Lin) : (neg a).ev env = -a.ev env := by
  simp only [ev, neg, evT_neg]; omega

theorem evT_scale (env : Nat → Int) (s : Int) : ∀ (l : Terms),
    evT env (l.map (fun p => (p.1, s * p.2))) = s * evT env l
  | [] => by simp [evT]
  | (v, a) :: l => by simp only [List.map, evT, evT_scale env s l, Int.mul_add, Int.mul_assoc]

@[simp] theorem ev_scale (env : Nat → Int) (s : Int) (a : Lin) : (scale s a).ev env = s * a.ev env := by
  unfold scale
  split
  · rename_i h; subst h; simp [ev, evT]
  · simp only [ev, evT_scale, Int.mul_add]

theorem ev_substT (env : Nat → Int) (m : Nat → Lin) (c : Int) : ∀ (l : Terms),
    (substT m c l).ev env = c + evT (fun v => (m v).ev env) l
  | [] => by simp [substT, ev, evT]
  | (v, x) :: l => by simp only [substT, ev_add, ev_scale, ev_substT env m c l, evT]; omega

theorem ev_subst (env : Nat → Int) (m : Nat → Lin) (e : Lin) :
    (subst m e).ev env = e.ev (fun v => (m v).ev env) := by
  show (substT m e.c e.t).ev env = _
  rw [ev_substT]; rfl

theorem cnt_add {env : Nat → Int} {a b : Lin} (ha : 0 ≤ a.ev env) (hb : 0 ≤ b.ev env) :
    (add a b).cnt env = a.cnt env + b.cnt env := by
  simp only [cnt, ev_add]; exact Int.toNat_add ha hb

theorem cnt_pred {env : Nat → Int} {a : Lin} (h : 0 ≤ (addc a (-1)).ev env) :
    a.cnt env = (addc a (-1)).cnt env + 1 := by
  simp only [cnt, ev_addc] at *
  omega

theorem cnt_of_nonpos {env : Nat → Int} {a : Lin} (h : a.ev env ≤ 0) : a.cnt env = 0 := by
  simp only [cnt]; omega

end Lin

/-- Every form of `cs` is `≥ 0` at `env`. -/
def Holds (env : Nat → Int) (cs : List Lin) : Prop := ∀ e ∈ cs, 0 ≤ e.ev env

theorem Holds.nil (env : Nat → Int) : Holds env [] := fun _ h => by cases h

theorem holds_append {env : Nat → Int} {a b : List Lin} : Holds env (a ++ b) ↔ Holds env a ∧ Holds env b := by
  simp only [Holds, List.mem_append]
  constructor
  · intro h; exact ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩
  · intro ⟨h1, h2⟩ e he; rcases he with he | he; exact h1 e he; exact h2 e he

theorem Holds.left {env : Nat → Int} {a b : List Lin} (h : Holds env (a ++ b)) : Holds env a :=
  (holds_append.1 h).1
theorem Holds.right {env : Nat → Int} {a b : List Lin} (h : Holds env (a ++ b)) : Holds env b :=
  (holds_append.1 h).2

theorem Holds.single {env : Nat → Int} {e : Lin} (h : Holds env [e]) : 0 ≤ e.ev env := h e (by simp)

/-! ## Sides with symbolic counts -/

abbrev SSide := List (List Bool × Lin)

/-- The side in front of the tape `b`, at `env`. -/
def den (env : Nat → Int) (b : Tape) : SSide → Tape
  | [] => b
  | (w, n) :: s => rep (n.cnt env) w (den env b s)

@[simp] theorem den_nil (env : Nat → Int) (b : Tape) : den env b [] = b := rfl
@[simp] theorem den_cons (env : Nat → Int) (b : Tape) (w : List Bool) (n : Lin) (s : SSide) :
    den env b ((w, n) :: s) = rep (n.cnt env) w (den env b s) := rfl

theorem den_append (env : Nat → Int) (b : Tape) : ∀ (s t : SSide), den env b (s ++ t) = den env (den env b t) s
  | [], _ => rfl
  | (w, n) :: s, t => by simp [den_append env b s t]

/-- Literal cells in front. -/
def pushCells : List Bool → SSide → SSide
  | [], s => s
  | a :: u, s => ([a], Lin.k 1) :: pushCells u s

theorem den_pushCells (env : Nat → Int) (b : Tape) (u : List Bool) (s : SSide) :
    den env b (pushCells u s) = app u (den env b s) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [pushCells, ih, rep_one]

/-! ## Decisions at `env₀` -/

section
variable (env₀ : Nat → Int)

/-- Is the count `n` zero?  Decided at `env₀` for a form with variables, with the condition used. -/
def isZ (n : Lin) : Bool × List Lin :=
  if n.t.isEmpty then (decide (n.c ≤ 0), [])
  else if n.ev env₀ ≤ 0 then (true, [n.neg]) else (false, [n.addc (-1)])

theorem isZ_true {n : Lin} {cs : List Lin} (h : isZ env₀ n = (true, cs)) {env : Nat → Int} (hc : Holds env cs) :
    n.cnt env = 0 := by
  unfold isZ at h
  split at h
  · rename_i he
    simp only [Prod.mk.injEq, decide_eq_true_eq] at h
    obtain ⟨h1, rfl⟩ := h
    apply Lin.cnt_of_nonpos
    have : n.t = [] := List.isEmpty_iff.1 he
    simp [Lin.ev, this, evT]; exact h1
  · split at h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have := hc.single
      simp only [Lin.ev_neg] at this
      exact Lin.cnt_of_nonpos (by omega)
    · simp at h

theorem isZ_false {n : Lin} {cs : List Lin} (h : isZ env₀ n = (false, cs)) {env : Nat → Int} (hc : Holds env cs) :
    n.cnt env = (n.addc (-1)).cnt env + 1 := by
  unfold isZ at h
  split at h
  · rename_i he
    simp only [Prod.mk.injEq, decide_eq_false_iff_not] at h
    obtain ⟨h1, rfl⟩ := h
    apply Lin.cnt_pred
    have : n.t = [] := List.isEmpty_iff.1 he
    simp [Lin.ev, Lin.addc, this, evT]; omega
  · split at h
    · simp at h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact Lin.cnt_pred hc.single

/-- A run in front, dropped when its count is a constant `≤ 0`. -/
def rzS (w : List Bool) (n : Lin) (s : SSide) : SSide :=
  if n.t.isEmpty ∧ n.c ≤ 0 then s else (w, n) :: s

theorem den_rzS (env : Nat → Int) (b : Tape) (w : List Bool) (n : Lin) (s : SSide) :
    den env b (rzS w n s) = rep (n.cnt env) w (den env b s) := by
  unfold rzS
  split
  · rename_i h
    obtain ⟨h1, h2⟩ := h
    have : n.t = [] := List.isEmpty_iff.1 h1
    have : n.cnt env = 0 := Lin.cnt_of_nonpos (by simp [Lin.ev, this, evT]; exact h2)
    rw [this]; rfl
  · rfl

/-- The first cell and the rest (`none` at the end of the side: then the side stands for its base tape); with the
conditions used. -/
def popB : SSide → Option (Bool × SSide) × List Lin
  | [] => (none, [])
  | ([], _) :: s => popB s
  | (a :: w, n) :: s =>
    match isZ env₀ n with
    | (true, c1) =>
      let p := popB s
      (p.1, c1 ++ p.2)
    | (false, c1) => (some (a, pushCells w (rzS (a :: w) (n.addc (-1)) s)), c1)

theorem popB_spec : ∀ (s : SSide) {env : Nat → Int}, Holds env (popB env₀ s).2 → ∀ b,
    (∀ a s', (popB env₀ s).1 = some (a, s') → den env b s = cons a (den env b s')) ∧
    ((popB env₀ s).1 = none → den env b s = b)
  | [], env, _, b => ⟨fun _ _ h => by simp [popB] at h, fun _ => rfl⟩
  | ([], n) :: s, env, hc, b => by
    simp only [popB] at hc ⊢
    simp only [den_cons, rep_nil_word]
    exact popB_spec s hc b
  | (a :: w, n) :: s, env, hc, b => by
    simp only [popB] at hc ⊢
    cases ez : isZ env₀ n with
    | mk z c1 =>
      cases z with
      | true =>
        rw [ez] at hc
        simp only at hc ⊢
        have h0 := isZ_true env₀ ez hc.left
        have ih := popB_spec s hc.right b
        simp only [den_cons, h0, rep_zero]
        exact ih
      | false =>
        rw [ez] at hc
        simp only at hc ⊢
        have h1 := isZ_false env₀ ez hc
        refine ⟨fun a' s' h => ?_, fun h => by cases h⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [den_cons, h1, rep_succ, den_pushCells, den_rzS, app_cons]

theorem popB_some {s : SSide} {a : Bool} {s' : SSide} {cs : List Lin} (h : popB env₀ s = (some (a, s'), cs))
    {env : Nat → Int} (hc : Holds env cs) (b : Tape) : den env b s = cons a (den env b s') := by
  have := popB_spec env₀ s (env := env) (by rw [h]; exact hc) b
  rw [h] at this
  exact this.1 a s' rfl

theorem popB_none {s : SSide} {cs : List Lin} (h : popB env₀ s = (none, cs))
    {env : Nat → Int} (hc : Holds env cs) (b : Tape) : den env b s = b := by
  have := popB_spec env₀ s (env := env) (by rw [h]; exact hc) b
  rw [h] at this
  exact this.2 rfl

/-- The first `j` cells, or `none` if the side has fewer. -/
def peelB : Nat → SSide → Option (List Bool × SSide × List Lin)
  | 0, s => some ([], s, [])
  | j + 1, s =>
    match popB env₀ s with
    | (none, _) => none
    | (some (a, s1), c1) =>
      match peelB j s1 with
      | none => none
      | some (u, s2, c2) => some (a :: u, s2, c1 ++ c2)

theorem peelB_spec : ∀ (j : Nat) (s : SSide) (u : List Bool) (s' : SSide) (cs : List Lin),
    peelB env₀ j s = some (u, s', cs) → ∀ {env : Nat → Int}, Holds env cs → ∀ b, den env b s = app u (den env b s')
  | 0, s, u, s', cs, h, env, _, b => by simp [peelB] at h; obtain ⟨rfl, rfl, -⟩ := h; rfl
  | j + 1, s, u, s', cs, h, env, hc, b => by
    simp only [peelB] at h
    cases e : popB env₀ s with
    | mk p c1 =>
      rw [e] at h
      cases p with
      | none => cases h
      | some p =>
        obtain ⟨a, s1⟩ := p
        simp only at h
        cases e2 : peelB env₀ j s1 with
        | none => rw [e2] at h; cases h
        | some p2 =>
          obtain ⟨u', s2, c2⟩ := p2
          rw [e2] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          rw [popB_some env₀ e hc.left b, peelB_spec j s1 u' s2 c2 e2 hc.right b]
          rfl

end

/-- The first `j` cells when they are literal runs `([b], 1)`, else `none` (no decision, no condition). -/
def peelLB : Nat → SSide → Option (List Bool × SSide)
  | 0, s => some ([], s)
  | j + 1, ([b], n) :: s =>
    if n = Lin.k 1 then
      match peelLB j s with
      | some (u, s') => some (b :: u, s')
      | none => none
    else none
  | _ + 1, _ => none

theorem peelLB_spec (env : Nat → Int) (b0 : Tape) : ∀ (j : Nat) (s : SSide) (u : List Bool) (s' : SSide),
    peelLB j s = some (u, s') → den env b0 s = app u (den env b0 s')
  | 0, s, u, s', h => by simp [peelLB] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | j + 1, [], u, s', h => by simp [peelLB] at h
  | j + 1, ([], n) :: s, u, s', h => by simp [peelLB] at h
  | j + 1, (_ :: _ :: _, n) :: s, u, s', h => by simp [peelLB] at h
  | j + 1, ([c], n) :: s, u, s', h => by
    simp only [peelLB] at h
    split at h
    · rename_i hn
      subst hn
      cases e : peelLB j s with
      | none => rw [e] at h; cases h
      | some p =>
        obtain ⟨u', s''⟩ := p
        rw [e] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [peelLB_spec env b0 j s u' s'' e]
    · cases h

/-- May the count `n` be added to another one: a form with variables (then `n ≥ 0` is recorded), or a constant `≥ 0`. -/
def okC (n : Lin) : Bool := !n.t.isEmpty || decide (0 ≤ n.c)
def nnC (n : Lin) : List Lin := if n.t.isEmpty then [] else [n]

theorem nn_of {env : Nat → Int} {n : Lin} (h : okC n = true) (hc : Holds env (nnC n)) : 0 ≤ n.ev env := by
  unfold okC at h
  unfold nnC at hc
  split at hc
  · rename_i he
    have : n.t = [] := List.isEmpty_iff.1 he
    simp only [he, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
    simp [Lin.ev, this, evT]; exact h
  · exact hc.single

/-- A run in front, merged with the first run when that has the same word. -/
def rc (w : List Bool) (n : Lin) (s : SSide) : SSide × List Lin :=
  match s with
  | (w', m) :: s' => if w' = w ∧ okC n = true ∧ okC m = true then ((w, n.add m) :: s', nnC n ++ nnC m)
      else ((w, n) :: s, [])
  | [] => ([(w, n)], [])

theorem rc_spec {env : Nat → Int} (b : Tape) (w : List Bool) (n : Lin) (s : SSide) (hc : Holds env (rc w n s).2) :
    den env b (rc w n s).1 = rep (n.cnt env) w (den env b s) := by
  unfold rc at hc ⊢
  match s with
  | [] => rfl
  | (w', m) :: s' =>
    simp only at hc ⊢
    split
    · rename_i h
      obtain ⟨rfl, h1, h2⟩ := h
      rw [if_pos ⟨rfl, h1, h2⟩] at hc
      simp only [den_cons]
      rw [Lin.cnt_add (nn_of h1 hc.left) (nn_of h2 hc.right), rep_add]
    · rfl

/-- Fold literal cells in front into a run of one of the words `ws` (as `nrm` of `ExcSim.lean`). -/
def nrmGo : List (List Bool) → SSide → SSide × List Lin
  | [], s => (s, [])
  | w :: ws', s =>
    match peelLB w.length s with
    | some (u, s1) =>
      if u = w then
        match s1 with
        | (w', m) :: r =>
          if w' = w ∧ okC m = true then ((w, m.addc 1) :: r, nnC m) else
            match peelLB w.length s1 with
            | some (u2, s2) => if u2 = w then rc w (Lin.k 2) s2 else nrmGo ws' s
            | none => nrmGo ws' s
        | [] => nrmGo ws' s
      else nrmGo ws' s
    | none => nrmGo ws' s

theorem nrmGo_spec {env : Nat → Int} (b : Tape) : ∀ (ws : List (List Bool)) (s : SSide),
    Holds env (nrmGo ws s).2 → den env b (nrmGo ws s).1 = den env b s
  | [], s, _ => rfl
  | w :: ws', s, hc => by
    unfold nrmGo at hc ⊢
    cases e1 : peelLB w.length s with
    | none => rw [e1] at hc; exact nrmGo_spec b ws' s hc
    | some p =>
      obtain ⟨u, s1⟩ := p
      rw [e1] at hc
      simp only at hc ⊢
      have h1 := peelLB_spec env b _ _ _ _ e1
      by_cases hu : u = w
      · subst hu
        simp only [if_true] at hc ⊢
        match s1, h1, hc with
        | [], h1, hc => exact nrmGo_spec b ws' s hc
        | (w', m) :: r, h1, hc =>
          simp only at hc ⊢
          by_cases hw : w' = u ∧ okC m = true
          · rw [if_pos hw] at hc ⊢
            obtain ⟨rfl, hm⟩ := hw
            have hm0 := nn_of hm hc
            rw [h1]
            simp only [den_cons]
            have : (m.addc 1).cnt env = m.cnt env + 1 := by
              simp only [Lin.cnt, Lin.ev_addc]; omega
            rw [this, rep_succ]
          · rw [if_neg hw] at hc ⊢
            cases e3 : peelLB u.length ((w', m) :: r) with
            | none => rw [e3] at hc; exact nrmGo_spec b ws' s hc
            | some p2 =>
              obtain ⟨u2, s2⟩ := p2
              rw [e3] at hc
              simp only at hc ⊢
              by_cases hu2 : u2 = u
              · subst hu2
                simp only [if_true] at hc ⊢
                rw [rc_spec b _ _ _ hc, h1, peelLB_spec env b _ _ _ _ e3]
                simp [rep_succ, rep_zero]
              · rw [if_neg hu2] at hc ⊢; exact nrmGo_spec b ws' s hc
      · rw [if_neg hu] at hc ⊢; exact nrmGo_spec b ws' s hc

def nrm (ws : List (List Bool)) (s : SSide) : SSide × List Lin :=
  match s with
  | (_, n1) :: _ => if n1 = Lin.k 1 then nrmGo ws s else (s, [])
  | [] => (s, [])

theorem nrm_spec {env : Nat → Int} (b : Tape) (ws : List (List Bool)) (s : SSide) (hc : Holds env (nrm ws s).2) :
    den env b (nrm ws s).1 = den env b s := by
  unfold nrm at hc ⊢
  match s with
  | [] => rfl
  | (w, n1) :: s' =>
    simp only at hc ⊢
    split
    · rename_i h; rw [if_pos h] at hc; exact nrmGo_spec b ws _ hc
    · rfl

/-- Cells in front of a side, folded into runs one by one from the far end. -/
def preL (ws : List (List Bool)) : List Bool → SSide → SSide × List Lin
  | [], T => (T, [])
  | a :: w, T =>
    let p := preL ws w T
    let q := nrm ws (([a], Lin.k 1) :: p.1)
    (q.1, q.2 ++ p.2)

theorem preL_spec {env : Nat → Int} (b : Tape) (ws : List (List Bool)) (T : SSide) : ∀ (w : List Bool),
    Holds env (preL ws w T).2 → den env b (preL ws w T).1 = app w (den env b T)
  | [], _ => rfl
  | a :: w, hc => by
    simp only [preL] at hc ⊢
    rw [nrm_spec b ws _ hc.left]
    simp only [den_cons, Lin.cnt_k, rep_one, app_cons, app_nil]
    rw [preL_spec b ws T w hc.right]

/-! ## Configurations and moves -/

/-- A configuration: left side (in front of an unknown tape `L`), right side (in front of `R`), state. -/
structure XS (Q : Type) where
  l : SSide
  r : SSide
  q : Q

variable {Q : Type}

def XS.cfg (env : Nat → Int) (L R : Tape) (c : XS Q) : Cfg Q := ⟨den env L c.l, den env R c.r, c.q⟩

/-- `c` reaches `c'` at every valuation satisfying `cs`, for every `R` (blank if `endB`), in a number of steps that
does not depend on `L`. -/
def Reach (δ : Q → Bool → Option (Bool × Dir × Q)) (endB : Bool) (cs : List Lin) (c : XS Q)
    (F : (Nat → Int) → Tape → Tape → Cfg Q) : Prop :=
  ∀ env, Holds env cs → ∀ R, (endB = true → R = blank) → ∃ n, ∀ L, steps δ n (c.cfg env L R) = some (F env L R)

section
variable [DecidableEq Q] (δ : Q → Bool → Option (Bool × Dir × Q)) (ws : List (List Bool)) (env₀ : Nat → Int)

/-- Cross a run `w^n` on the right, carrying `j` literal cells of the left side. -/
def xcrossR (j : Nat) (c : XS Q) : Option (XS Q × List Lin) :=
  match c.r with
  | (w, n) :: r' =>
    if w.length < 2 then none else
    match peelB env₀ j c.l with
    | none => none
    | some (u, l'', c1) =>
      match findR δ (8 * (w.length + u.length) + 16) 0 (u, w, c.q) with
      | none => none
      | some s =>
        match bsteps δ s (u, w, c.q) with
        | some (ll, [], q') =>
          if q' = c.q ∧ ll.take u.length = u then
            let p := rc (ll.drop u.length) n l''
            some (⟨pushCells u p.1, r', c.q⟩, c1 ++ p.2)
          else none
        | _ => none
  | [] => none

theorem xcrossR_spec (endB : Bool) (j : Nat) (c c' : XS Q) (cs : List Lin) (h : xcrossR δ env₀ j c = some (c', cs)) :
    Reach δ endB cs c (fun env L R => c'.cfg env L R) := by
  intro env hc R _
  obtain ⟨l, r, q⟩ := c
  unfold xcrossR at h
  simp only at h
  match r, h with
  | (w, k) :: r', h =>
    simp only at h
    split at h
    · cases h
    cases ep : peelB env₀ j l with
    | none => rw [ep] at h; cases h
    | some p =>
      obtain ⟨u, l'', c1⟩ := p
      rw [ep] at h
      simp only at h
      cases ef : findR δ (8 * (w.length + u.length) + 16) 0 (u, w, q) with
      | none => rw [ef] at h; cases h
      | some s =>
        rw [ef] at h
        simp only at h
        cases eb : bsteps δ s (u, w, q) with
        | none => rw [eb] at h; cases h
        | some t =>
          obtain ⟨ll, rr, q'⟩ := t
          rw [eb] at h
          match rr, h with
          | [], h =>
            simp only at h
            split at h
            · rename_i hcd
              obtain ⟨hq, hu⟩ := hcd
              subst hq
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hll : ll = u ++ ll.drop u.length := by
                conv => lhs; rw [← List.take_append_drop u.length ll]
                rw [hu]
              have h1 : ∀ L R : Tape, steps δ s ⟨app u L, app w R, q'⟩ =
                  some ⟨app u (app (ll.drop u.length) L), R, q'⟩ := by
                intro L R
                have := bsteps_spec δ s eb L R
                rw [hll, ← app_app] at this
                simpa using this
              refine ⟨k.cnt env * s, fun L => ?_⟩
              have h2 := cross_r δ h1 (k.cnt env) (den env L l'') (den env R r')
              simp only [XS.cfg, den_cons]
              rw [peelB_spec env₀ j l u l'' c1 ep hc.left L, den_pushCells, rc_spec L _ _ _ hc.right]
              exact h2
            · cases h
          | _ :: _, h => cases h

/-- Cross a run `w^n` on the left, carrying `j` literal cells of the right side. -/
def xcrossL (j : Nat) (c : XS Q) : Option (XS Q × List Lin) :=
  match c.l with
  | (w, n) :: l' =>
    if w.length < 2 then none else
    match peelB env₀ j c.r with
    | none => none
    | some (u, r'', c1) =>
      match findL δ c.q u (8 * (w.length + u.length) + 16) 0 (w, u, c.q) with
      | none => none
      | some s =>
        match bsteps δ s (w, u, c.q) with
        | some ([], rr, q') =>
          if q' = c.q ∧ rr.take u.length = u then
            let p := rc (rr.drop u.length) n r''
            some (⟨l', pushCells u p.1, c.q⟩, c1 ++ p.2)
          else none
        | _ => none
  | [] => none

theorem xcrossL_spec (endB : Bool) (j : Nat) (c c' : XS Q) (cs : List Lin) (h : xcrossL δ env₀ j c = some (c', cs)) :
    Reach δ endB cs c (fun env L R => c'.cfg env L R) := by
  intro env hc R _
  obtain ⟨l, r, q⟩ := c
  unfold xcrossL at h
  simp only at h
  match l, h with
  | (w, k) :: l', h =>
    simp only at h
    split at h
    · cases h
    cases ep : peelB env₀ j r with
    | none => rw [ep] at h; cases h
    | some p =>
      obtain ⟨u, r'', c1⟩ := p
      rw [ep] at h
      simp only at h
      cases ef : findL δ q u (8 * (w.length + u.length) + 16) 0 (w, u, q) with
      | none => rw [ef] at h; cases h
      | some s =>
        rw [ef] at h
        simp only at h
        cases eb : bsteps δ s (w, u, q) with
        | none => rw [eb] at h; cases h
        | some t =>
          obtain ⟨ll, rr, q'⟩ := t
          rw [eb] at h
          match ll, h with
          | [], h =>
            simp only at h
            split at h
            · rename_i hcd
              obtain ⟨hq, hu⟩ := hcd
              subst hq
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hrr : rr = u ++ rr.drop u.length := by
                conv => lhs; rw [← List.take_append_drop u.length rr]
                rw [hu]
              have h1 : ∀ L R : Tape, steps δ s ⟨app w L, app u R, q'⟩ =
                  some ⟨L, app u (app (rr.drop u.length) R), q'⟩ := by
                intro L R
                have := bsteps_spec δ s eb L R
                rw [hrr, ← app_app] at this
                simpa using this
              refine ⟨k.cnt env * s, fun L => ?_⟩
              have h2 := cross_l δ h1 (k.cnt env) (den env L l') (den env R r'')
              simp only [XS.cfg, den_cons]
              rw [peelB_spec env₀ j r u r'' c1 ep hc.left R, den_pushCells, rc_spec R _ _ _ hc.right]
              exact h2
            · cases h
          | _ :: _, h => cases h

/-- The result of a move: a configuration, or the exit (state, written cell, right side). -/
abbrev Res (Q : Type) := Sum (XS Q) (Q × Bool × SSide)

def Res.cfg (env : Nat → Int) (L R : Tape) : Res Q → Cfg Q
  | .inl c => c.cfg env L R
  | .inr (s, w, r) => ⟨tail L, cons (L 0) (cons w (den env R r)), s⟩

/-- The cell under the head and the rest of the right side; at the end of the side only if it ends in blank. -/
def popR (endB : Bool) (r : SSide) : Option (Bool × SSide) × List Lin :=
  match popB env₀ r with
  | (some p, c) => (some p, c)
  | (none, c) => (if endB then some (false, []) else none, c)

theorem popR_spec (endB : Bool) (r : SSide) (a : Bool) (r' : SSide) (cs : List Lin)
    (h : popR env₀ endB r = (some (a, r'), cs)) {env : Nat → Int} (hc : Holds env cs) (R : Tape)
    (hR : endB = true → R = blank) : den env R r = cons a (den env R r') := by
  unfold popR at h
  cases e : popB env₀ r with
  | mk p c =>
    rw [e] at h
    cases p with
    | some p =>
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact popB_some env₀ e hc R
    | none =>
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      cases endB with
      | false => simp at h1
      | true =>
        simp only [if_true, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        rw [popB_none env₀ e hc R, hR rfl]
        exact cons_false_blank.symm

/-- One ordinary step; `none` on a halt, or when the head would read past a side that does not end in blank. -/
def xstep (endB : Bool) (c : XS Q) : Option (Res Q × List Lin) :=
  match popR env₀ endB c.r with
  | (none, _) => none
  | (some (a, r2), c0) =>
    match δ c.q a with
    | none => none
    | some (w, .R, s) =>
      let p := nrm ws (([w], Lin.k 1) :: c.l)
      some (.inl ⟨p.1, r2, s⟩, c0 ++ p.2)
    | some (w, .L, s) =>
      match popB env₀ c.l with
      | (none, c1) => some (.inr (s, w, r2), c0 ++ c1)
      | (some (b, l'), c1) =>
        let p := nrm ws (([b], Lin.k 1) :: ([w], Lin.k 1) :: r2)
        some (.inl ⟨l', p.1, s⟩, c0 ++ c1 ++ p.2)

theorem xstep_spec (endB : Bool) (c : XS Q) (x : Res Q) (cs : List Lin) (h : xstep δ ws env₀ endB c = some (x, cs)) :
    Reach δ endB cs c (fun env L R => x.cfg env L R) := by
  intro env hc R hR
  refine ⟨1, fun L => ?_⟩
  obtain ⟨l, r, q⟩ := c
  unfold xstep at h
  simp only at h
  cases ep : popR env₀ endB r with
  | mk p c0 =>
    rw [ep] at h
    cases p with
    | none => cases h
    | some p =>
      obtain ⟨a, r2⟩ := p
      simp only at h
      cases et : δ q a with
      | none => rw [et] at h; cases h
      | some t =>
        obtain ⟨w, d, s⟩ := t
        rw [et] at h
        cases d with
        | R =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hr := popR_spec env₀ endB r a r2 c0 ep hc.left R hR
          simp only [steps, step, XS.cfg, Res.cfg]
          rw [hr, cons_zero, et]
          simp only [tail_cons, Option.some.injEq]
          rw [nrm_spec L ws _ hc.right]
          simp [rep_one]
        | L =>
          simp only at h
          cases el : popB env₀ l with
          | mk pl c1 =>
            rw [el] at h
            cases pl with
            | none =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hr := popR_spec env₀ endB r a r2 c0 ep hc.left R hR
              simp only [steps, step, XS.cfg, Res.cfg]
              rw [hr, cons_zero, et, popB_none env₀ el hc.right L]
              simp only [tail_cons]
            | some pl =>
              obtain ⟨b, l'⟩ := pl
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hr := popR_spec env₀ endB r a r2 c0 ep hc.left.left R hR
              simp only [steps, step, XS.cfg, Res.cfg]
              rw [hr, cons_zero, et, popB_some env₀ el hc.left.right L]
              simp only [tail_cons, cons_zero, Option.some.injEq]
              rw [nrm_spec R ws _ hc.right]
              simp [rep_one]

/-- `a`, or else `f ()`. -/
def orX {α : Type} (a : Option α) (f : Unit → Option α) : Option α :=
  match a with
  | some x => some x
  | none => f ()

theorem orX_cases {α : Type} {a : Option α} {f : Unit → Option α} {x : α} (h : orX a f = some x) :
    a = some x ∨ f () = some x := by
  unfold orX at h
  cases a with
  | some y => left; exact h
  | none => right; exact h

def asRes (x : Option (XS Q × List Lin)) : Option (Res Q × List Lin) := x.map (fun p => (Sum.inl p.1, p.2))

theorem asRes_spec {endB : Bool} {c : XS Q} {x : Option (XS Q × List Lin)}
    (hx : ∀ c' cs, x = some (c', cs) → Reach δ endB cs c (fun env L R => c'.cfg env L R))
    {r : Res Q} {cs : List Lin} (h : asRes x = some (r, cs)) : Reach δ endB cs c (fun env L R => r.cfg env L R) := by
  unfold asRes at h
  cases e : x with
  | none => rw [e] at h; cases h
  | some p =>
    rw [e] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hx p.1 p.2 e

/-- One move: a crossing on the right (0 to 3 carried cells), on the left (0 to 3), else one step. -/
def xmove (endB : Bool) (c : XS Q) : Option (Res Q × List Lin) :=
  orX (asRes (xcrossR δ env₀ 0 c)) fun _ => orX (asRes (xcrossR δ env₀ 1 c)) fun _ =>
  orX (asRes (xcrossR δ env₀ 2 c)) fun _ => orX (asRes (xcrossR δ env₀ 3 c)) fun _ =>
  orX (asRes (xcrossL δ env₀ 0 c)) fun _ => orX (asRes (xcrossL δ env₀ 1 c)) fun _ =>
  orX (asRes (xcrossL δ env₀ 2 c)) fun _ => orX (asRes (xcrossL δ env₀ 3 c)) fun _ => xstep δ ws env₀ endB c

theorem xmove_spec (endB : Bool) (c : XS Q) (x : Res Q) (cs : List Lin) (h : xmove δ ws env₀ endB c = some (x, cs)) :
    Reach δ endB cs c (fun env L R => x.cfg env L R) := by
  unfold xmove at h
  have hR : ∀ j r cs, asRes (xcrossR δ env₀ j c) = some (r, cs) → Reach δ endB cs c (fun env L R => r.cfg env L R) :=
    fun j r cs h => asRes_spec δ (fun c' cs e => xcrossR_spec δ env₀ endB j c c' cs e) h
  have hL : ∀ j r cs, asRes (xcrossL δ env₀ j c) = some (r, cs) → Reach δ endB cs c (fun env L R => r.cfg env L R) :=
    fun j r cs h => asRes_spec δ (fun c' cs e => xcrossL_spec δ env₀ endB j c c' cs e) h
  rcases orX_cases h with h | h; exact hR 0 _ _ h
  rcases orX_cases h with h | h; exact hR 1 _ _ h
  rcases orX_cases h with h | h; exact hR 2 _ _ h
  rcases orX_cases h with h | h; exact hR 3 _ _ h
  rcases orX_cases h with h | h; exact hL 0 _ _ h
  rcases orX_cases h with h | h; exact hL 1 _ _ h
  rcases orX_cases h with h | h; exact hL 2 _ _ h
  rcases orX_cases h with h | h; exact hL 3 _ _ h
  exact xstep_spec δ ws env₀ endB c x cs h

/-- Run to the exit, collecting the conditions in `acc` (tail recursive). -/
def xrun (endB : Bool) : Nat → XS Q → List Lin → Option ((Q × Bool × SSide) × List Lin)
  | 0, _, _ => none
  | fuel + 1, c, acc =>
    match xmove δ ws env₀ endB c with
    | none => none
    | some (.inl c', c1) => xrun endB fuel c' (c1 ++ acc)
    | some (.inr e, c1) => some (e, c1 ++ acc)

theorem xrun_spec (endB : Bool) : ∀ (fuel : Nat) (c : XS Q) (acc : List Lin) (e : Q × Bool × SSide) (cs : List Lin),
    xrun δ ws env₀ endB fuel c acc = some (e, cs) →
    ∀ env, Holds env cs → Holds env acc ∧ ∀ R, (endB = true → R = blank) →
      ∃ n, ∀ L, steps δ n (c.cfg env L R) = some ⟨tail L, cons (L 0) (cons e.2.1 (den env R e.2.2)), e.1⟩
  | 0, _, _, _, _, h => by simp [xrun] at h
  | fuel + 1, c, acc, e, cs, h => by
    intro env hc
    simp only [xrun] at h
    cases em : xmove δ ws env₀ endB c with
    | none => rw [em] at h; cases h
    | some x =>
      obtain ⟨r, c1⟩ := x
      rw [em] at h
      cases r with
      | inl c' =>
        simp only at h
        obtain ⟨h1, h2⟩ := xrun_spec endB fuel c' (c1 ++ acc) e cs h env hc
        refine ⟨h1.right, fun R hR => ?_⟩
        obtain ⟨k, hk⟩ := xmove_spec δ ws env₀ endB c _ c1 em env h1.left R hR
        obtain ⟨m, hm⟩ := h2 R hR
        exact ⟨k + m, fun L => steps_seq δ (hk L) (hm L)⟩
      | inr e' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hc.right, fun R hR => ?_⟩
        obtain ⟨k, hk⟩ := xmove_spec δ ws env₀ endB c _ c1 em env hc.left R hR
        exact ⟨k, fun L => hk L⟩

/-- **An excursion, checked for a family.**  Start with the cells `u` (nearest first) on the left and the right
side `T`, in state `q`; on success, the exit is in state `q'` with the cells `v` (reading order) in front of the
returned side, at every valuation satisfying the returned conditions. -/
def exc (endB : Bool) (fuel : Nat) (u : List Bool) (q q' : Q) (v : List Bool) (T : SSide) :
    Option (SSide × List Lin) :=
  match xrun δ ws env₀ endB fuel ⟨pushCells u [], T, q⟩ [] with
  | none => none
  | some ((s, w, r), cs) =>
    if s = q' then
      match peelB env₀ (v.length - 1) r with
      | some (v', r', c2) => if v = w :: v' then some (r', c2 ++ cs) else none
      | none => none
    else none

theorem exc_spec (endB : Bool) (fuel : Nat) (u : List Bool) (q q' : Q) (v : List Bool) (T T' : SSide)
    (cs : List Lin) (h : exc δ ws env₀ endB fuel u q q' v T = some (T', cs)) :
    ∀ env, Holds env cs → ∀ R, (endB = true → R = blank) →
    ∃ n, ∀ L, steps δ n ⟨app u L, den env R T, q⟩ = some ⟨tail L, cons (L 0) (app v (den env R T')), q'⟩ := by
  intro env hc R hR
  unfold exc at h
  cases e : xrun δ ws env₀ endB fuel ⟨pushCells u [], T, q⟩ [] with
  | none => rw [e] at h; cases h
  | some x =>
    obtain ⟨⟨s, w, r⟩, cs1⟩ := x
    rw [e] at h
    simp only at h
    split at h
    · rename_i hs
      subst hs
      cases ep : peelB env₀ (v.length - 1) r with
      | none => rw [ep] at h; cases h
      | some p =>
        obtain ⟨v', r', c2⟩ := p
        rw [ep] at h
        simp only at h
        split at h
        · rename_i hv
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨-, hrun⟩ := xrun_spec δ ws env₀ endB fuel _ [] _ cs1 e env hc.right
          obtain ⟨n, hn⟩ := hrun R hR
          refine ⟨n, fun L => ?_⟩
          have := hn L
          simp only [XS.cfg, den_pushCells, den_nil] at this
          rw [this, hv, peelB_spec env₀ _ r v' r' c2 ep hc.left R]
          rfl
        · cases h
    · cases h

end

end SX
end TM
