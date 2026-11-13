import TM

set_option linter.unusedSectionVars false

/-!
# Checking symbolic runs by evaluation

A configuration whose tape is a list of *tokens*: single cells, and runs `w^n` of a word `w` whose count `n` is a
linear expression `c + a₁ x₁ + a₂ x₂ + …` in some variables.  The checker `run` replays a list of moves on such a
configuration: single machine steps (unrolling a run whose count is surely at least 1), crossings of a whole run by
the shift rules `TM.cross_r` and `TM.cross_l` (one copy simulated on a window that fails if it reads outside it),
and re-bracketings (`TM.rep_rotate`).  Everything it does is a computation on data, so a claim "these moves take this
configuration to that one" is a `decide` goal, and `run_sound` turns it into a statement about `steps` for every
value of the variables at once.

`norm` puts a token list in a normal form for comparing two lists that denote the same tape (runs of `01` merged,
pairs `0 1` absorbed, trailing blank cells dropped); `check` replays the moves and compares normal forms.

`auto` needs no list of moves: at each point it tries to cross the next run with a shift rule found on the spot
(`candR`, `candL`), else takes one step, and each time the head is at the left end in a given state it puts the
tape in normal form and compares it with the target.  `auto_reach` is its soundness theorem.
-/

namespace TM
namespace Sym

/-! ## Linear expressions -/

/-- `c + a₁ x₁ + a₂ x₂ + …`. -/
structure Lin where
  c : Nat
  a : List Nat
  deriving DecidableEq, Repr

def dot : List Nat → List Nat → Nat
  | a :: as, x :: xs => a * x + dot as xs
  | _, _ => 0

def Lin.eval (e : Lin) (x : List Nat) : Nat := e.c + dot e.a x

def addL : List Nat → List Nat → List Nat
  | a :: as, b :: bs => (a + b) :: addL as bs
  | [], bs => bs
  | as, [] => as

theorem dot_addL (as bs x : List Nat) : dot (addL as bs) x = dot as x + dot bs x := by
  induction as generalizing bs x with
  | nil => cases bs <;> simp [addL, dot]
  | cons a as ih =>
    cases bs with
    | nil => cases x <;> simp [addL, dot]
    | cons b bs =>
      cases x with
      | nil => simp [addL, dot]
      | cons y ys => simp only [addL, dot, ih]; rw [Nat.add_mul]; omega

def Lin.add (e f : Lin) : Lin := ⟨e.c + f.c, addL e.a f.a⟩

theorem Lin.eval_add (e f : Lin) (x : List Nat) : (e.add f).eval x = e.eval x + f.eval x := by
  simp only [Lin.add, Lin.eval, dot_addL]; omega

def Lin.const (n : Nat) : Lin := ⟨n, []⟩

theorem Lin.eval_const (n : Nat) (x : List Nat) : (Lin.const n).eval x = n := by
  simp [Lin.const, Lin.eval, dot]

def Lin.scale (m : Nat) (e : Lin) : Lin := ⟨m * e.c, e.a.map (m * ·)⟩

theorem dot_map (m : Nat) (as x : List Nat) : dot (as.map (m * ·)) x = m * dot as x := by
  induction as generalizing x with
  | nil => simp [dot]
  | cons a as ih => cases x <;> simp [dot, ih, Nat.mul_add, Nat.mul_assoc]

theorem Lin.eval_scale (m : Nat) (e : Lin) (x : List Nat) : (e.scale m).eval x = m * e.eval x := by
  simp only [Lin.scale, Lin.eval, dot_map, Nat.mul_add]

def Lin.pred (e : Lin) : Lin := ⟨e.c - 1, e.a⟩

theorem Lin.eval_pred (e : Lin) (h : 1 ≤ e.c) (x : List Nat) : e.eval x = e.pred.eval x + 1 := by
  simp only [Lin.eval, Lin.pred]; omega

def Lin.isZero (e : Lin) : Bool := e.c == 0 && e.a.all (· == 0)

theorem dot_zero (as x : List Nat) (h : as.all (· == 0) = true) : dot as x = 0 := by
  induction as generalizing x with
  | nil => simp [dot]
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    cases x with
    | nil => simp [dot]
    | cons y ys => simp [dot, h.1, ih ys h.2]

theorem Lin.eval_isZero (e : Lin) (h : e.isZero = true) (x : List Nat) : e.eval x = 0 := by
  simp only [Lin.isZero, Bool.and_eq_true, beq_iff_eq] at h
  simp [Lin.eval, h.1, dot_zero _ _ h.2]

/-- Substitution: each variable `xᵢ` replaced by the expression `σᵢ`. -/
def substL : List Nat → List Lin → Lin
  | a :: as, s :: ss => (s.scale a).add (substL as ss)
  | _, _ => Lin.const 0

def Lin.subst (e : Lin) (σ : List Lin) : Lin := (Lin.const e.c).add (substL e.a σ)

theorem eval_substL (as : List Nat) (σ : List Lin) (x : List Nat) :
    (substL as σ).eval x = dot as (σ.map (·.eval x)) := by
  induction as generalizing σ with
  | nil => cases σ <;> simp [substL, dot, Lin.eval_const]
  | cons a as ih =>
    cases σ with
    | nil => simp [substL, dot, Lin.eval_const]
    | cons s ss => simp only [substL, Lin.eval_add, Lin.eval_scale, ih, List.map_cons, dot]

theorem Lin.eval_subst (e : Lin) (σ : List Lin) (x : List Nat) :
    (e.subst σ).eval x = e.eval (σ.map (·.eval x)) := by
  rw [Lin.subst, Lin.eval_add, Lin.eval_const, eval_substL]; rfl

/-- Trailing zero coefficients dropped, so that equal expressions have equal data. -/
def trimZ : List Nat → List Nat
  | [] => []
  | a :: as => match a, trimZ as with
    | 0, [] => []
    | a, t => a :: t

theorem dot_trimZ (as x : List Nat) : dot (trimZ as) x = dot as x := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih =>
    have key : dot (a :: trimZ as) x = dot (a :: as) x := by
      cases x with
      | nil => simp [dot]
      | cons y ys => simp only [dot, ih]
    simp only [trimZ]
    split
    · rename_i h
      rw [← key, h]
      cases x <;> simp [dot]
    · exact key

def Lin.trim (e : Lin) : Lin := ⟨e.c, trimZ e.a⟩

theorem Lin.eval_trim (e : Lin) (x : List Nat) : e.trim.eval x = e.eval x := by
  simp [Lin.trim, Lin.eval, dot_trimZ]

/-! ## Tokens and their tapes -/

inductive Tok where
  | b : Bool → Tok
  | r : List Bool → Lin → Tok
  deriving DecidableEq, Repr

/-- The tape of a token list in front of `t` (first token nearest the head; on the left of the head, words are
written nearest cell first, as for every left stream). -/
def den (x : List Nat) : List Tok → Tape → Tape
  | [], t => t
  | .b v :: ts, t => cons v (den x ts t)
  | .r w n :: ts, t => rep (n.eval x) w (den x ts t)

theorem den_append (x : List Nat) (s ts : List Tok) (t : Tape) : den x (s ++ ts) t = den x s (den x ts t) := by
  induction s with
  | nil => rfl
  | cons a s ih => cases a <;> simp [den, ih]

theorem den_lits (x : List Nat) (w : List Bool) (t : Tape) : den x (w.map .b) t = app w t := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [den, ih]

theorem rep_nil (n : Nat) (t : Tape) : rep n [] t = t := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- A configuration: tokens left of the head (nearest first), tokens from the head on, the state; blank beyond. -/
structure MC (Q : Type) where
  l : List Tok
  r : List Tok
  st : Q
  deriving DecidableEq, Repr

variable {Q : Type}

def MC.den (x : List Nat) (c : MC Q) : Cfg Q := ⟨Sym.den x c.l blank, Sym.den x c.r blank, c.st⟩

/-! ## Reading the first cell -/

/-- The first cell of a token list and the tokens after it: a run is unrolled if its count is surely at least 1 and
dropped if it is surely 0; the end of the list is blank. -/
def pop : Nat → List Tok → Option (Bool × List Tok)
  | 0, _ => none
  | _ + 1, [] => some (false, [])
  | _ + 1, .b v :: ts => some (v, ts)
  | f + 1, .r w n :: ts =>
    match w with
    | [] => pop f ts
    | a :: w' =>
      if 1 ≤ n.c then some (a, w'.map .b ++ .r (a :: w') n.pred :: ts)
      else if n.isZero then pop f ts else none

theorem pop_den (x : List Nat) : ∀ (f : Nat) (ts : List Tok) (v : Bool) (rest : List Tok),
    pop f ts = some (v, rest) → den x ts blank = cons v (den x rest blank) := by
  intro f
  induction f with
  | zero => intro ts v rest h; simp [pop] at h
  | succ f ih =>
    intro ts v rest h
    match ts with
    | [] =>
      simp only [pop, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact cons_false_blank.symm
    | .b u :: ts =>
      simp only [pop, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | .r w n :: ts =>
      match w with
      | [] =>
        simp only [pop] at h
        simp only [den, rep_nil]
        exact ih ts v rest h
      | a :: w' =>
        simp only [pop] at h
        split at h
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [den]
          rw [Lin.eval_pred n hc x, den_append, den_lits]
          rfl
        · split at h
          · rename_i _ hz
            simp only [den, Lin.eval_isZero n hz x, rep_zero]
            exact ih ts v rest h
          · simp at h

/-! ## Moves -/

section
variable [DecidableEq Q] (δ : Q → Bool → Option (Bool × Dir × Q))

/-- One machine step. -/
def mstep (c : MC Q) : Option (MC Q) :=
  match pop 64 c.r with
  | none => none
  | some (v, rt) =>
    match δ c.st v with
    | none => none
    | some (w, .R, s) => some ⟨.b w :: c.l, rt, s⟩
    | some (w, .L, s) =>
      match pop 64 c.l with
      | none => none
      | some (y, lt) => some ⟨lt, .b y :: .b w :: rt, s⟩

theorem mstep_sound (x : List Nat) (c c' : MC Q) (h : mstep δ c = some c') :
    step δ (c.den x) = some (c'.den x) := by
  unfold mstep at h
  cases hp : pop 64 c.r with
  | none => simp [hp] at h
  | some p =>
    obtain ⟨v, rt⟩ := p
    have hr := pop_den x 64 c.r v rt hp
    simp only [hp] at h
    cases hd : δ c.st v with
    | none => simp [hd] at h
    | some t =>
      obtain ⟨w, d, s⟩ := t
      cases d with
      | R =>
        simp only [hd, Option.some.injEq] at h
        subst h
        simp only [step, MC.den, hr, cons_zero, hd, tail_cons, Sym.den]
      | L =>
        cases hq : pop 64 c.l with
        | none => simp [hd, hq] at h
        | some p' =>
          obtain ⟨y, lt⟩ := p'
          have hl := pop_den x 64 c.l y lt hq
          simp only [hd, hq, Option.some.injEq] at h
          subst h
          simp only [step, MC.den, hr, cons_zero, hd, hl, tail_cons, Sym.den]

/-- The local simulator on a window of cells, failing when the head would read a cell outside it. -/
def wstep (c : FCfg Q) : Option (FCfg Q) :=
  match c.r with
  | [] => none
  | v :: rt =>
    match δ c.st v with
    | none => none
    | some (w, .R, s) => some ⟨w :: c.l, rt, s⟩
    | some (w, .L, s) =>
      match c.l with
      | [] => none
      | y :: lt => some ⟨lt, y :: w :: rt, s⟩

def wsteps : Nat → FCfg Q → Option (FCfg Q)
  | 0, c => some c
  | n + 1, c => match wstep δ c with
    | none => none
    | some c' => wsteps n c'

theorem wstep_sound (c c' : FCfg Q) (h : wstep δ c = some c') (L R : Tape) :
    step δ ⟨app c.l L, app c.r R, c.st⟩ = some ⟨app c'.l L, app c'.r R, c'.st⟩ := by
  obtain ⟨l, r, q⟩ := c
  cases r with
  | nil => simp [wstep] at h
  | cons v rt =>
    cases hd : δ q v with
    | none => simp [wstep, hd] at h
    | some t =>
      obtain ⟨w, d, s⟩ := t
      cases d with
      | R => simp only [wstep, hd, Option.some.injEq] at h; subst h; simp [step, hd]
      | L =>
        cases l with
        | nil => simp [wstep, hd] at h
        | cons y lt => simp only [wstep, hd, Option.some.injEq] at h; subst h; simp [step, hd]

theorem wsteps_sound (n : Nat) : ∀ (c c' : FCfg Q), wsteps δ n c = some c' → ∀ L R : Tape,
    steps δ n ⟨app c.l L, app c.r R, c.st⟩ = some ⟨app c'.l L, app c'.r R, c'.st⟩ := by
  induction n with
  | zero => intro c c' h L R; simp only [wsteps, Option.some.injEq] at h; subst h; rfl
  | succ n ih =>
    intro c c' h L R
    simp only [wsteps] at h
    split at h
    · cases h
    · rename_i d hd
      rw [steps_succ_of_step δ n (wstep_sound δ c d hd L R)]
      exact ih d c' h L R

/-- The first `k` tokens of a list, if they are all single cells. -/
def lits : Nat → List Tok → Option (List Bool × List Tok)
  | 0, ts => some ([], ts)
  | k + 1, .b v :: ts => (lits k ts).map fun p => (v :: p.1, p.2)
  | _ + 1, _ => none

theorem lits_eq : ∀ (k : Nat) (ts : List Tok) (u : List Bool) (rest : List Tok),
    lits k ts = some (u, rest) → ts = u.map .b ++ rest := by
  intro k
  induction k with
  | zero => intro ts u rest h; simp only [lits, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | succ k ih =>
    intro ts u rest h
    match ts with
    | [] => simp [lits] at h
    | .r _ _ :: _ => simp [lits] at h
    | .b v :: ts =>
      simp only [lits, Option.map_eq_some_iff, Prod.exists] at h
      obtain ⟨u', rest', h1, h2⟩ := h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      simp [ih ts u' rest' h1]

/-- Cross the run at the head to the right, carrying the `k` cells on its left: one copy is simulated in `s` steps
on a window and must come out on the far side in the same state. -/
def crossR (k s : Nat) (c : MC Q) : Option (MC Q) :=
  match c.r with
  | .r w n :: rest =>
    match lits k c.l with
    | none => none
    | some (u, lrest) =>
      match wsteps δ s ⟨u, w, c.st⟩ with
      | none => none
      | some e =>
        if e.r = [] ∧ e.st = c.st ∧ e.l.take u.length = u ∧ e.l.length = u.length + w.length then
          some ⟨u.map .b ++ .r (e.l.drop u.length) n :: lrest, rest, c.st⟩
        else none
  | _ => none

/-- Cross the run on the left of the head, carrying the `k` cells from the head on. -/
def crossL (k s : Nat) (c : MC Q) : Option (MC Q) :=
  match c.l with
  | .r w n :: lrest =>
    match lits k c.r with
    | none => none
    | some (u, rest) =>
      match wsteps δ s ⟨w, u, c.st⟩ with
      | none => none
      | some e =>
        if e.l = [] ∧ e.st = c.st ∧ e.r.take u.length = u ∧ e.r.length = u.length + w.length then
          some ⟨lrest, u.map .b ++ .r (e.r.drop u.length) n :: rest, c.st⟩
        else none
  | _ => none

theorem take_drop_eq (u l : List Bool) (h : l.take u.length = u) : l = u ++ l.drop u.length := by
  conv => lhs; rw [← List.take_append_drop u.length l]
  rw [h]

theorem crossR_sound (k s : Nat) (x : List Nat) (c c' : MC Q) (h : crossR δ k s c = some c') :
    ∃ n, steps δ n (c.den x) = some (c'.den x) := by
  unfold crossR at h
  split at h
  · rename_i w n rest hr
    split at h
    · cases h
    · rename_i u lrest hl
      split at h
      · cases h
      · rename_i e he
        split at h
        · rename_i hc
          obtain ⟨h1, h2, h3, _⟩ := hc
          simp only [Option.some.injEq] at h
          subst h
          have hw : ∀ L R : Tape, steps δ s ⟨app u L, app w R, c.st⟩ =
              some ⟨app u (app (e.l.drop u.length) L), R, c.st⟩ := by
            intro L R
            have := wsteps_sound δ s ⟨u, w, c.st⟩ e he L R
            rw [this]
            obtain ⟨el, er, est⟩ := e
            simp only at h1 h2 h3 ⊢
            subst h1 h2
            rw [take_drop_eq u el h3, app_app]
            simp only [List.length_append, Nat.add_sub_cancel_left, List.drop_left']
            rfl
          refine ⟨(n.eval x) * s, ?_⟩
          have hc := cross_r δ hw (n.eval x) (Sym.den x lrest blank) (Sym.den x rest blank)
          simp only [MC.den, hr, lits_eq k c.l u lrest hl, den_append, den_lits, Sym.den]
          exact hc
        · cases h
  · cases h

theorem crossL_sound (k s : Nat) (x : List Nat) (c c' : MC Q) (h : crossL δ k s c = some c') :
    ∃ n, steps δ n (c.den x) = some (c'.den x) := by
  unfold crossL at h
  split at h
  · rename_i w n lrest hlr
    split at h
    · cases h
    · rename_i u rest hl
      split at h
      · cases h
      · rename_i e he
        split at h
        · rename_i hc
          obtain ⟨h1, h2, h3, _⟩ := hc
          simp only [Option.some.injEq] at h
          subst h
          have hw : ∀ L R : Tape, steps δ s ⟨app w L, app u R, c.st⟩ =
              some ⟨L, app u (app (e.r.drop u.length) R), c.st⟩ := by
            intro L R
            have := wsteps_sound δ s ⟨w, u, c.st⟩ e he L R
            rw [this]
            obtain ⟨el, er, est⟩ := e
            simp only at h1 h2 h3 ⊢
            subst h1 h2
            have e1 : app er R = app u (app (er.drop u.length) R) := by
              conv => lhs; rw [take_drop_eq u er h3]
              rw [app_app]
            rw [app_nil, e1]
          refine ⟨(n.eval x) * s, ?_⟩
          have hc := cross_l δ hw (n.eval x) (Sym.den x lrest blank) (Sym.den x rest blank)
          simp only [MC.den, hlr, lits_eq k c.r u rest hl, den_append, den_lits, Sym.den]
          exact hc
        · cases h
  · cases h

/-- Re-bracket `x (y)^n` into `(y')^n x` at the front of a token list, when `x ++ y = y' ++ x`. -/
def rot (k : Nat) (ts : List Tok) : Option (List Tok) :=
  match lits k ts with
  | none => none
  | some (xw, rest) =>
    match rest with
    | .r y n :: rest' =>
      let y' := (xw ++ y).take y.length
      if (xw ++ y).drop y.length = xw then some (.r y' n :: xw.map .b ++ rest') else none
    | _ => none

theorem rot_den (k : Nat) (x : List Nat) (ts ts' : List Tok) (h : rot k ts = some ts') (t : Tape) :
    den x ts t = den x ts' t := by
  unfold rot at h
  cases hl : lits k ts with
  | none => simp [hl] at h
  | some p =>
    obtain ⟨xw, rest⟩ := p
    simp only [hl] at h
    match rest, h with
    | .r y n :: rest', h =>
      simp only at h
      split at h
      · rename_i hd
        simp only [Option.some.injEq] at h
        subst h
        rw [lits_eq k ts xw _ hl]
        simp only [den_append, den_lits, den]
        apply rep_rotate
        conv => lhs; rw [← List.take_append_drop y.length (xw ++ y)]
        rw [hd]
      · cases h
    | [], h => simp at h
    | .b _ :: _, h => simp at h

/-- The moves of a trace. -/
inductive Move where
  | step : Move
  | cr : Nat → Nat → Move      -- cross right, carrying k cells, s steps a copy
  | cl : Nat → Nat → Move      -- cross left
  | rr : Nat → Move            -- re-bracket on the right of the head
  | rl : Nat → Move            -- re-bracket on the left
  deriving DecidableEq, Repr

def move1 (c : MC Q) : Move → Option (MC Q)
  | .step => mstep δ c
  | .cr k s => crossR δ k s c
  | .cl k s => crossL δ k s c
  | .rr k => (rot k c.r).map fun r => ⟨c.l, r, c.st⟩
  | .rl k => (rot k c.l).map fun l => ⟨l, c.r, c.st⟩

/-- Replay moves; also counts the single steps. -/
def run : MC Q → List Move → Option (MC Q × Nat)
  | c, [] => some (c, 0)
  | c, m :: ms => match move1 δ c m with
    | none => none
    | some c' => (run c' ms).map fun p => (p.1, p.2 + (if m = .step then 1 else 0))

theorem move1_sound (x : List Nat) (c c' : MC Q) (m : Move) (h : move1 δ c m = some c') :
    ∃ n, (m = .step → 1 ≤ n) ∧ steps δ n (c.den x) = some (c'.den x) := by
  cases m with
  | step =>
    refine ⟨1, fun _ => Nat.le_refl 1, ?_⟩
    simp only [move1] at h
    rw [steps_succ_of_step δ 0 (mstep_sound δ x c c' h)]; rfl
  | cr k s =>
    obtain ⟨n, hn⟩ := crossR_sound δ k s x c c' h
    exact ⟨n, (fun h => by cases h), hn⟩
  | cl k s =>
    obtain ⟨n, hn⟩ := crossL_sound δ k s x c c' h
    exact ⟨n, (fun h => by cases h), hn⟩
  | rr k =>
    simp only [move1, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    refine ⟨0, (fun h => by cases h), ?_⟩
    simp only [steps, MC.den, rot_den k x c.r r hr]
  | rl k =>
    simp only [move1, Option.map_eq_some_iff] at h
    obtain ⟨l, hl, rfl⟩ := h
    refine ⟨0, (fun h => by cases h), ?_⟩
    simp only [steps, MC.den, rot_den k x c.l l hl]

theorem run_sound (x : List Nat) : ∀ (ms : List Move) (c c' : MC Q) (k : Nat), run δ c ms = some (c', k) →
    ∃ n, k ≤ n ∧ steps δ n (c.den x) = some (c'.den x) := by
  intro ms
  induction ms with
  | nil => intro c c' k h; simp only [run, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨0, Nat.le_refl 0, rfl⟩
  | cons m ms ih =>
    intro c c' k h
    simp only [run] at h
    split at h
    · cases h
    · rename_i d hd
      simp only [Option.map_eq_some_iff, Prod.exists] at h
      obtain ⟨c2, k2, h2, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨n1, hn1, hs1⟩ := move1_sound δ x c d m hd
      obtain ⟨n2, hn2, hs2⟩ := ih d c2 k2 h2
      refine ⟨n1 + n2, ?_, steps_seq δ hs1 hs2⟩
      split
      · rename_i hm; have := hn1 hm; omega
      · omega

end


/-! ## Powers of words, regrouping a run -/

/-- `w` written `m` times. -/
def pw : Nat → List Bool → List Bool
  | 0, _ => []
  | m + 1, w => w ++ pw m w

theorem app_pw (m : Nat) (w : List Bool) (t : Tape) : app (pw m w) t = rep m w t := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [pw, rep_succ, ← app_app, ih]

theorem rep_pw (m n : Nat) (w : List Bool) (t : Tape) : rep n (pw m w) t = rep (m * n) w t := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [rep_succ, app_pw, ih, Nat.mul_succ, Nat.add_comm, rep_add]

theorem dot_div (m : Nat) : ∀ (as x : List Nat), as.all (· % m == 0) = true →
    m * dot (as.map (· / m)) x = dot as x
  | [], x, _ => by simp [dot]
  | a :: as, [], _ => by simp [dot]
  | a :: as, y :: ys, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.map_cons, dot, Nat.mul_add, ← Nat.mul_assoc]
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.1), dot_div m as ys h.2]

/-- `e = m * q + r` with `r` a constant, when every coefficient of `e` is a multiple of `m`. -/
def Lin.divm (m : Nat) (e : Lin) : Option (Lin × Nat) :=
  if e.a.all (· % m == 0) then some (⟨e.c / m, e.a.map (· / m)⟩, e.c % m) else none

theorem Lin.eval_divm (m : Nat) (e q : Lin) (r : Nat) (h : e.divm m = some (q, r)) (x : List Nat) :
    e.eval x = m * q.eval x + r := by
  unfold Lin.divm at h
  split at h
  · rename_i ha
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Lin.eval, Nat.mul_add, dot_div m e.a x ha]
    have := Nat.div_add_mod e.c m
    omega
  · cases h

/-- Regroup the run at the front of a token list: `w^(m q + r)` as `(w^m)^q w^r`. -/
def grp (m : Nat) : List Tok → Option (List Tok)
  | .r w n :: rest =>
    match n.divm m with
    | some (q, r) => some (.r (pw m w) q :: (if r = 0 then rest else .r w (Lin.const r) :: rest))
    | none => none
  | _ => none

theorem grp_den (m : Nat) (x : List Nat) (ts ts' : List Tok) (h : grp m ts = some ts') (t : Tape) :
    den x ts t = den x ts' t := by
  match ts with
  | [] => simp [grp] at h
  | .b _ :: _ => simp [grp] at h
  | .r w n :: rest =>
    simp only [grp] at h
    split at h
    · rename_i q r hd
      simp only [Option.some.injEq] at h
      subst h
      split
      · rename_i hr0
        simp only [den, rep_pw, Lin.eval_divm m n q r hd x, hr0, Nat.add_zero]
      · simp only [den, rep_pw, Lin.eval_const, Lin.eval_divm m n q r hd x, rep_add]
    · cases h

/-- A copy of the run's word written out just behind it joins the run: `w^n w = w^(n+1)`. -/
def absorb : List Tok → Option (List Tok)
  | .r w n :: rest =>
    match lits w.length rest with
    | some (u, rest') => if u = w then some (.r w (n.add (Lin.const 1)) :: rest') else none
    | none => none
  | _ => none

theorem absorb_den (x : List Nat) (ts ts' : List Tok) (h : absorb ts = some ts') (t : Tape) :
    den x ts t = den x ts' t := by
  match ts with
  | [] => simp [absorb] at h
  | .b _ :: _ => simp [absorb] at h
  | .r w n :: rest =>
    simp only [absorb] at h
    split at h
    · rename_i u rest' hl
      split at h
      · rename_i hu
        simp only [Option.some.injEq] at h
        subst h hu
        rw [lits_eq _ rest u rest' hl]
        simp only [den, den_append, den_lits, Lin.eval_add, Lin.eval_const, rep_app_comm]
      · cases h
    · cases h

/-! ## Normal form -/

/-- `(0 1)^m` written out. -/
def isPairs : List Bool → Option Nat
  | [] => some 0
  | false :: true :: w => (isPairs w).map (· + 1)
  | _ => none

theorem isPairs_eq : ∀ (w : List Bool) (m : Nat), isPairs w = some m → w = pw m [false, true]
  | [], m, h => by simp only [isPairs, Option.some.injEq] at h; subst h; rfl
  | false :: true :: w, m, h => by
    simp only [isPairs, Option.map_eq_some_iff] at h
    obtain ⟨m', hm, rfl⟩ := h
    rw [isPairs_eq w m' hm]; rfl
  | [false], _, h => by simp [isPairs] at h
  | false :: false :: _, _, h => by simp [isPairs] at h
  | true :: _, _, h => by simp [isPairs] at h

theorem den_cons_tok (x : List Nat) (tk : Tok) (ts : List Tok) (t : Tape) :
    den x (tk :: ts) t = den x [tk] (den x ts t) := by
  cases tk <;> rfl

/-- One token, expanded: empty runs dropped, runs of `(0 1)^m` written as runs of `0 1`, constant runs of other
words written out. -/
def expandTok : Tok → List Tok
  | .b v => [.b v]
  | .r w n =>
    if n.isZero then []
    else match isPairs w with
      | some m => [.r [false, true] (n.scale m)]
      | none => if n.a.all (· == 0) then (pw n.c w).map .b else [.r w n]

theorem expandTok_den (x : List Nat) (tk : Tok) (t : Tape) : den x (expandTok tk) t = den x [tk] t := by
  cases tk with
  | b v => rfl
  | r w n =>
    simp only [expandTok]
    split
    · rename_i hz; simp [den, Lin.eval_isZero n hz x]
    · split
      · rename_i m hm
        simp only [den, Lin.eval_scale, isPairs_eq w m hm, rep_pw]
      · split
        · rename_i ha
          have hc : n.eval x = n.c := by simp [Lin.eval, dot_zero _ _ ha]
          simp only [den_lits, den, hc, app_pw]
        · rfl

def expand : List Tok → List Tok
  | [] => []
  | tk :: ts => expandTok tk ++ expand ts

theorem expand_den (x : List Nat) (ts : List Tok) (t : Tape) : den x (expand ts) t = den x ts t := by
  induction ts with
  | nil => rfl
  | cons tk ts ih => rw [expand, den_append, ih, expandTok_den, ← den_cons_tok]

/-- Trailing blank cells dropped. -/
def dropTF : List Tok → List Tok
  | [] => []
  | tk :: ts =>
    match tk, dropTF ts with
    | .b false, [] => []
    | tk, r => tk :: r

theorem dropTF_den (x : List Nat) (ts : List Tok) : den x (dropTF ts) blank = den x ts blank := by
  induction ts with
  | nil => rfl
  | cons tk ts ih =>
    simp only [dropTF]
    split
    · rename_i h
      rw [h] at ih
      simp only [den] at ih ⊢
      rw [← ih, cons_false_blank]
    · rw [den_cons_tok, ih, ← den_cons_tok]

/-- Put a token in front of a normal list, merging runs of `0 1` and absorbing a pair `0 1`. -/
def push : Tok → List Tok → List Tok
  | .r [false, true] n, .r [false, true] m :: rest => .r [false, true] (n.add m) :: rest
  | .b false, .b true :: rest => push (.r [false, true] (Lin.const 1)) rest
  | tk, rest => tk :: rest

theorem push_den (x : List Nat) (t : Tape) : ∀ (ts : List Tok) (tk : Tok), den x (push tk ts) t = den x (tk :: ts) t := by
  intro ts
  induction ts with
  | nil => intro tk; unfold push; split <;> simp_all
  | cons hd ts ih =>
    intro tk
    unfold push
    split
    · rename_i n m rest h
      cases h
      simp only [den, Lin.eval_add, rep_add]
    · rename_i rest h
      cases h
      rw [ih]
      simp [den, Lin.eval_const]
    · rfl

def merge : List Tok → List Tok
  | [] => []
  | tk :: ts => push tk (merge ts)

theorem merge_den (x : List Nat) (ts : List Tok) (t : Tape) : den x (merge ts) t = den x ts t := by
  induction ts with
  | nil => rfl
  | cons tk ts ih => rw [merge, push_den, den_cons_tok, ih, ← den_cons_tok]

def trimTok : Tok → Tok
  | .r w n => .r w n.trim
  | tk => tk

theorem trim_den (x : List Nat) (ts : List Tok) (t : Tape) : den x (ts.map trimTok) t = den x ts t := by
  induction ts with
  | nil => rfl
  | cons tk ts ih => cases tk <;> simp [trimTok, den, ih, Lin.eval_trim]

/-- The normal form of a token list ending in blank tape. -/
def norm (ts : List Tok) : List Tok := (merge (dropTF (expand ts))).map trimTok

theorem norm_den (x : List Nat) (ts : List Tok) : den x (norm ts) blank = den x ts blank := by
  rw [norm, trim_den, merge_den, dropTF_den, expand_den]

theorem allFalse_den (x : List Nat) : ∀ (ts : List Tok), ts.all (· == .b false) = true → den x ts blank = blank
  | [], _ => rfl
  | tk :: ts, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [den, allFalse_den x ts h, cons_false_blank]

/-! ## Substitution -/

def Tok.subst (σ : List Lin) : Tok → Tok
  | .b v => .b v
  | .r w n => .r w (n.subst σ)

theorem den_subst (σ : List Lin) (x : List Nat) (ts : List Tok) (t : Tape) :
    den x (ts.map (Tok.subst σ)) t = den (σ.map (·.eval x)) ts t := by
  induction ts with
  | nil => rfl
  | cons tk ts ih => cases tk <;> simp [Tok.subst, den, ih, Lin.eval_subst]

def MC.subst (σ : List Lin) (c : MC Q) : MC Q := ⟨c.l.map (Tok.subst σ), c.r.map (Tok.subst σ), c.st⟩

theorem MC.den_subst (σ : List Lin) (x : List Nat) (c : MC Q) : (c.subst σ).den x = c.den (σ.map (·.eval x)) := by
  simp only [MC.subst, MC.den]
  rw [Sym.den_subst, Sym.den_subst]

/-! ## Searching for the moves -/

section
variable [DecidableEq Q] (δ : Q → Bool → Option (Bool × Dir × Q))

/-- Steps of one copy of a right crossing: run the window until the head leaves it on the right. -/
def findR : Nat → FCfg Q → Nat → Option Nat
  | 0, _, _ => none
  | f + 1, c, n =>
    match c.r with
    | [] => some n
    | _ => match wstep δ c with
      | none => none
      | some c' => findR f c' (n + 1)

/-- Steps of one copy of a left crossing: run the window until the head is on its first cell, in state `q`, with
the carried word `u` there. -/
def findL (q : Q) (u : List Bool) : Nat → FCfg Q → Nat → Option Nat
  | 0, _, _ => none
  | f + 1, c, n =>
    if c.l = [] ∧ c.st = q ∧ c.r.take u.length = u then some n
    else match wstep δ c with
      | none => none
      | some c' => findL q u f c' (n + 1)

def crossRa (k : Nat) (c : MC Q) : Option (MC Q) :=
  match c.r, lits k c.l with
  | .r w n :: _, some (u, _) =>
    if n.isZero then none else
    match findR δ 200 ⟨u, w, c.st⟩ 0 with
    | some s => crossR δ k s c
    | none => none
  | _, _ => none

def crossLa (k : Nat) (c : MC Q) : Option (MC Q) :=
  match c.l, lits k c.r with
  | .r w n :: _, some (u, _) =>
    if n.isZero then none else
    match findL δ c.st u 200 ⟨w, u, c.st⟩ 0 with
    | some s => crossL δ k s c
    | none => none
  | _, _ => none

/-- A crossing at the head, with carry 0–3 cells, possibly after regrouping or re-bracketing the run. -/
def crossAny (c : MC Q) : Option (MC Q) :=
  (crossRa δ 0 c) <|> (crossRa δ 1 c) <|> (crossRa δ 2 c) <|> (crossRa δ 3 c) <|>
  (crossLa δ 1 c) <|> (crossLa δ 2 c) <|> (crossLa δ 3 c)

def withR (c : MC Q) : Option (List Tok) → Option (MC Q)
  | some r => some ⟨c.l, r, c.st⟩
  | none => none

def withL (c : MC Q) : Option (List Tok) → Option (MC Q)
  | some l => some ⟨l, c.r, c.st⟩
  | none => none

def bindC : Option (MC Q) → (MC Q → Option (MC Q)) → Option (MC Q)
  | some c, f => f c
  | none, _ => none

def bindS (o : Option (MC Q)) : Option (MC Q) :=
  match o with
  | some d => mstep δ d
  | none => none

/-- One step, after letting a run at the head absorb a copy of its word if the step needs it. -/
def stepA (c : MC Q) : Option (MC Q) :=
  mstep δ c <|> bindS δ (withL c (absorb c.l)) <|> bindS δ (withR c (absorb c.r))

/-- The next move: a crossing (directly, after regrouping the run by 2 or 3, or after re-bracketing 1–3 cells),
else one step (`true`). -/
def headRun : List Tok → Bool
  | .r _ _ :: _ => true
  | _ => false

def headFT : List Tok → Bool
  | .r [false, true] _ :: _ => true
  | _ => false

/-- `k` single cells, then a run. -/
def runAt : Nat → List Tok → Bool
  | 0, ts => headRun ts
  | k + 1, .b _ :: ts => runAt k ts
  | _, _ => false

def crossRany (c : MC Q) : Option (MC Q) :=
  crossRa δ 0 c <|> crossRa δ 1 c <|> crossRa δ 2 c <|> crossRa δ 3 c

def crossLany (c : MC Q) : Option (MC Q) :=
  crossLa δ 1 c <|> crossLa δ 2 c <|> crossLa δ 3 c

def bindF (o : Option (MC Q)) (f : MC Q → Option (MC Q)) : Option (MC Q) :=
  match o with
  | some d => f d
  | none => none

/-- Crossings to the right: of the run at the head, after regrouping it (runs of `0 1`), or after re-bracketing
1–3 cells in front of a run. -/
def candR (c : MC Q) : Option (MC Q) :=
  (if headRun c.r then crossRany δ c else none) <|>
  (if headFT c.r then bindF (withR c (grp 3 c.r)) (crossRany δ) <|> bindF (withR c (grp 2 c.r)) (crossRany δ)
   else none) <|>
  (if runAt 1 c.r then bindF (withR c (rot 1 c.r)) (crossRany δ) else none) <|>
  (if runAt 2 c.r then bindF (withR c (rot 2 c.r)) (crossRany δ) else none) <|>
  (if runAt 3 c.r then bindF (withR c (rot 3 c.r)) (crossRany δ) else none)

def candL (c : MC Q) : Option (MC Q) :=
  (if headRun c.l then crossLany δ c else none) <|>
  (if headFT c.l then bindF (withL c (grp 3 c.l)) (crossLany δ) <|> bindF (withL c (grp 2 c.l)) (crossLany δ)
   else none) <|>
  (if runAt 1 c.l then bindF (withL c (rot 1 c.l)) (crossLany δ) else none) <|>
  (if runAt 2 c.l then bindF (withL c (rot 2 c.l)) (crossLany δ) else none) <|>
  (if runAt 3 c.l then bindF (withL c (rot 3 c.l)) (crossLany δ) else none)

/-- The next move: a crossing, else one step (`true`). -/
def next (c : MC Q) : Option (MC Q × Bool) :=
  match candR δ c <|> candL δ c with
  | some c' => some (c', false)
  | none => (stepA δ c).map fun c' => (c', true)

/-- Search from `c` for the configuration `⟨blank, R, q⟩` (compared in normal form), at most `f` moves.  At every
visit of the left end in state `q` the right part is put in normal form (merging the runs). -/
def auto (q : Q) (R : List Tok) : Nat → Bool → MC Q → Bool
  | 0, _, _ => false
  | f + 1, stepped, c =>
    let atEnd : Bool := decide (c.st = q) && c.l.all (· == .b false)
    let c := if atEnd then ⟨c.l, norm c.r, c.st⟩ else c
    if stepped && atEnd && decide (c.r = R) then true
    else match next δ c with
      | some (c', b) => auto q R f (stepped || b) c'
      | none => false

/-- The number of moves `auto` makes (for measuring). -/
def autoLen (q : Q) (R : List Tok) : Nat → Bool → MC Q → Nat → Option Nat
  | 0, _, _, _ => none
  | f + 1, stepped, c, n =>
    let atEnd : Bool := decide (c.st = q) && c.l.all (· == .b false)
    let c := if atEnd then ⟨c.l, norm c.r, c.st⟩ else c
    if stepped && atEnd && decide (c.r = R) then some n
    else match next δ c with
      | some (c', b) => autoLen q R f (stepped || b) c' (n + 1)
      | none => none

theorem crossRa_sound (k : Nat) (x : List Nat) (c c' : MC Q) (h : crossRa δ k c = some c') :
    ∃ n, steps δ n (c.den x) = some (c'.den x) := by
  unfold crossRa at h
  split at h
  · split at h
    · cases h
    · split at h
      · exact crossR_sound δ k _ x c c' h
      · cases h
  · cases h

theorem crossLa_sound (k : Nat) (x : List Nat) (c c' : MC Q) (h : crossLa δ k c = some c') :
    ∃ n, steps δ n (c.den x) = some (c'.den x) := by
  unfold crossLa at h
  split at h
  · split at h
    · cases h
    · split at h
      · exact crossL_sound δ k _ x c c' h
      · cases h
  · cases h

/-- What the candidate moves have in common: they reach their result by some steps. -/
def Reach (c c' : MC Q) : Prop := ∀ x, ∃ n, steps δ n (c.den x) = some (c'.den x)

theorem orElse_reach {c : MC Q} {a b : Option (MC Q)} (ha : ∀ c', a = some c' → Reach δ c c')
    (hb : ∀ c', b = some c' → Reach δ c c') : ∀ c', (a <|> b) = some c' → Reach δ c c' := by
  intro c' h
  cases a with
  | some a' => exact ha c' h
  | none => exact hb c' h

theorem crossAny_reach (c : MC Q) : ∀ c', crossAny δ c = some c' → Reach δ c c' := by
  unfold crossAny
  refine orElse_reach δ (fun c' h x => crossRa_sound δ 0 x c c' h) ?_
  refine orElse_reach δ (fun c' h x => crossRa_sound δ 1 x c c' h) ?_
  refine orElse_reach δ (fun c' h x => crossRa_sound δ 2 x c c' h) ?_
  refine orElse_reach δ (fun c' h x => crossRa_sound δ 3 x c c' h) ?_
  refine orElse_reach δ (fun c' h x => crossLa_sound δ 1 x c c' h) ?_
  refine orElse_reach δ (fun c' h x => crossLa_sound δ 2 x c c' h) ?_
  exact fun c' h x => crossLa_sound δ 3 x c c' h

theorem withR_den (c : MC Q) (o : Option (List Tok)) (hr : ∀ r, o = some r → ∀ x, den x c.r blank = den x r blank) :
    ∀ d, withR c o = some d → ∀ x, c.den x = d.den x := by
  intro d h x
  cases o with
  | none => cases h
  | some r => simp only [withR, Option.some.injEq] at h; subst h; simp [MC.den, hr r rfl x]

theorem withL_den (c : MC Q) (o : Option (List Tok)) (hl : ∀ l, o = some l → ∀ x, den x c.l blank = den x l blank) :
    ∀ d, withL c o = some d → ∀ x, c.den x = d.den x := by
  intro d h x
  cases o with
  | none => cases h
  | some l => simp only [withL, Option.some.injEq] at h; subst h; simp [MC.den, hl l rfl x]

theorem bindC_reach (c : MC Q) (o : Option (MC Q)) (ho : ∀ d, o = some d → ∀ x, c.den x = d.den x) :
    ∀ c', bindC o (crossAny δ) = some c' → Reach δ c c' := by
  intro c' h x
  cases o with
  | none => cases h
  | some d =>
    simp only [bindC] at h
    obtain ⟨n, hn⟩ := crossAny_reach δ d c' h x
    exact ⟨n, by rw [ho d rfl x]; exact hn⟩

theorem stepA_sound (x : List Nat) (c c' : MC Q) (h : stepA δ c = some c') : step δ (c.den x) = some (c'.den x) := by
  unfold stepA at h
  cases h1 : mstep δ c with
  | some d => rw [h1] at h; cases h; exact mstep_sound δ x c _ h1
  | none =>
    rw [h1] at h
    have hL : ∀ l, absorb c.l = some l → ∀ x, den x c.l blank = den x l blank := fun l hl x => absorb_den x c.l l hl blank
    have hR : ∀ r, absorb c.r = some r → ∀ x, den x c.r blank = den x r blank := fun r hr x => absorb_den x c.r r hr blank
    cases h2 : bindS δ (withL c (absorb c.l)) with
    | some d =>
      rw [h2] at h; cases h
      cases h3 : absorb c.l with
      | none => simp [h3, withL, bindS] at h2
      | some l =>
        simp only [h3, withL, bindS] at h2
        rw [show c.den x = MC.den x ⟨l, c.r, c.st⟩ by simp [MC.den, hL l h3 x]]
        exact mstep_sound δ x _ _ h2
    | none =>
      rw [h2] at h
      cases h3 : absorb c.r with
      | none => simp [h3, withR, bindS] at h
      | some r =>
        simp only [h3, withR, bindS] at h
        rw [show c.den x = MC.den x ⟨c.l, r, c.st⟩ by simp [MC.den, hR r h3 x]]
        exact mstep_sound δ x _ _ h

theorem ite_reach (c : MC Q) (p : Bool) (o : Option (MC Q)) (h : ∀ c', o = some c' → Reach δ c c') :
    ∀ c', (if p = true then o else none) = some c' → Reach δ c c' := by
  intro c' hc
  split at hc
  · exact h c' hc
  · cases hc

theorem bindF_reach (c : MC Q) (o : Option (MC Q)) (ho : ∀ d, o = some d → ∀ x, c.den x = d.den x)
    (f : MC Q → Option (MC Q)) (hf : ∀ d c', f d = some c' → Reach δ d c') :
    ∀ c', bindF o f = some c' → Reach δ c c' := by
  intro c' h x
  cases o with
  | none => cases h
  | some d =>
    simp only [bindF] at h
    obtain ⟨n, hn⟩ := hf d c' h x
    exact ⟨n, by rw [ho d rfl x]; exact hn⟩

theorem crossRany_reach : ∀ c c', crossRany δ c = some c' → Reach δ c c' := by
  intro c
  unfold crossRany
  refine orElse_reach δ (fun c' h x => crossRa_sound δ 0 x c c' h) ?_
  refine orElse_reach δ (fun c' h x => crossRa_sound δ 1 x c c' h) ?_
  refine orElse_reach δ (fun c' h x => crossRa_sound δ 2 x c c' h) ?_
  exact fun c' h x => crossRa_sound δ 3 x c c' h

theorem crossLany_reach : ∀ c c', crossLany δ c = some c' → Reach δ c c' := by
  intro c
  unfold crossLany
  refine orElse_reach δ (fun c' h x => crossLa_sound δ 1 x c c' h) ?_
  refine orElse_reach δ (fun c' h x => crossLa_sound δ 2 x c c' h) ?_
  exact fun c' h x => crossLa_sound δ 3 x c c' h

theorem candR_reach (c : MC Q) : ∀ c', candR δ c = some c' → Reach δ c c' := by
  have gR : ∀ m, ∀ d', withR c (grp m c.r) = some d' → ∀ x, c.den x = d'.den x := fun m =>
    withR_den c _ (fun r hr x => grp_den m x c.r r hr blank)
  have rR : ∀ m, ∀ d', withR c (rot m c.r) = some d' → ∀ x, c.den x = d'.den x := fun m =>
    withR_den c _ (fun r hr x => rot_den m x c.r r hr blank)
  unfold candR
  refine orElse_reach δ (ite_reach δ c _ _ (crossRany_reach δ c)) ?_
  refine orElse_reach δ (ite_reach δ c _ _ (orElse_reach δ (bindF_reach δ c _ (gR 3) _ (crossRany_reach δ))
    (bindF_reach δ c _ (gR 2) _ (crossRany_reach δ)))) ?_
  refine orElse_reach δ (ite_reach δ c _ _ (bindF_reach δ c _ (rR 1) _ (crossRany_reach δ))) ?_
  refine orElse_reach δ (ite_reach δ c _ _ (bindF_reach δ c _ (rR 2) _ (crossRany_reach δ))) ?_
  exact ite_reach δ c _ _ (bindF_reach δ c _ (rR 3) _ (crossRany_reach δ))

theorem candL_reach (c : MC Q) : ∀ c', candL δ c = some c' → Reach δ c c' := by
  have gL : ∀ m, ∀ d', withL c (grp m c.l) = some d' → ∀ x, c.den x = d'.den x := fun m =>
    withL_den c _ (fun l hl x => grp_den m x c.l l hl blank)
  have rL : ∀ m, ∀ d', withL c (rot m c.l) = some d' → ∀ x, c.den x = d'.den x := fun m =>
    withL_den c _ (fun l hl x => rot_den m x c.l l hl blank)
  unfold candL
  refine orElse_reach δ (ite_reach δ c _ _ (crossLany_reach δ c)) ?_
  refine orElse_reach δ (ite_reach δ c _ _ (orElse_reach δ (bindF_reach δ c _ (gL 3) _ (crossLany_reach δ))
    (bindF_reach δ c _ (gL 2) _ (crossLany_reach δ)))) ?_
  refine orElse_reach δ (ite_reach δ c _ _ (bindF_reach δ c _ (rL 1) _ (crossLany_reach δ))) ?_
  refine orElse_reach δ (ite_reach δ c _ _ (bindF_reach δ c _ (rL 2) _ (crossLany_reach δ))) ?_
  exact ite_reach δ c _ _ (bindF_reach δ c _ (rL 3) _ (crossLany_reach δ))

theorem next_sound (c c' : MC Q) (b : Bool) (h : next δ c = some (c', b)) (x : List Nat) :
    ∃ n, (b = true → 1 ≤ n) ∧ steps δ n (c.den x) = some (c'.den x) := by
  unfold next at h
  split at h
  · rename_i d hd
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨n, hn⟩ := orElse_reach δ (candR_reach δ c) (candL_reach δ c) d hd x
    exact ⟨n, (fun h => by cases h), hn⟩
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨d, hd, rfl, rfl⟩ := h
    refine ⟨1, fun _ => Nat.le_refl 1, ?_⟩
    rw [steps_succ_of_step δ 0 (stepA_sound δ x c d hd)]; rfl

theorem auto_sound (q : Q) (R : List Tok) : ∀ (f : Nat) (stepped : Bool) (c : MC Q), auto δ q R f stepped c = true →
    ∀ x, ∃ n, (stepped = false → 1 ≤ n) ∧ steps δ n (c.den x) = some (MC.den x ⟨[], R, q⟩) := by
  intro f
  induction f with
  | zero => intro s c h; simp [auto] at h
  | succ f ih =>
    intro s c h x
    simp only [auto] at h
    -- the normalized configuration has the same tape
    generalize hA : (decide (c.st = q) && c.l.all (· == .b false)) = atEnd at h
    have hd : ∀ d : MC Q, d = (if atEnd = true then ⟨c.l, norm c.r, c.st⟩ else c) → d.den x = c.den x := by
      intro d hd'
      subst hd'
      split
      · simp [MC.den, norm_den]
      · rfl
    generalize hc : (if atEnd = true then (⟨c.l, norm c.r, c.st⟩ : MC Q) else c) = d at h
    rw [← hd d hc.symm]
    split at h
    · rename_i hc2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc2
      obtain ⟨⟨h1, h2⟩, h3⟩ := hc2
      rw [h2] at hA
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hA
      have hdl : d.l = c.l := by rw [← hc]; split <;> rfl
      have hds : d.st = c.st := by rw [← hc]; split <;> rfl
      refine ⟨0, fun h => by simp_all, ?_⟩
      simp only [steps, MC.den, Option.some.injEq]
      rw [hdl, allFalse_den x c.l hA.2, h3, hds, hA.1]
      rfl
    · split at h
      · rename_i c' b hn
        obtain ⟨n1, hn1, hs1⟩ := next_sound δ d c' b hn x
        obtain ⟨n2, hn2, hs2⟩ := ih (s || b) c' h x
        refine ⟨n1 + n2, ?_, steps_seq δ hs1 hs2⟩
        intro hs
        cases b with
        | true => have := hn1 rfl; omega
        | false =>
          simp only [Bool.or_false] at hn2
          have := hn2 hs; omega
      · cases h

/-- What a certificate states: from `c`, for every value of the variables, at least one step leads to
`⟨blank, R, q⟩`. -/
theorem auto_reach (q : Q) (R : List Tok) (f : Nat) (c : MC Q) (h : auto δ q R f false c = true) (x : List Nat) :
    ∃ n, 1 ≤ n ∧ steps δ n (c.den x) = some (MC.den x ⟨[], R, q⟩) := by
  obtain ⟨n, h1, h2⟩ := auto_sound δ q R f false c h x
  exact ⟨n, h1 rfl, h2⟩

end

end Sym
end TM
