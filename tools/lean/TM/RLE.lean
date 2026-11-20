import TM.Basic

/-!
# A run-length simulator proved to agree with `steps`, with room for proved jumps

Long bounded runs (no halt in the first N steps, for N far beyond what a cell-by-cell simulator reaches) as one
evaluation.  The tape is kept as two lists of *runs* `(w, n)`, the word `w` repeated `n` times, and the simulator
makes one of three kinds of move:

* a **jump**: a rule that the caller proves for its own machine (for example a closed form for a whole visit of
  a counter), given as a function `jump` with a soundness hypothesis (`JumpOK`);
* a **crossing**: the head faces a run `w^n` (with a few literal cells `u` beside it), one copy of `w` is crossed
  by a bounded simulation that never looks past `u` and `w` (`bsteps`, `bsteps_spec`), so all `n` copies are
  crossed at once (`cross_r`, `cross_l` of `TM/Basic.lean`);
* one ordinary **step**.

Step counts of jumps may be lower bounds (`ReachGe`: at least so many steps); crossings and steps are exact.  So the
result of a run is a lower bound on the steps made without a halt:

* `run_ok`: if `run fuel c 0 N = true` then the machine makes `N` steps from `c` without halting;
* `run_halts`: if `runH fuel c = true`, the machine halts from `c`.

Only the soundness of each move is proved.  Which move is tried when (the search for the length of a crossing,
the folding of literal cells into runs) is ordinary unverified code: a bad choice can only make a move fail.  For
any machine `δ` with decidable states.  The big runs are evaluated by `native_decide`.
-/

namespace TM

variable {Q : Type}

/-! ## Reaching a configuration in at least `n` steps -/

section
variable (δ : Q → Bool → Option (Bool × Dir × Q))

/-- `c'` is reached from `c` after some number `m ≥ n` of steps. -/
def ReachGe (c c' : Cfg Q) (n : Nat) : Prop := ∃ m, n ≤ m ∧ steps δ m c = some c'

theorem ReachGe.refl (c : Cfg Q) : ReachGe δ c c 0 := ⟨0, Nat.le_refl _, rfl⟩

theorem ReachGe.of_steps {n : Nat} {c c' : Cfg Q} (h : steps δ n c = some c') : ReachGe δ c c' n :=
  ⟨n, Nat.le_refl _, h⟩

theorem ReachGe.trans {a b : Nat} {c₁ c₂ c₃ : Cfg Q} (h₁ : ReachGe δ c₁ c₂ a) (h₂ : ReachGe δ c₂ c₃ b) :
    ReachGe δ c₁ c₃ (a + b) := by
  obtain ⟨m₁, l₁, s₁⟩ := h₁
  obtain ⟨m₂, l₂, s₂⟩ := h₂
  exact ⟨m₁ + m₂, by omega, steps_seq δ s₁ s₂⟩

theorem ReachGe.mono {a b : Nat} {c c' : Cfg Q} (h : ReachGe δ c c' a) (hb : b ≤ a) : ReachGe δ c c' b := by
  obtain ⟨m, l, s⟩ := h
  exact ⟨m, by omega, s⟩

/-- Reaching after at least `n` steps means the first `n` steps are made without a halt. -/
theorem ReachGe.runs {n : Nat} {c c' : Cfg Q} (h : ReachGe δ c c' n) : ∃ d, steps δ n c = some d := by
  obtain ⟨m, l, s⟩ := h
  have e : m = n + (m - n) := by omega
  rw [e] at s
  exact steps_le δ s

end

/-! ## Runs -/

/-- One side of the tape as runs `(w, n)` (the word `w`, nearest cell first, `n` times), nearest run first, then
blank tape. -/
abbrev Side := List (List Bool × Nat)

/-- The tape a side stands for. -/
def den : Side → Tape
  | [] => blank
  | (w, n) :: s => rep n w (den s)

@[simp] theorem den_nil : den [] = blank := rfl
@[simp] theorem den_cons (w : List Bool) (n : Nat) (s : Side) : den ((w, n) :: s) = rep n w (den s) := rfl

theorem rep_nil_word (n : Nat) (s : Tape) : rep n [] s = s := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem rep_one (w : List Bool) (s : Tape) : rep 1 w s = app w s := rfl

/-- A run in front, empty runs dropped. -/
def rcons (w : List Bool) (n : Nat) (s : Side) : Side :=
  if n = 0 ∨ w = [] then s else (w, n) :: s

theorem den_rcons (w : List Bool) (n : Nat) (s : Side) : den (rcons w n s) = rep n w (den s) := by
  unfold rcons
  split
  · rename_i h
    rcases h with h | h
    · subst h; rfl
    · subst h; rw [rep_nil_word]
  · rfl

/-- A run in front, merged with the first run when that is the same word. -/
def rconsM (w : List Bool) (n : Nat) (s : Side) : Side :=
  match s with
  | (w', m) :: s' => if w' = w then (w, n + m) :: s' else rcons w n s
  | [] => rcons w n []

theorem den_rconsM (w : List Bool) (n : Nat) (s : Side) : den (rconsM w n s) = rep n w (den s) := by
  unfold rconsM
  match s with
  | [] => exact den_rcons w n []
  | (w', m) :: s' =>
    simp only
    split
    · rename_i h; subst h; simp [rep_add]
    · exact den_rcons w n _

/-- Literal cells in front, one run `([b], 1)` each. -/
def pushCells : List Bool → Side → Side
  | [], s => s
  | b :: u, s => ([b], 1) :: pushCells u s

theorem den_pushCells (u : List Bool) (s : Side) : den (pushCells u s) = app u (den s) := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [pushCells, ih]

/-- The first cell and the rest of a side. -/
def pop : Side → Bool × Side
  | [] => (false, [])
  | ([], _) :: s => pop s
  | (_, 0) :: s => pop s
  | (a :: w, n + 1) :: s => (a, pushCells w (rcons (a :: w) n s))

theorem den_pop (s : Side) : den s = cons (pop s).1 (den (pop s).2) := by
  induction s with
  | nil => exact cons_false_blank.symm
  | cons p s ih =>
    obtain ⟨w, n⟩ := p
    match w, n with
    | [], n => simp only [pop, den_cons, rep_nil_word]; exact ih
    | a :: w, 0 => simp only [pop, den_cons, rep_zero]; exact ih
    | a :: w, n + 1 =>
      simp only [pop, den_cons, rep_succ, den_pushCells, den_rcons, app_cons]

/-- The first `j` cells of a side, when they are literal runs `([b], 1)`. -/
def peelLits : Nat → Side → Option (List Bool × Side)
  | 0, s => some ([], s)
  | j + 1, ([b], 1) :: s =>
    match peelLits j s with
    | some (u, s') => some (b :: u, s')
    | none => none
  | _ + 1, _ => none

theorem peelLits_spec : ∀ (j : Nat) (s : Side) (u : List Bool) (s' : Side),
    peelLits j s = some (u, s') → den s = app u (den s')
  | 0, s, u, s', h => by simp [peelLits] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | j + 1, ([b], 1) :: s, u, s', h => by
    simp only [peelLits] at h
    cases e : peelLits j s with
    | none => rw [e] at h; cases h
    | some p =>
      obtain ⟨u', s''⟩ := p
      rw [e] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      simp [peelLits_spec j s u' s'' e]
  | j + 1, [], _, _, h => by simp [peelLits] at h
  | j + 1, ([], _) :: _, _, _, h => by simp [peelLits] at h
  | j + 1, ([_], 0) :: _, _, _, h => by simp [peelLits] at h
  | j + 1, ([_], _ + 2) :: _, _, _, h => by simp [peelLits] at h
  | j + 1, (_ :: _ :: _, _) :: _, _, _, h => by simp [peelLits] at h

/-- The first `j` cells of a side, whatever runs they are in (it splits runs). -/
def peel : Nat → Side → List Bool × Side
  | 0, s => ([], s)
  | j + 1, s =>
    let p := pop s
    let q := peel j p.2
    (p.1 :: q.1, q.2)

theorem peel_spec : ∀ (j : Nat) (s : Side), den s = app (peel j s).1 (den (peel j s).2)
  | 0, s => rfl
  | j + 1, s => by
    simp only [peel, app_cons]
    rw [den_pop s, ← peel_spec j (pop s).2]

/-- The first `j` cells, as an option (for the crossings). -/
def peelS (j : Nat) (s : Side) : Option (List Bool × Side) := some (peel j s)

theorem peelS_spec (j : Nat) (s : Side) (u : List Bool) (s' : Side) (h : peelS j s = some (u, s')) :
    den s = app u (den s') := by
  simp only [peelS, Option.some.injEq] at h
  rw [peel_spec j s, h]

/-- Fold the literal cells in front into a run of one of the words `ws`: when the first `|w|` cells spell `w`
and a run of `w` follows, it grows by one; when the first `2|w|` cells spell `w w`, they become a run of two.
Tried only when the first run is a single literal cell. -/
def fold (ws : List (List Bool)) (s : Side) : Side :=
  match s with
  | (_, 1) :: _ =>
    match ws with
    | [] => s
    | w :: ws' =>
      let p := peel w.length s
      if p.1 = w then
        match p.2 with
        | (w', m) :: r => if w' = w then (w, m + 1) :: r else
            let p2 := peel w.length p.2
            if p2.1 = w then rconsM w 2 p2.2 else fold ws' s
        | [] => fold ws' s
      else fold ws' s
  | _ => s

theorem den_fold (ws : List (List Bool)) (s : Side) : den (fold ws s) = den s := by
  induction ws with
  | nil => unfold fold; split <;> rfl
  | cons w ws ih =>
    unfold fold
    split
    · rename_i b t
      simp only
      split
      · rename_i hw
        have e1 := peel_spec w.length ((b, 1) :: t)
        rw [hw] at e1
        split
        · rename_i w' m r hr
          split
          · rename_i hw'
            subst hw'
            rw [e1, hr]; simp [rep_succ]
          · split
            · rename_i hw2
              have e2 := peel_spec w.length (peel w.length ((b, 1) :: t)).2
              rw [hw2] at e2
              rw [e1, e2, den_rconsM]; simp [rep_succ]
            · exact ih
        · exact ih
      · exact ih
    · rfl

/-! ## Bounded simulation of a finite piece of tape -/

section
variable (δ : Q → Bool → Option (Bool × Dir × Q))

/-- One step on a finite piece `(left nearest first, right from the head, state)`; `none` if the machine halts or
the head would read a cell outside the piece. -/
def bstep : List Bool × List Bool × Q → Option (List Bool × List Bool × Q)
  | (_, [], _) => none
  | (l, a :: r, q) =>
    match δ q a with
    | none => none
    | some (w, .R, s) => some (w :: l, r, s)
    | some (w, .L, s) =>
      match l with
      | [] => none
      | b :: l' => some (l', b :: w :: r, s)

def bsteps : Nat → List Bool × List Bool × Q → Option (List Bool × List Bool × Q)
  | 0, c => some c
  | n + 1, c =>
    match bstep δ c with
    | none => none
    | some c' => bsteps n c'

theorem bstep_spec {l r l' r' : List Bool} {q q' : Q} (h : bstep δ (l, r, q) = some (l', r', q')) (L R : Tape) :
    step δ ⟨app l L, app r R, q⟩ = some ⟨app l' L, app r' R, q'⟩ := by
  match r, h with
  | a :: r, h =>
    simp only [bstep] at h
    unfold step
    simp only [app_cons, cons_zero]
    cases e : δ q a with
    | none => rw [e] at h; cases h
    | some t =>
      obtain ⟨w, d, s⟩ := t
      rw [e] at h
      cases d with
      | R =>
        simp at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rfl
      | L =>
        match l, h with
        | b :: l, h =>
          simp at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          rfl

theorem bsteps_spec : ∀ (n : Nat) {l r l' r' : List Bool} {q q' : Q},
    bsteps δ n (l, r, q) = some (l', r', q') → ∀ L R : Tape,
    steps δ n ⟨app l L, app r R, q⟩ = some ⟨app l' L, app r' R, q'⟩
  | 0, l, r, l', r', q, q', h, L, R => by
    simp [bsteps] at h; obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  | n + 1, l, r, l', r', q, q', h, L, R => by
    simp only [bsteps] at h
    cases e : bstep δ (l, r, q) with
    | none => rw [e] at h; cases h
    | some c =>
      obtain ⟨l₁, r₁, q₁⟩ := c
      rw [e] at h
      rw [steps_succ_of_step δ n (bstep_spec δ e L R)]
      exact bsteps_spec n h L R

/-- Unverified search: the number of steps until the head leaves the piece on the right (at most `fuel`). -/
def findR : Nat → Nat → List Bool × List Bool × Q → Option Nat
  | _, acc, (_, [], _) => some acc
  | 0, _, _ => none
  | fuel + 1, acc, c =>
    match bstep δ c with
    | none => none
    | some c' => findR fuel (acc + 1) c'

/-- Unverified search: the number of steps until the head, in state `q0`, is at the left end of the piece with
the word `u` in front of it. -/
def findL [DecidableEq Q] (q0 : Q) (u : List Bool) : Nat → Nat → List Bool × List Bool × Q → Option Nat
  | 0, _, _ => none
  | fuel + 1, acc, c =>
    match bstep δ c with
    | none => none
    | some (l', r', q') =>
      if l' = [] ∧ q' = q0 ∧ r'.take u.length = u then some (acc + 1) else findL q0 u fuel (acc + 1) (l', r', q')

end

/-! ## Configurations of runs and the moves -/

/-- A configuration with both sides as runs. -/
structure RCfg (Q : Type) where
  l : Side
  r : Side
  st : Q

def RCfg.toCfg (c : RCfg Q) : Cfg Q := ⟨den c.l, den c.r, c.st⟩

section
variable [DecidableEq Q] (δ : Q → Bool → Option (Bool × Dir × Q))

/-- A jump rule is sound: every jump it makes is a run of at least the steps it claims. -/
def JumpOK (jump : RCfg Q → Option (RCfg Q × Nat)) : Prop :=
  ∀ c c' n, jump c = some (c', n) → ReachGe δ c.toCfg c'.toCfg n

/-- One ordinary step; literal cells are folded into runs of the words `ws`. -/
def rstep (ws : List (List Bool)) (c : RCfg Q) : Option (RCfg Q) :=
  match δ c.st (pop c.r).1 with
  | none => none
  | some (w, .R, s) => some ⟨fold ws (([w], 1) :: c.l), (pop c.r).2, s⟩
  | some (w, .L, s) => some ⟨(pop c.l).2, fold ws (([(pop c.l).1], 1) :: ([w], 1) :: (pop c.r).2), s⟩

omit [DecidableEq Q] in
theorem rstep_spec (ws : List (List Bool)) (c : RCfg Q) :
    step δ c.toCfg = (rstep δ ws c).map RCfg.toCfg := by
  obtain ⟨l, r, q⟩ := c
  have hr := den_pop r
  have hl := den_pop l
  unfold rstep step RCfg.toCfg
  simp only
  rw [hr, cons_zero]
  cases δ q (pop r).1 with
  | none => rfl
  | some t =>
    obtain ⟨w, d, s⟩ := t
    cases d with
    | R => simp only [Option.map_some, den_fold, den_cons, rep_one, tail_cons]; rfl
    | L =>
      simp only [Option.map_some, den_fold, den_cons, rep_one, tail_cons, app_cons, app_nil]
      rw [hl]; rfl

/-- Cross a run `w^n` on the right, with the `j` literal cells `u` on the left carried along. -/
def crossR (ws : List (List Bool)) (j : Nat) (c : RCfg Q) : Option (RCfg Q × Nat) :=
  match c.r with
  | (w, n) :: r' =>
    if w.length < 2 then none else
    match peelS j c.l with
    | none => none
    | some (u, l'') =>
      match findR δ (8 * (w.length + u.length) + 16) 0 (u, w, c.st) with
      | none => none
      | some s =>
        match bsteps δ s (u, w, c.st) with
        | some (ll, [], q') =>
          if q' = c.st ∧ ll.take u.length = u then
            some (⟨fold ws (pushCells u (rconsM (ll.drop u.length) n l'')), r', c.st⟩, n * s)
          else none
        | _ => none
  | [] => none

theorem crossR_spec (ws : List (List Bool)) (j : Nat) (c c' : RCfg Q) (n : Nat) (h : crossR δ ws j c = some (c', n)) :
    steps δ n c.toCfg = some c'.toCfg := by
  obtain ⟨l, r, q⟩ := c
  unfold crossR at h
  simp only at h
  match r, h with
  | (w, k) :: r', h =>
    simp only at h
    split at h
    · cases h
    cases ep : peelS j l with
    | none => rw [ep] at h; cases h
    | some p =>
      obtain ⟨u, l''⟩ := p
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
            · rename_i hc
              obtain ⟨hq, hu⟩ := hc
              subst hq
              simp at h
              obtain ⟨rfl, rfl⟩ := h
              have one : ∀ L R : Tape, steps δ s ⟨app u L, app w R, q'⟩ =
                  some ⟨app u (app (ll.drop u.length) L), R, q'⟩ := by
                intro L R
                have := bsteps_spec δ s eb L R
                have e : u ++ ll.drop u.length = ll := by
                  conv => rhs; rw [← List.take_append_drop u.length ll]
                  rw [hu]
                rw [app_app, e]
                exact this
              have hc := cross_r δ one k (den l'') (den r')
              unfold RCfg.toCfg
              simp only [den_fold, den_cons, den_pushCells, den_rconsM]
              rw [peelS_spec j l u l'' ep]
              exact hc
            · cases h

/-- Cross a run `w^n` on the left, with the `j` literal cells `u` on the right carried along. -/
def crossL (ws : List (List Bool)) (j : Nat) (c : RCfg Q) : Option (RCfg Q × Nat) :=
  match c.l with
  | (w, n) :: l' =>
    if w.length < 2 then none else
    match peelS j c.r with
    | none => none
    | some (u, r'') =>
      match findL δ c.st u (8 * (w.length + u.length) + 16) 0 (w, u, c.st) with
      | none => none
      | some s =>
        match bsteps δ s (w, u, c.st) with
        | some ([], rr, q') =>
          if q' = c.st ∧ rr.take u.length = u then
            some (⟨l', fold ws (pushCells u (rconsM (rr.drop u.length) n r'')), c.st⟩, n * s)
          else none
        | _ => none
  | [] => none

theorem crossL_spec (ws : List (List Bool)) (j : Nat) (c c' : RCfg Q) (n : Nat) (h : crossL δ ws j c = some (c', n)) :
    steps δ n c.toCfg = some c'.toCfg := by
  obtain ⟨l, r, q⟩ := c
  unfold crossL at h
  simp only at h
  match l, h with
  | (w, k) :: l', h =>
    simp only at h
    split at h
    · cases h
    cases ep : peelS j r with
    | none => rw [ep] at h; cases h
    | some p =>
      obtain ⟨u, r''⟩ := p
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
            · rename_i hc
              obtain ⟨hq, hu⟩ := hc
              subst hq
              simp at h
              obtain ⟨rfl, rfl⟩ := h
              have one : ∀ L R : Tape, steps δ s ⟨app w L, app u R, q'⟩ =
                  some ⟨L, app u (app (rr.drop u.length) R), q'⟩ := by
                intro L R
                have := bsteps_spec δ s eb L R
                have e : u ++ rr.drop u.length = rr := by
                  conv => rhs; rw [← List.take_append_drop u.length rr]
                  rw [hu]
                rw [app_app, e]
                exact this
              have hc := cross_l δ one k (den l') (den r'')
              unfold RCfg.toCfg
              simp only [den_fold, den_cons, den_pushCells, den_rconsM]
              rw [peelS_spec j r u r'' ep]
              exact hc
            · cases h

/-- Split the first run `w^n` (n ≥ 2) as `w^(n mod 2) (w w)^(n / 2)`, so that a crossing can take two copies of
`w` at a time. -/
def regroup : Side → Option Side
  | (w, n + 2) :: s => some (rcons w ((n + 2) % 2) ((w ++ w, (n + 2) / 2) :: s))
  | _ => none

theorem rep_double_word (n : Nat) (w : List Bool) (s : Tape) : rep (2 * n) w s = rep n (w ++ w) s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, rep_succ, rep_succ, ih, app_app, rep_succ]

theorem regroup_spec {s s' : Side} (h : regroup s = some s') : den s' = den s := by
  match s, h with
  | (w, n + 2) :: s, h =>
    simp only [regroup, Option.some.injEq] at h
    subst h
    rw [den_rcons, den_cons, ← rep_double_word, ← rep_add, den_cons]
    congr 1
    omega

/-- `a`, or else `f ()` (evaluated only when `a` is `none`). -/
def orL {α : Type} (a : Option α) (f : Unit → Option α) : Option α :=
  match a with
  | some x => some x
  | none => f ()

theorem orL_cases {α : Type} {a : Option α} {f : Unit → Option α} {x : α} (h : orL a f = some x) :
    a = some x ∨ f () = some x := by
  unfold orL at h
  cases a with
  | some y => left; exact h
  | none => right; exact h

/-- A regrouped crossing on the right. -/
def crossRG (ws : List (List Bool)) (c : RCfg Q) : Option (RCfg Q × Nat) :=
  match regroup c.r with
  | some r' => crossR δ ws 0 ⟨c.l, r', c.st⟩
  | none => none

theorem crossRG_spec (ws : List (List Bool)) (c c' : RCfg Q) (n : Nat) (h : crossRG δ ws c = some (c', n)) :
    steps δ n c.toCfg = some c'.toCfg := by
  unfold crossRG at h
  cases e : regroup c.r with
  | none => rw [e] at h; cases h
  | some r' =>
    rw [e] at h
    have := crossR_spec δ ws 0 _ _ _ h
    unfold RCfg.toCfg at this ⊢
    rw [regroup_spec e] at this
    exact this

/-- Try the crossings: on the right with 0..3 carried cells, then with the run regrouped, then on the left with
1..3 carried cells. -/
def tryCross (ws : List (List Bool)) (c : RCfg Q) : Option (RCfg Q × Nat) :=
  orL (crossR δ ws 0 c) fun _ => orL (crossR δ ws 1 c) fun _ => orL (crossR δ ws 2 c) fun _ => orL (crossR δ ws 3 c) fun _ =>
  orL (crossRG δ ws c) fun _ => orL (crossL δ ws 1 c) fun _ => orL (crossL δ ws 2 c) fun _ => crossL δ ws 3 c

theorem tryCross_spec (ws : List (List Bool)) (c c' : RCfg Q) (n : Nat) (h : tryCross δ ws c = some (c', n)) :
    steps δ n c.toCfg = some c'.toCfg := by
  unfold tryCross at h
  rcases orL_cases h with h | h; exact crossR_spec δ ws _ c _ _ h
  rcases orL_cases h with h | h; exact crossR_spec δ ws _ c _ _ h
  rcases orL_cases h with h | h; exact crossR_spec δ ws _ c _ _ h
  rcases orL_cases h with h | h; exact crossR_spec δ ws _ c _ _ h
  rcases orL_cases h with h | h; exact crossRG_spec δ ws c _ _ h
  rcases orL_cases h with h | h; exact crossL_spec δ ws _ c _ _ h
  rcases orL_cases h with h | h; exact crossL_spec δ ws _ c _ _ h
  exact crossL_spec δ ws _ c _ _ h

/-! ## The run -/

/-- One move: a jump if the rule gives one, else a crossing, else a step; `none` exactly when the configuration
halts. -/
def move (ws : List (List Bool)) (jump : RCfg Q → Option (RCfg Q × Nat)) (c : RCfg Q) : Option (RCfg Q × Nat) :=
  orL (jump c) fun _ => orL (tryCross δ ws c) fun _ =>
    match rstep δ ws c with
    | some c' => some (c', 1)
    | none => none

theorem move_some (ws : List (List Bool)) {jump : RCfg Q → Option (RCfg Q × Nat)} (hj : JumpOK δ jump)
    {c c' : RCfg Q} {n : Nat} (h : move δ ws jump c = some (c', n)) : ReachGe δ c.toCfg c'.toCfg n := by
  unfold move at h
  rcases orL_cases h with h | h
  · exact hj c c' n h
  rcases orL_cases h with h | h
  · exact ReachGe.of_steps δ (tryCross_spec δ ws c c' n h)
  · cases e : rstep δ ws c with
    | none => rw [e] at h; cases h
    | some d =>
      rw [e] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      have := rstep_spec δ ws c
      rw [e] at this
      exact ReachGe.of_steps δ (by simp [steps, this])

theorem move_none (ws : List (List Bool)) {jump : RCfg Q → Option (RCfg Q × Nat)} {c : RCfg Q}
    (h : move δ ws jump c = none) : step δ c.toCfg = none := by
  unfold move orL at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i e; rw [rstep_spec δ ws c, e]; rfl

/-- Run until at least `target` steps are accounted for (`true`), or a halt or the end of the fuel (`false`). -/
def run (ws : List (List Bool)) (jump : RCfg Q → Option (RCfg Q × Nat)) (target : Nat) :
    Nat → RCfg Q → Nat → Bool
  | 0, _, acc => decide (target ≤ acc)
  | fuel + 1, c, acc =>
    if target ≤ acc then true else
    match move δ ws jump c with
    | none => false
    | some (c', n) => run ws jump target fuel c' (acc + n)

theorem run_spec (ws : List (List Bool)) {jump : RCfg Q → Option (RCfg Q × Nat)} (hj : JumpOK δ jump)
    (target : Nat) : ∀ (fuel : Nat) (c : RCfg Q) (acc : Nat) (c₀ : Cfg Q),
    run δ ws jump target fuel c acc = true → ReachGe δ c₀ c.toCfg acc → ∃ d, steps δ target c₀ = some d
  | 0, c, acc, c₀, h, hr => by
    simp [run] at h
    exact (hr.mono δ h).runs δ
  | fuel + 1, c, acc, c₀, h, hr => by
    simp only [run] at h
    split at h
    · rename_i ht; exact (hr.mono δ ht).runs δ
    · cases e : move δ ws jump c with
      | none => rw [e] at h; cases h
      | some p =>
        obtain ⟨c', n⟩ := p
        rw [e] at h
        exact run_spec ws hj target fuel c' (acc + n) c₀ h (hr.trans δ (move_some δ ws hj e))

/-- **Bounded run**: `run` reaching `target` from `c` proves `target` steps from `c` without a halt. -/
theorem run_ok (ws : List (List Bool)) {jump : RCfg Q → Option (RCfg Q × Nat)} (hj : JumpOK δ jump)
    {target fuel : Nat} {c : RCfg Q} (h : run δ ws jump target fuel c 0 = true) :
    ∃ d, steps δ target c.toCfg = some d :=
  run_spec δ ws hj target fuel c 0 c.toCfg h (ReachGe.refl δ _)

/-- Run until a halt (`true`) or the end of the fuel (`false`). -/
def runH (ws : List (List Bool)) (jump : RCfg Q → Option (RCfg Q × Nat)) : Nat → RCfg Q → Bool
  | 0, _ => false
  | fuel + 1, c =>
    match move δ ws jump c with
    | none => true
    | some (c', _) => runH ws jump fuel c'

theorem runH_spec (ws : List (List Bool)) {jump : RCfg Q → Option (RCfg Q × Nat)} (hj : JumpOK δ jump) :
    ∀ (fuel : Nat) (c : RCfg Q), runH δ ws jump fuel c = true → Halts δ c.toCfg
  | 0, c, h => by simp [runH] at h
  | fuel + 1, c, h => by
    simp only [runH] at h
    cases e : move δ ws jump c with
    | none => exact ⟨0, c.toCfg, rfl, move_none δ ws e⟩
    | some p =>
      obtain ⟨c', n⟩ := p
      rw [e] at h
      obtain ⟨m, d, h1, h2⟩ := runH_spec ws hj fuel c' h
      obtain ⟨k, _, hk⟩ := move_some δ ws hj e
      exact ⟨k + m, d, steps_seq δ hk h1, h2⟩

end

end TM
