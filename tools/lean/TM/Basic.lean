/-!
# Two-symbol Turing machines, for any machine

The semantics of `bb6-holdout/lean/BB6/Basic.lean`, with the transition table as a parameter `δ` instead of one
fixed machine.  A machine file defines its states as an inductive type and its table as a function by `match`
(`tools/py/leangen.py` writes one from the standard text format), and then every lemma here applies to it.

The tape is split into two streams of cells: `l n` is the cell `n + 1` places to the left of the head, `r 0` is the
cell under the head, `r (n + 1)` the cell `n + 1` places to its right.  Both streams are infinite, so a configuration
with "the rest of the tape unknown" is a configuration whose streams are variables: a lemma stated for all `L R : Tape`
holds for any surrounding tape, and a proof that is a chain of machine steps never inspects `L` or `R`.

Patterns are written with `cons` (one cell), `app` (a finite word) and `rep` (a word repeated); `blank` is the all-zero
tape.  The left stream lists cells nearest first, so a word written left to right on the left of the head is reversed:
the tape `L 1 0 0 E>0 1 1 0 R` is `⟨app [false, false, true] L, app [false, true, true, false] R, E⟩`.

`steps n c = some c'` says the machine makes `n` ordinary transitions from `c` to `c'`; `step c = none` says `c` is a
halting configuration.  In the bbchallenge count, where the halting transition is a step, that is a halt after `n + 1`
steps.
-/

namespace TM

/-- The tape to one side of the head, nearest cell first. -/
abbrev Tape := Nat → Bool

/-- `cons a s` puts the cell `a` in front of the stream `s`. -/
def cons (a : Bool) (s : Tape) : Tape := fun n =>
  match n with
  | 0 => a
  | n + 1 => s n

/-- Drop the first cell. -/
def tail (s : Tape) : Tape := fun n => s (n + 1)

/-- Blank tape. -/
def blank : Tape := fun _ => false

/-- A finite word in front of a stream (reading order). -/
def app : List Bool → Tape → Tape
  | [], s => s
  | a :: w, s => cons a (app w s)

/-- The word `w` repeated `n` times in front of `s`. -/
def rep : Nat → List Bool → Tape → Tape
  | 0, _, s => s
  | n + 1, w, s => app w (rep n w s)

@[simp] theorem cons_zero (a : Bool) (s : Tape) : cons a s 0 = a := rfl
@[simp] theorem cons_succ (a : Bool) (s : Tape) (n : Nat) : cons a s (n + 1) = s n := rfl
@[simp] theorem tail_cons (a : Bool) (s : Tape) : tail (cons a s) = s := rfl
@[simp] theorem app_nil (s : Tape) : app [] s = s := rfl
@[simp] theorem app_cons (a : Bool) (w : List Bool) (s : Tape) : app (a :: w) s = cons a (app w s) := rfl
@[simp] theorem rep_zero (w : List Bool) (s : Tape) : rep 0 w s = s := rfl
@[simp] theorem rep_succ (n : Nat) (w : List Bool) (s : Tape) : rep (n + 1) w s = app w (rep n w s) := rfl

theorem tail_blank : tail blank = blank := rfl

/-- A blank cell in front of blank tape is blank tape (true, but not by `rfl`). -/
theorem cons_false_blank : cons false blank = blank := by
  funext n; cases n <;> rfl

theorem app_app (v w : List Bool) (s : Tape) : app v (app w s) = app (v ++ w) s := by
  induction v with
  | nil => rfl
  | cons a v ih => simp [app, ih]

theorem rep_add (a b : Nat) (w : List Bool) (s : Tape) : rep (a + b) w s = rep a w (rep b w s) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e, rep_succ, rep_succ, ih]

/-- A repeat absorbs one more copy of its word placed behind it. -/
theorem rep_app_comm (n : Nat) (w : List Bool) (s : Tape) : rep n w (app w s) = rep (n + 1) w s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, ih]; rfl

/-- Re-bracketing a repeat: `x (y)^n = (x y')^n x'` when `x ++ y = y' ++ x`, as words. -/
theorem rep_rotate (n : Nat) (x y y' : List Bool) (h : x ++ y = y' ++ x) (s : Tape) :
    app x (rep n y s) = rep n y' (app x s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    show app x (app y (rep n y s)) = app y' (rep n y' (app x s))
    rw [← ih, app_app, h, ← app_app]

inductive Dir where
  | L | R
  deriving DecidableEq, Repr

variable {Q : Type}

/-- A configuration: left stream, right stream (head on `r 0`), state. -/
structure Cfg (Q : Type) where
  l : Tape
  r : Tape
  st : Q

section
variable (δ : Q → Bool → Option (Bool × Dir × Q))

/-- One step; `none` when the machine halts. -/
def step (c : Cfg Q) : Option (Cfg Q) :=
  match δ c.st (c.r 0) with
  | none => none
  | some (w, .R, s) => some ⟨cons w c.l, tail c.r, s⟩
  | some (w, .L, s) => some ⟨tail c.l, cons (c.l 0) (cons w (tail c.r)), s⟩

/-- `n` steps; `none` if the machine halts on the way. -/
def steps : Nat → Cfg Q → Option (Cfg Q)
  | 0, c => some c
  | n + 1, c =>
    match step δ c with
    | none => none
    | some c' => steps n c'

/-- The configuration of the run from blank tape in state `q`. -/
def blankCfg (q : Q) : Cfg Q := ⟨blank, blank, q⟩

@[simp] theorem steps_zero (c : Cfg Q) : steps δ 0 c = some c := rfl

theorem steps_succ_of_step {c c' : Cfg Q} (n : Nat) (h : step δ c = some c') :
    steps δ (n + 1) c = steps δ n c' := by
  simp [steps, h]

/-- Chaining two runs. -/
theorem steps_seq {a b : Nat} {c c' c'' : Cfg Q} (h₁ : steps δ a c = some c') (h₂ : steps δ b c' = some c'') :
    steps δ (a + b) c = some c'' := by
  induction a generalizing c with
  | zero =>
    simp [steps] at h₁
    subst h₁
    simpa using h₂
  | succ a ih =>
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e]
    cases hs : step δ c with
    | none => simp [steps, hs] at h₁
    | some d =>
      rw [steps_succ_of_step δ a hs] at h₁
      rw [steps_succ_of_step δ (a + b) hs]
      exact ih h₁

/-- The same run with its length written another way (for step counts that `omega` equates). -/
theorem steps_congr {a b : Nat} (h : a = b) {c : Cfg Q} {x : Option (Cfg Q)} (hc : steps δ a c = x) :
    steps δ b c = x := h ▸ hc

/-- A halting run: once a step halts, every longer run is `none`. -/
theorem steps_halt {a : Nat} {c c' : Cfg Q} (h₁ : steps δ a c = some c') (h₂ : step δ c' = none) (b : Nat) :
    steps δ (a + (b + 1)) c = none := by
  induction a generalizing c with
  | zero =>
    simp [steps] at h₁
    subst h₁
    simp [steps, h₂]
  | succ a ih =>
    cases hs : step δ c with
    | none => simp [steps, hs] at h₁
    | some d =>
      rw [steps_succ_of_step δ a hs] at h₁
      have e : a + 1 + (b + 1) = (a + (b + 1)) + 1 := by omega
      rw [e, steps_succ_of_step δ (a + (b + 1)) hs]
      exact ih h₁

/-- A run that is defined is defined at every shorter length. -/
theorem steps_le {a b : Nat} {c c'' : Cfg Q} (h : steps δ (a + b) c = some c'') :
    ∃ c', steps δ a c = some c' := by
  induction a generalizing c with
  | zero => exact ⟨c, rfl⟩
  | succ a ih =>
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e] at h
    cases hs : step δ c with
    | none => simp [steps, hs] at h
    | some d =>
      rw [steps_succ_of_step δ (a + b) hs] at h
      obtain ⟨c', hc'⟩ := ih h
      exact ⟨c', by rw [steps_succ_of_step δ a hs]; exact hc'⟩

/-- The machine halts from `c`: some run from `c` ends at a halting configuration. -/
def Halts (c : Cfg Q) : Prop := ∃ n c', steps δ n c = some c' ∧ step δ c' = none

/-- If every run length is defined, the machine never halts. -/
theorem not_halts_of_forall {c : Cfg Q} (h : ∀ n, ∃ c', steps δ n c = some c') : ¬ Halts δ c := by
  rintro ⟨n, c', h₁, h₂⟩
  obtain ⟨c'', h₃⟩ := h (n + 1)
  rw [steps_halt δ h₁ h₂ 0] at h₃
  cases h₃

/-- A run defined for every length `n` with `P n`, where `P` is unbounded, is defined for every length. -/
theorem forall_of_unbounded {c : Cfg Q} (P : Nat → Prop) (hP : ∀ n, ∃ m, n ≤ m ∧ P m)
    (h : ∀ m, P m → ∃ c', steps δ m c = some c') : ∀ n, ∃ c', steps δ n c = some c' := by
  intro n
  obtain ⟨m, hnm, hm⟩ := hP n
  obtain ⟨c', hc'⟩ := h m hm
  have e : m = n + (m - n) := by omega
  rw [e] at hc'
  exact steps_le δ hc'

/-! ## Crossing a repeated word

A shift rule: if one pass of the machine over a word `w` brings the head, in the same state, to the far side of the
word, never looking past it (a statement for all `L R`), then it crosses `w` repeated any number of times.  A word
`u` may travel with the head (it is on the side the head leaves from, before and after).
-/

/-- Crossing to the right: `L u q> w^k R` becomes `L v^k u q> R` (left words written nearest first). -/
theorem cross_r {s : Nat} {q : Q} {u w v : List Bool}
    (h : ∀ L R : Tape, steps δ s ⟨app u L, app w R, q⟩ = some ⟨app u (app v L), R, q⟩) (k : Nat) :
    ∀ L R : Tape, steps δ (k * s) ⟨app u L, rep k w R, q⟩ = some ⟨app u (rep k v L), R, q⟩ := by
  induction k with
  | zero => intro L R; simp
  | succ k ih =>
    intro L R
    have e : (k + 1) * s = s + k * s := by rw [Nat.succ_mul, Nat.add_comm]
    rw [e]
    have h₂ := ih (app v L) R
    rw [rep_app_comm] at h₂
    exact steps_seq δ (h L (rep k w R)) h₂

/-- Crossing to the left: `w^k q> u R` becomes `q> u v^k R` (left words written nearest first). -/
theorem cross_l {s : Nat} {q : Q} {u w v : List Bool}
    (h : ∀ L R : Tape, steps δ s ⟨app w L, app u R, q⟩ = some ⟨L, app u (app v R), q⟩) (k : Nat) :
    ∀ L R : Tape, steps δ (k * s) ⟨rep k w L, app u R, q⟩ = some ⟨L, app u (rep k v R), q⟩ := by
  induction k with
  | zero => intro L R; simp
  | succ k ih =>
    intro L R
    have e : (k + 1) * s = s + k * s := by rw [Nat.succ_mul, Nat.add_comm]
    rw [e]
    have h₂ := ih L (app v R)
    rw [rep_app_comm] at h₂
    exact steps_seq δ (h (rep k w L) R) h₂

end

end TM
