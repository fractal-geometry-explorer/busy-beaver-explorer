/-!
# The machine 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE, formalized

Semantics of the 6-state, 2-symbol Turing machine, with the tape split into two streams of cells:
`l n` is the cell `n + 1` places to the left of the head, `r 0` is the cell under the head, `r (n + 1)` the cell
`n + 1` places to its right.  Both streams are infinite, so a configuration with "the rest of the tape unknown" is
simply a configuration whose streams are variables: a lemma stated for all `L R : Tape` holds for any
surrounding tape, and a proof that is a chain of machine steps never inspects `L` or `R` (it cannot: nothing is
known about them).

Patterns are written with `cons` (one cell), `app` (a finite word) and `rep` (a word repeated); `blank` is the
all-zero tape.  Written left to right, a tape `L 1 0 0 E>0 1 1 0 R` is the configuration
`⟨app [0, 0, 1] L, app [0, 1, 1, 0] R, .E⟩`: the left stream lists cells nearest first, so a written word is
reversed on the left and kept in reading order on the right.
-/

namespace BB6

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

/-- The states. `D` has no transition on `1`: that is the halting move. -/
inductive St where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

inductive Dir where
  | L | R
  deriving DecidableEq, Repr

/-- A configuration: left stream, right stream (head on `r 0`), state. -/
structure Cfg where
  l : Tape
  r : Tape
  st : St

/-- The transition table of 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE: (write, move, next state). -/
def trans : St → Bool → Option (Bool × Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true => some (false, .R, .E)
  | .B, false => some (true, .L, .C)
  | .B, true => some (false, .R, .A)
  | .C, false => some (true, .L, .A)
  | .C, true => some (true, .L, .D)
  | .D, false => some (true, .L, .A)
  | .D, true => none
  | .E, false => some (false, .R, .F)
  | .E, true => some (false, .L, .B)
  | .F, false => some (false, .L, .D)
  | .F, true => some (true, .R, .E)

/-- One step; `none` when the machine halts. -/
def step (c : Cfg) : Option Cfg :=
  match trans c.st (c.r 0) with
  | none => none
  | some (w, .R, s) => some ⟨cons w c.l, tail c.r, s⟩
  | some (w, .L, s) => some ⟨tail c.l, cons (c.l 0) (cons w (tail c.r)), s⟩

/-- `n` steps; `none` if the machine halts on the way. -/
def steps : Nat → Cfg → Option Cfg
  | 0, c => some c
  | n + 1, c =>
    match step c with
    | none => none
    | some c' => steps n c'

@[simp] theorem steps_zero (c : Cfg) : steps 0 c = some c := rfl

theorem steps_succ_of_step {c c' : Cfg} (n : Nat) (h : step c = some c') : steps (n + 1) c = steps n c' := by
  simp [steps, h]

/-- Chaining two runs. -/
theorem steps_seq {a b : Nat} {c c' c'' : Cfg} (h₁ : steps a c = some c') (h₂ : steps b c' = some c'') :
    steps (a + b) c = some c'' := by
  induction a generalizing c with
  | zero =>
    simp [steps] at h₁
    subst h₁
    simpa using h₂
  | succ a ih =>
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e]
    cases hs : step c with
    | none => simp [steps, hs] at h₁
    | some d =>
      rw [steps_succ_of_step a hs] at h₁
      rw [steps_succ_of_step (a + b) hs]
      exact ih h₁

/-- A halting run: once a step halts, every longer run is `none`. -/
theorem steps_halt {a : Nat} {c c' : Cfg} (h₁ : steps a c = some c') (h₂ : step c' = none) (b : Nat) :
    steps (a + (b + 1)) c = none := by
  induction a generalizing c with
  | zero =>
    simp [steps] at h₁
    subst h₁
    simp [steps, h₂]
  | succ a ih =>
    cases hs : step c with
    | none => simp [steps, hs] at h₁
    | some d =>
      rw [steps_succ_of_step a hs] at h₁
      have e : a + 1 + (b + 1) = (a + (b + 1)) + 1 := by omega
      rw [e, steps_succ_of_step (a + (b + 1)) hs]
      exact ih h₁

end BB6
