import Machine
import Rules

/-!
# 1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC: the two growth phases, restated and iterated

`Y n p R` is the configuration `0^inf D> 0111011 (011)^n (1011)^p R`: the head in state D at the left end, then
two growing blocks.  Phase 1 (`grow'`): `Y n p (1111 R)` reaches `Y (n+1) (p+1) R`, so a run of 4j ones after the
blocks is eaten in j cycles (`grows`).  Phase 2 (`eat'`): `Y n p ((1110)^(k+2) 1 R)` reaches
`Y (n+2) (p+1) ((1110)^(k+1) 1 R)`, eating one copy of 1110 per cycle (`eats`).
-/

namespace H279

open TM

/-- `0^inf D> 0111011 (011)^n (1011)^p R`. -/
def Y (n p : Nat) (R : Tape) : Config :=
  ⟨blank, cons false (cons true (cons true (cons true (cons false (cons true (cons true
    (rep n [false, true, true] (rep p [true, false, true, true] R)))))))), .D⟩

theorem rot (p : Nat) (S : Tape) :
    cons true (cons false (rep p [true, true, true, false] S)) =
      rep p [true, false, true, true] (cons true (cons false S)) :=
  rep_rotate p [true, false] [true, true, true, false] [true, false, true, true] rfl S

theorem grow' (n p : Nat) (R : Tape) :
    steps (10 * n + 10 * p + 35) (Y n p (cons true (cons true (cons true (cons true R))))) =
      some (Y (n + 1) (p + 1) R) := by
  have h := grow n p R
  rw [rot] at h
  unfold Y
  rw [rep_add p 1]
  exact h

/-- `j` copies of 1111. -/
def ones4 (j : Nat) (R : Tape) : Tape := rep j [true, true, true, true] R

def grows_steps (n p : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => (10 * n + 10 * p + 35) + grows_steps (n + 1) (p + 1) j

theorem grows (j n p : Nat) (R : Tape) :
    steps (grows_steps n p j) (Y n p (ones4 j R)) = some (Y (n + j) (p + j) R) := by
  induction j generalizing n p with
  | zero => rfl
  | succ j ih =>
    have h1 := grow' n p (ones4 j R)
    have h2 := ih (n + 1) (p + 1)
    rw [show n + (j + 1) = n + 1 + j by omega, show p + (j + 1) = p + 1 + j by omega]
    exact steps_seq trans h1 h2

/-- `(1110)^k 1 R`. -/
def dk (k : Nat) (R : Tape) : Tape := rep k [true, true, true, false] (cons true R)

theorem eat' (n p k : Nat) (R : Tape) :
    steps (20 * n + 20 * p + 86) (Y n p (dk (k + 2) R)) = some (Y (n + 2) (p + 1) (dk (k + 1) R)) := by
  have h := eat k n p R
  unfold Y dk
  simp only [rep_succ, app_cons, app_nil] at h ⊢
  exact h

def eats_steps (n p : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => (20 * n + 20 * p + 86) + eats_steps (n + 2) (p + 1) j

theorem eats (j n p k : Nat) (R : Tape) :
    steps (eats_steps n p j) (Y n p (dk (k + 1 + j) R)) = some (Y (n + 2 * j) (p + j) (dk (k + 1) R)) := by
  induction j generalizing n p with
  | zero => rfl
  | succ j ih =>
    have h1 := eat' n p (k + j) R
    have h2 := ih (n + 2) (p + 1)
    rw [show k + 1 + (j + 1) = k + j + 2 by omega, show n + 2 * (j + 1) = n + 2 + 2 * j by omega,
      show p + (j + 1) = p + 1 + j by omega]
    rw [show k + j + 1 = k + 1 + j by omega] at h1
    exact steps_seq trans h1 h2

end H279
