import Machine
import Rules

/-!
# 1RB1RF_1LC1RD_1LA1LC_1RA0RE_1RD1LA_---0LE: the sweep phase, iterated

`X n R` is the configuration `0^inf A> 0 1^n 000 1111 R`: the head in state A on the blank cell just left of the
tape, a block of n ones, three 0s, the marker 1111, and the rest of the tape R.  One sweep (`xstep` of
`Rules.lean`, proved by symbolic simulation) takes `X (2k+2) (0000 R)` to `X (2k+8) R` in 6k+50 steps; `sweeps`
iterates it: `X (2k+2) (0^(4j) R)` reaches `X (2k+2+6j) R`, in `sweeps_steps k j` steps.
-/

namespace H38519

open TM

/-- `0^inf A> 0 1^n 000 1111 R`. -/
def X (n : Nat) (R : Tape) : Config :=
  ⟨blank, cons false (rep n [true] (cons false (cons false (cons false (cons true (cons true (cons true
    (cons true R)))))))), .A⟩

/-- `j` zero cells in front of `R`. -/
def zeros (j : Nat) (R : Tape) : Tape := rep j [false] R

theorem rep_tt (n : Nat) (s : Tape) : rep n [true, true] s = rep (2 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    show cons true (cons true (rep n [true, true] s)) = cons true (rep (2 * n + 1) [true] s)
    rw [ih]; rfl

theorem rep_t_cons (n : Nat) (s : Tape) : rep n [true] (cons true s) = rep (n + 1) [true] s :=
  rep_app_comm n [true] s

/-- One sweep in the `X` notation. -/
theorem sweep (k : Nat) (R : Tape) :
    steps (6 * k + 50) (X (2 * k + 2) (cons false (cons false (cons false (cons false R))))) =
      some (X (2 * k + 8) R) := by
  have h := xstep k R
  rw [rep_tt, rep_tt, rep_t_cons, rep_t_cons, rep_t_cons] at h
  have e1 : (2 * (k + 1)) = 2 * k + 2 := by omega
  rw [e1] at h
  unfold X
  rw [show 2 * k + 8 = 2 * k + 3 + 1 + 1 + 1 + 1 + 1 by omega]
  exact h

/-- The steps of j sweeps from `X (2k+2)`: the sum of 6(k+3i)+50 for i < j. -/
def sweeps_steps (k : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => (6 * k + 50) + sweeps_steps (k + 3) j

theorem zeros_succ4 (j : Nat) (R : Tape) :
    zeros (4 * (j + 1)) R = cons false (cons false (cons false (cons false (zeros (4 * j) R)))) := by
  unfold zeros
  rw [show 4 * (j + 1) = 4 * j + 1 + 1 + 1 + 1 by omega]
  rfl

/-- j sweeps: the block of ones grows by 6j while the marker crosses 4j zeros. -/
theorem sweeps (j k : Nat) (R : Tape) :
    steps (sweeps_steps k j) (X (2 * k + 2) (zeros (4 * j) R)) = some (X (2 * k + 2 + 6 * j) R) := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih =>
    rw [zeros_succ4]
    have h1 := sweep k (zeros (4 * j) R)
    have h2 := ih (k + 3)
    rw [show 2 * (k + 3) + 2 = 2 * k + 8 by omega] at h2
    rw [show 2 * k + 2 + 6 * (j + 1) = 2 * k + 8 + 6 * j by omega]
    exact steps_seq trans h1 h2

/-- The closed form of the step count: j(3n+44) + 9j(j-1) with n = 2k+2. -/
theorem sweeps_steps_eq (k j : Nat) : sweeps_steps k j = j * (6 * k + 50) + 9 * (j * (j - 1)) := by
  induction j generalizing k with
  | zero => simp [sweeps_steps]
  | succ j ih =>
    rw [sweeps_steps, ih]
    cases j with
    | zero => simp
    | succ j =>
      simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega

end H38519
