import Rules

/-! # The dealing sweep of 1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF

Written by hand.  During a sweep right the tape near the head is `L 1^(k+1) 000 F> 1^n 0 1^m R`: a finished block of
k + 1 ones, the block being dealt (n ones) and the block after it (m ones).  One `deal` (in `Rules.lean`) moves three
ones out of the dealt block, one to the left and two to the right.  `deals` iterates it j times by induction: a
block of n + 3j ones gives j ones to the left and 2j to the right, the 1 : 2 split seen in the run. -/

namespace H68273

open TM

/-- `L 1^(k+1) 000 F> 1^n 0 1^m R`. -/
def dealCfg (L R : Tape) (k n m : Nat) : Config :=
  ⟨cons false (cons false (cons false (rep (k + 1) [true] L))), rep n [true] (cons false (rep m [true] R)), .F⟩

theorem deal_step (L R : Tape) (k n m : Nat) :
    steps (4 * n + 23) (dealCfg L R k (n + 4) m) = some (dealCfg L R (k + 1) (n + 1) (m + 2)) := by
  have h := deal n (rep k [true] L) (rep m [true] R)
  unfold dealCfg
  have e1 : rep n [true] (cons true (cons false (cons true (cons true (rep m [true] R)))))
      = rep (n + 1) [true] (cons false (rep (m + 2) [true] R)) := by
    have := rep_app_comm n [true] (cons false (cons true (cons true (rep m [true] R))))
    exact this
  rw [e1] at h
  exact h

/-- j deals: `L 1^(k+1) 000 F> 1^(n+1+3j) 0 1^m R` reaches `L 1^(k+j+1) 000 F> 1^(n+1) 0 1^(m+2j) R`. -/
theorem deals (n j : Nat) : ∀ (L R : Tape) (k m : Nat),
    steps (4 * n * j + 6 * j * j + 17 * j) (dealCfg L R k (n + 1 + 3 * j) m) =
      some (dealCfg L R (k + j) (n + 1) (m + 2 * j)) := by
  induction j with
  | zero => intro L R k m; rfl
  | succ j ih =>
    intro L R k m
    have e : n + 1 + 3 * (j + 1) = (n + 3 * j) + 4 := by omega
    rw [e]
    have h1 := deal_step L R k (n + 3 * j) m
    have e1 : n + 3 * j + 1 = n + 1 + 3 * j := by omega
    rw [e1] at h1
    have h2 := ih L R (k + 1) (m + 2)
    have h3 := steps_seq trans h1 h2
    have e2 : k + 1 + j = k + (j + 1) := by omega
    have e3 : m + 2 + 2 * j = m + 2 * (j + 1) := by omega
    rw [e2, e3] at h3
    refine steps_congr trans (a := 4 * (n + 3 * j) + 23 + (4 * n * j + 6 * j * j + 17 * j)) ?_ h3
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc]
    omega

end H68273
