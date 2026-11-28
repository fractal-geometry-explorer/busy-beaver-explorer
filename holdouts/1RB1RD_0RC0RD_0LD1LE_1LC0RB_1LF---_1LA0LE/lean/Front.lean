import Rules

/-! # The front of 1RB1RD_0RC0RD_0LD1LE_1LC0RB_1LF---_1LA0LE runs through a block of `10` pairs

Written by hand.  A configuration of the front is `L 1 0 (00)^m D> (10)^b R`: a block of 2m zeros behind the head,
`b` pairs `10` ahead.  One `cycle` (in `Rules.lean`) eats two pairs ahead, adds one pair behind and two zeros to the
block.  `cycles` iterates it k times by induction: the front halves a block of 2k pairs into k pairs and 2k zeros. -/

namespace H161169

open TM

/-- The front: `L 1 0 (00)^m D> (10)^b R`. -/
def front (L R : Tape) (m b : Nat) : Config :=
  ⟨rep m [false, false] (cons false (cons true L)), rep b [true, false] R, .D⟩

/-- A 0 in front of `(00)^m 0` re-brackets as `(00)^(m+1)`. -/
theorem zeros_succ (m : Nat) (X : Tape) :
    cons false (rep m [false, false] (cons false X)) = rep (m + 1) [false, false] X := by
  have h := rep_rotate m [false] [false, false] [false, false] rfl (cons false X)
  show app [false] (rep m [false, false] (cons false X)) = _
  rw [h]
  exact rep_app_comm m [false, false] X

/-- One cycle, in terms of `front`. -/
theorem front_cycle (L R : Tape) (m b : Nat) :
    steps (28 * m + 30) (front L R m (b + 2)) = some (front (cons false (cons true L)) R (m + 1) b) := by
  have h := cycle b m L R
  unfold front
  rw [h, zeros_succ]

/-- k cycles: `L 1 0 (00)^m D> (10)^(b+2k) R` reaches `L (10)^k 1 0 (00)^(m+k) D> (10)^b R`. -/
theorem front_cycles (k : Nat) : ∀ (L R : Tape) (m b : Nat),
    steps (28 * m * k + 14 * k * k + 16 * k) (front L R m (b + 2 * k)) =
      some (front (rep k [false, true] L) R (m + k) b) := by
  induction k with
  | zero => intro L R m b; rfl
  | succ k ih =>
    intro L R m b
    have e : b + 2 * (k + 1) = (b + 2 * k) + 2 := by omega
    rw [e]
    have h1 := front_cycle L R m (b + 2 * k)
    have h2 := ih (cons false (cons true L)) R (m + 1) b
    have h3 := steps_seq trans h1 h2
    have e2 : rep k [false, true] (cons false (cons true L)) = rep (k + 1) [false, true] L :=
      rep_app_comm k [false, true] L
    rw [e2] at h3
    have e3 : m + 1 + k = m + (k + 1) := by omega
    rw [e3] at h3
    refine steps_congr trans (a := 28 * m + 30 + (28 * (m + 1) * k + 14 * k * k + 16 * k)) ?_ h3
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc]
    omega

end H161169
