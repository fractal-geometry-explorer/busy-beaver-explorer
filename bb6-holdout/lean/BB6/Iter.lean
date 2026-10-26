import BB6.Rules

/-!
# Repeated bounces

`BOUNCE^k`: `L 0 0 E>0 (10)^(m+2k) 1 1 0 R` → `L (01)^k 0 0 E>0 (10)^m 1 1 0 (10)^k R` in 6km + 6k² + 24k steps.
`WALLBOUNCE^k`: `L 0 0 E>0 (10)^(m+k) 0 R` → `L (01)^k 0 0 E>0 (10)^m 0 R` in 6km + 3k² + 9k steps.
The end of one bounce is the start of the next with the count lowered (`prove_iteration` in proofs.py).
-/

namespace BB6

/-- Steps of k bounces off a marker with m stripe pairs left at the end. -/
def bounceSteps : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, m => 6 * (m + 2 * k) + 30 + bounceSteps k m

theorem bounce_iter (k : Nat) : ∀ (m : Nat) (L R : Tape),
    steps (bounceSteps k m)
        ⟨cons false (cons false L), cons false (rep (m + 2 * k) [true, false] (cons true (cons true (cons false R)))), .E⟩
      = some ⟨cons false (cons false (rep k [true, false] L)),
              cons false (rep m [true, false] (cons true (cons true (cons false (rep k [true, false] R))))), .E⟩ := by
  induction k with
  | zero => intro m L R; rfl
  | succ k ih =>
    intro m L R
    have e₁ : m + 2 * (k + 1) = m + 2 * k + 2 := by omega
    rw [e₁]
    have h₁ := bounce (m + 2 * k) L R
    have h₂ := ih m (cons true (cons false L)) (cons true (cons false R))
    rw [rep_cons2, rep_cons2] at h₂
    exact steps_seq h₁ h₂

theorem bounceSteps_eq (k m : Nat) : bounceSteps k m = 6 * k * m + 6 * k * k + 24 * k := by
  induction k with
  | zero => simp [bounceSteps]
  | succ k ih =>
    rw [bounceSteps, ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_succ, Nat.succ_mul]
    omega

/-- Steps of k bounces off a wall with m stripe pairs left at the end. -/
def wallbounceSteps : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, m => 6 * (m + k) + 12 + wallbounceSteps k m

theorem wallbounce_iter (k : Nat) : ∀ (m : Nat) (L R : Tape),
    steps (wallbounceSteps k m)
        ⟨cons false (cons false L), cons false (rep (m + k) [true, false] (cons false R)), .E⟩
      = some ⟨cons false (cons false (rep k [true, false] L)), cons false (rep m [true, false] (cons false R)), .E⟩ := by
  induction k with
  | zero => intro m L R; rfl
  | succ k ih =>
    intro m L R
    have e₁ : m + (k + 1) = m + k + 1 := by omega
    rw [e₁]
    have h₁ := wallbounce (m + k) L R
    have h₂ := ih m (cons true (cons false L)) R
    rw [rep_cons2] at h₂
    exact steps_seq h₁ h₂

theorem wallbounceSteps_eq (k m : Nat) : wallbounceSteps k m = 6 * k * m + 3 * k * k + 9 * k := by
  induction k with
  | zero => simp [wallbounceSteps]
  | succ k ih =>
    rw [wallbounceSteps, ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_succ, Nat.succ_mul]
    omega

end BB6
