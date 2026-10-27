import BB6.Marks

/-!
# A block at the end: the machine halts

A round start whose only mark is a block three cells before the width, `roundStart [⟨.B, W − 3⟩] W` (W odd, the
stripe between the gap and the block being even), is a halt: the head passes the stripe to the block in W − 7 steps,
meets it at distance 0, and the machine halts 71 steps later, one cell left of where the stripe ended
(`block_end_halt`).  The round model leaves this round uncovered (an end meeting at distance 0, `swap0`); it is how
the pass starts with R = 6 of `thm/PassHaltR6.lean` halt.
-/

namespace BB6

/-- A run, then a halting run from where it ends. -/
theorem steps_seq_none {a b : Nat} {c c' : Cfg} (h₁ : steps a c = some c') (h₂ : steps b c' = none) :
    steps (a + b) c = none := by
  induction a generalizing c with
  | zero =>
    simp only [steps, Option.some.injEq] at h₁
    subst h₁
    simpa using h₂
  | succ a ih =>
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e]
    cases hs : step c with
    | none => simp [steps, hs]
    | some d =>
      rw [steps_succ_of_step a hs] at h₁
      rw [steps_succ_of_step (a + b) hs]
      exact ih h₁

/-- The 71 steps after the pass and the halt: the stripe's last cell (1) on the left, the stripe's closing 0 under the
head, the block and blank tape on the right. -/
theorem block_end_local (L : Tape) :
    steps 72 ⟨cons true L, cons false (cons true (cons true (cons true blank))), .E⟩ = none := rfl

/-- **A block three cells before the width halts the machine**, W + 65 steps after the round start (W = 2k + 9). -/
theorem block_end_halt (k : Nat) :
    steps (2 * k + 74) (roundStart [⟨.B, 2 * k + 6⟩] (2 * k + 9)) = none := by
  have hstart : roundStart [⟨.B, 2 * k + 6⟩] (2 * k + 9)
      = ⟨cons false (cons false (cons true blank)),
         rep (k + 1) [false, true] (cons false (cons true (cons true (cons true blank)))), .E⟩ := by
    have e₁ : 2 * k + 6 - 4 = 2 * (k + 1) := by omega
    have e₂ : 2 * k + 9 - (2 * k + 6 + 3) = 0 := by omega
    simp only [roundStart, build, mcells, mval, mlen, Bool.not_false, Bool.not_true, e₁, e₂, stripe_zero,
      stripe_even, app_cons, app_nil]
    rw [rep_shift']
  have hpass := pass (k + 1) (cons false (cons false (cons true blank)))
    (cons false (cons true (cons true (cons true blank))))
  have e : 2 * k + 74 = 2 * (k + 1) + 72 := by omega
  rw [hstart, e]
  exact steps_seq_none hpass (block_end_local _)

/-- The same for any odd width W ≥ 9: the machine halts within W + 65 steps. -/
theorem block_end_halt' (W : Nat) (hW : W % 2 = 1) (h9 : 9 ≤ W) :
    steps (W + 65) (roundStart [⟨.B, W - 3⟩] W) = none := by
  obtain ⟨k, rfl⟩ : ∃ k, W = 2 * k + 9 := ⟨(W - 9) / 2, by omega⟩
  have e₁ : 2 * k + 9 - 3 = 2 * k + 6 := by omega
  have e₂ : 2 * k + 9 + 65 = 2 * k + 74 := by omega
  rw [e₁, e₂]
  exact block_end_halt k

end BB6
