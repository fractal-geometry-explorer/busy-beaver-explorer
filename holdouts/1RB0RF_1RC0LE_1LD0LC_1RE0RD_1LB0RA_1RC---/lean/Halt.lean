import Rules

/-!
# 1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC---: where a halt comes from

Written by hand.  The halting transition is F reading 1, and F is entered only by A reading 1 (A1 -> 0RF), which
moves right.  So one step before any halt the machine is in state A on a 1 with a 1 to its right (`prehalt`); if the
run from blank tape never shows `A>1 1`, the machine never halts (`nonhalting_of_no_A11`); and `A>1 1` does halt
(`halts_of_A11`).
-/

namespace H112382

open TM

/-- The pattern a halt comes from: state A on a 1, with a 1 to its right. -/
def Pre (c : Config) : Prop := c.st = .A ∧ c.r 0 = true ∧ c.r 1 = true

theorem prehalt_aux (s : St) (a x y : Bool) (L R : Tape) (c : Config)
    (h : steps 1 ⟨cons a L, cons x (cons y R), s⟩ = some c) (hh : step c = none) :
    s = .A ∧ x = true ∧ y = true := by
  cases s <;> cases a <;> cases x <;> cases y <;>
    first
    | exact ⟨rfl, rfl, rfl⟩
    | (cases h <;> cases hh)

/-- One step before a halt the machine shows the pattern `Pre`. -/
theorem prehalt (c0 c : Config) (h : steps 1 c0 = some c) (hh : step c = none) : Pre c0 := by
  obtain ⟨l, r, s⟩ := c0
  have hl : l = cons (l 0) (tail l) := by funext n; rcases n with _ | n <;> rfl
  have hr : r = cons (r 0) (cons (r 1) (tail (tail r))) := by funext n; rcases n with _ | _ | n <;> rfl
  have h' : steps 1 ⟨cons (l 0) (tail l), cons (r 0) (cons (r 1) (tail (tail r))), s⟩ = some c := by
    rw [← hl, ← hr]; exact h
  exact prehalt_aux s _ _ _ _ _ c h' hh

theorem steps_split : ∀ (a b : Nat) (c c'' : Config), steps (a + b) c = some c'' →
    ∃ c', steps a c = some c' ∧ steps b c' = some c'' := by
  intro a
  induction a with
  | zero => intro b c c'' h; exact ⟨c, rfl, by simpa using h⟩
  | succ a ih =>
    intro b c c'' h
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e] at h
    cases hs : step c with
    | none => simp [steps, TM.steps, hs] at h
    | some d =>
      have h0 : steps (a + b) d = some c'' := (steps_succ_of_step trans (a + b) hs).symm.trans h
      obtain ⟨c', h1, h2⟩ := ih b d c'' h0
      exact ⟨c', (steps_succ_of_step trans a hs).trans h1, h2⟩

/-- A halting run from blank tape passes through the pattern `Pre` (one step before its end). -/
theorem pre_of_halts (H : HaltsFromBlank) : ∃ n c, steps n init = some c ∧ Pre c := by
  obtain ⟨n, c, h, hh⟩ := H
  by_cases hn : 1 ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨c0, h1, h2⟩ := steps_split k 1 init c h
    exact ⟨k, c0, h1, prehalt c0 c h2 hh⟩
  · have : n = 0 := by omega
    subst this
    cases h; cases hh

/-- If the run from blank tape never has state A on a 1 with a 1 to its right, the machine never halts. -/
theorem nonhalting_of_no_A11 (h : ∀ n c, steps n init = some c → ¬ Pre c) : ¬ HaltsFromBlank := by
  intro H
  obtain ⟨n, c, hc, hp⟩ := pre_of_halts H
  exact h n c hc hp

/-- And the pattern does halt: `A>1 1` halts after one step. -/
theorem halts_of_A11 (L R : Tape) :
    ∃ c, steps 1 ⟨L, cons true (cons true R), .A⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

end H112382
