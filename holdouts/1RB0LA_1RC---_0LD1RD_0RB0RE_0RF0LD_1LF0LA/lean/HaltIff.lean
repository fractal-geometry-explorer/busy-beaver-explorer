import Machine

/-!
# 1RB0LA_1RC---_0LD1RD_0RB0RE_0RF0LD_1LF0LA: the only way to halt

The machine halts when B reads a 1.  B is entered by A0 = 1RB and by D0 = 0RB, and A is entered only by A1 and F1
(both move left and leave a 0 on the right of the head).  So a halt needs the head, in state D, on a 0 with a 1 to
its right: `D>0 1`, then `0 B>1`.

`halts_iff_crit`: the run from blank tape halts if and only if it reaches a configuration `D>0 1` (`Crit`).
Written by hand; kernel only.
-/

namespace H164904

open TM

/-- The critical configuration: state D on a 0, with a 1 to the right of the head. -/
def Crit (c : Config) : Prop := c.st = .D ∧ c.r 0 = false ∧ c.r 1 = true

/-- What holds as long as no critical configuration has occurred: A on a 0 has a 0 on its right, B reads a 0. -/
def Safe (c : Config) : Prop :=
  (c.st = .A → c.r 0 = false → c.r 1 = false) ∧ (c.st = .B → c.r 0 = false)

theorem safe_init : Safe init := ⟨fun _ _ => rfl, fun h => by cases h⟩

/-- One step keeps `Safe`, unless the configuration is critical. -/
theorem safe_step (c c' : Config) (hs : Safe c) (hc : ¬ Crit c) (h : step c = some c') : Safe c' := by
  obtain ⟨l, r, s⟩ := c
  obtain ⟨hA, hB⟩ := hs
  cases s <;> cases h0 : r 0 <;>
    simp [step, TM.step, trans, h0] at h <;> subst h <;>
    simp_all [Safe, Crit, tail, cons]

/-- A critical configuration halts one step later. -/
theorem crit_halts (c : Config) (h : Crit c) : ∃ c', steps 1 c = some c' ∧ step c' = none := by
  obtain ⟨l, r, s⟩ := c
  obtain ⟨hs, h0, h1⟩ := h
  simp only at hs h0 h1
  subst hs
  refine ⟨⟨cons false l, tail r, .B⟩, ?_, ?_⟩
  · simp [steps, TM.steps, TM.step, trans, h0]
  · simp [step, TM.step, trans, tail, h1]

/-- A run extended by one step. -/
theorem steps_snoc (n : Nat) : ∀ (c c1 : Config), TM.steps trans n c = some c1 →
    TM.steps trans (n + 1) c = TM.step trans c1 := by
  induction n with
  | zero =>
    intro c c1 h
    simp [TM.steps] at h
    subst h
    cases hq : TM.step trans c <;> simp [TM.steps, hq]
  | succ n ih =>
    intro c c1 h
    cases hs : TM.step trans c with
    | none => simp [TM.steps, hs] at h
    | some d =>
      rw [steps_succ_of_step trans n hs] at h
      rw [steps_succ_of_step trans (n + 1) hs]
      exact ih d c1 h

/-- Along the run from blank tape: `Safe` holds, or a critical configuration has occurred. -/
theorem safe_or_crit (n : Nat) : ∀ c, steps n init = some c → Safe c ∨ ∃ m c0, steps m init = some c0 ∧ Crit c0 := by
  induction n with
  | zero => intro c h; simp [steps, TM.steps] at h; subst h; exact Or.inl safe_init
  | succ n ih =>
    intro c h
    obtain ⟨c1, h1⟩ := steps_le trans (a := n) (b := 1) h
    have h' : TM.step trans c1 = some c := by rw [← steps_snoc n init c1 h1]; exact h
    rcases ih c1 h1 with hs | hx
    · by_cases hc : Crit c1
      · exact Or.inr ⟨n, c1, h1, hc⟩
      · exact Or.inl (safe_step c1 c hs hc h')
    · exact Or.inr hx

/-- The machine halts from blank tape if and only if the run reaches `D>0 1`. -/
theorem halts_iff_crit : HaltsFromBlank ↔ ∃ n c, steps n init = some c ∧ Crit c := by
  constructor
  · rintro ⟨n, c, h, hh⟩
    rcases safe_or_crit n c h with hs | hx
    · exfalso
      obtain ⟨l, r, s⟩ := c
      obtain ⟨hA, hB⟩ := hs
      cases s <;> cases h0 : r 0 <;> simp [TM.step, trans, h0] at hh
      simp_all
    · exact hx
  · rintro ⟨n, c, h, hc⟩
    obtain ⟨c', h2, hh⟩ := crit_halts c hc
    exact ⟨n + 1, c', steps_seq trans h h2, hh⟩

end H164904
