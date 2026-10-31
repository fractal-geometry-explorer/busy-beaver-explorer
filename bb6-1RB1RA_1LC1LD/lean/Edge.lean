import Blank
import EdgeCert

/-!
# A halt can only happen at the right edge

**The left end.**  D is entered in two ways: from E reading 1 (`1RD`, so the cell to D's left is the 1 that E kept),
or by a left move from B reading 1 or C reading 0 (`1LD`, so the cell to D's right is the 1 that was just written).
So whenever D has a 0 on its left, in particular at the left end of the tape, it has a 1 on its right
(`d_one_right`, `d_left_end`).  The observation from the long runs is forced by one step and is not a property of the
run.

**The right side.**  A closed tape language (`EdgeCert.lean`, found by `tools/py/bbtools/ctl.py` from windows of
three cells, checked here by `decide` in the kernel) covers every configuration of the run from blank tape
(`reach_inv`).  It shows that past the head cell, two 0s in a row occur only in the blank region beyond everything
written (`right_no_double_zero`).  So the halting shape `D>0 0` arises only with blank tape to the right of D
(`d_zero_zero`), and the machine halts from blank tape exactly when E reaches the blank region to the right
(`halts_iff_edge`).  The left side is not constrained by the language: blocks of 0s there are allowed.
-/

namespace BB6c

open TM

/-! ## The left end -/

/-- D with a 0 on its left has a 1 on its right, one step after any configuration. -/
theorem d_one_right {b c : Config} (h : step b = some c) (hD : c.st = .D) (hl : c.l 0 = false) : c.r 1 = true := by
  obtain ⟨l, r, s⟩ := b
  cases s <;> cases hr : r 0 <;> simp [step, TM.step, trans, hr] at h <;> subst h <;> simp_all

theorem steps_succ_last {n : Nat} {c₀ c : Config} (h : steps (n + 1) c₀ = some c) :
    ∃ b, steps n c₀ = some b ∧ step b = some c := by
  obtain ⟨b, hb⟩ := TM.steps_le trans (a := n) (b := 1) h
  refine ⟨b, hb, ?_⟩
  have h2 : TM.steps trans (n + 1) c₀ = some c := h
  cases hs : step b with
  | none => rw [TM.steps_halt trans hb hs 0] at h2; cases h2
  | some d =>
    have := TM.steps_seq trans hb (show steps 1 b = some d by simp [TM.steps, hs])
    rw [this] at h2
    rw [← Option.some.inj h2]

/-- In the run from blank tape, D at the left end of the tape (nothing but blank to its left) has a 1 to its right. -/
theorem d_left_end {n : Nat} {c : Config} (h : steps n init = some c) (hD : c.st = .D) (hl : c.l = blank) :
    c.r 1 = true := by
  cases n with
  | zero => simp at h; subst h; cases hD
  | succ n =>
    obtain ⟨b, -, hb⟩ := steps_succ_last h
    exact d_one_right hb hD (by rw [hl]; rfl)

/-! ## The closed tape language -/

theorem cert_closed : TM.CTL.closed trans certL certR certS = true := by decide +kernel

theorem cert_starts : TM.CTL.starts certL certR certS St.A = true := by decide +kernel

theorem cert_blankOnly : TM.CTL.blankOnly certR certB = true := by decide +kernel

theorem cert_haltsBlank : TM.CTL.haltsBlank trans certR certS certB = true := by decide +kernel

theorem cert_noDoubleZero : TM.CTL.noDoubleZero certR certS certRt certB = true := by decide +kernel

/-- Every configuration of the run from blank tape is in the language. -/
theorem reach_inv {n : Nat} {c : Config} (h : steps n init = some c) : TM.CTL.Inv certL certR certS c :=
  TM.CTL.reach trans cert_closed cert_starts h

/-- Past the head cell, two 0s in a row are followed only by 0s: inside what has been written, the right side has
no `0 0`. -/
theorem right_no_double_zero {n : Nat} {c : Config} (h : steps n init = some c) {i : Nat}
    (h0 : c.r (i + 1) = false) (h1 : c.r (i + 2) = false) : ∀ j, i + 1 ≤ j → c.r j = false :=
  TM.CTL.no_double_zero cert_blankOnly cert_noDoubleZero (reach_inv h) h0 h1

/-- Every halt from blank tape happens in state E with blank tape from the head onward. -/
theorem halt_at_edge {n : Nat} {c : Config} (h : steps n init = some c) (hs : step c = none) :
    c.st = .E ∧ c.r = blank := by
  have ht := TM.CTL.halt_tail_blank trans cert_blankOnly cert_haltsBlank (reach_inv h) hs
  obtain ⟨hE, h0⟩ := (step_none_iff c).1 hs
  refine ⟨hE, ?_⟩
  rw [← TM.CTL.cons_head_tail c.r, ht, h0]
  exact cons_false_blank

/-- The halting shape `D>0 0` occurs only with blank tape from D onward. -/
theorem d_zero_zero {n : Nat} {c : Config} (h : steps n init = some c) (hD : c.st = .D) (h0 : c.r 0 = false)
    (h1 : c.r 1 = false) : c.r = blank := by
  obtain ⟨l, r, s⟩ := c
  simp only at hD h0 h1
  subst hD
  have hs : step ⟨l, r, .D⟩ = some ⟨cons true l, tail r, .E⟩ := by simp [step, TM.step, trans, h0]
  have h' : steps (n + 1) init = some ⟨cons true l, tail r, .E⟩ :=
    TM.steps_seq trans h (show steps 1 _ = some _ by simp [TM.steps, hs])
  have hr := (halt_at_edge h' (by simp [step, TM.step, trans, tail, h1])).2
  simp only at hr ⊢
  rw [← TM.CTL.cons_head_tail r, hr, h0]
  exact cons_false_blank

/-- The machine halts from blank tape exactly when E reaches the blank region at the right. -/
theorem halts_iff_edge : HaltsFromBlank ↔ ∃ n c, steps n init = some c ∧ c.st = .E ∧ c.r = blank := by
  constructor
  · rintro ⟨n, c, h, hs⟩
    exact ⟨n, c, h, halt_at_edge h hs⟩
  · rintro ⟨n, ⟨l, r, s⟩, h, hE, hr⟩
    simp only at hE hr
    subst hE hr
    exact ⟨n, _, h, rfl⟩

end BB6c
