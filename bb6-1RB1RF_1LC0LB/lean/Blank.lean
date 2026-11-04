import Machine

/-!
# The halting shape, and the run from blank tape, bounded

The only halting transition is F1.  F is entered from A reading 1 (`1RF`) and from D reading 1 (`0RF`), and the
cell F then reads is the one to the right of A or D.  D is entered only from C reading 1 (`0LD`, a left move), which
writes a 0 where D then has its right neighbour, so D never has a 1 to its right (`d_right_zero`) and the D route
never halts.  A is entered only from E reading 0 (`0RA`).  So in the run from blank tape every halt happens three
steps after the head, in state E, reads `0 1 1` (`halt_from_e011`): E steps onto the 0, A onto the first 1, F onto
the second.

The bounded runs are plain step-by-step runs, evaluated on the list simulator of `tools/lean/TM/Fin.lean` (proved to
agree with `steps`).  They are a floor and a test of the setup, not the way to the question.
-/

namespace BB6e

open TM

/-- The halting configurations: the machine stops exactly in state F on a 1. -/
theorem step_none_iff (c : Config) : step c = none ↔ c.st = .F ∧ c.r 0 = true := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h : r 0 <;> simp [step, TM.step, trans, h]

/-- `E>0 1 1` halts after two more ordinary steps, whatever the rest of the tape. -/
theorem halt_shape (L R : Tape) : ∃ c, steps 2 ⟨L, app [false, true, true] R, .E⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- One step after any configuration, D has a 0 on its right: D is entered only by `C1 → 0LD`. -/
theorem d_right_zero {b c : Config} (h : step b = some c) (hD : c.st = .D) : c.r 1 = false := by
  obtain ⟨l, r, s⟩ := b
  cases s <;> cases hr : r 0 <;> simp [step, TM.step, trans, hr] at h <;> subst h <;> simp_all

/-- A is entered only by `E0 → 0RA`. -/
theorem a_entry {a b : Config} (h : step a = some b) (hA : b.st = .A) :
    a.st = .E ∧ a.r 0 = false ∧ b.r = tail a.r := by
  obtain ⟨l, r, s⟩ := a
  cases s <;> cases hr : r 0 <;> simp [step, TM.step, trans, hr] at h <;> subst h <;> simp_all

/-- What a step into F reads: F comes from A or D reading 1, and reads the cell to their right. -/
theorem f_entry {b c : Config} (h : step b = some c) (hF : c.st = .F) :
    (b.st = .A ∨ b.st = .D) ∧ b.r 0 = true ∧ c.r = tail b.r := by
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

/-- Every halt from blank tape comes two ordinary steps after a configuration `E>0 1 1`. -/
theorem halt_from_e011 {n : Nat} {c : Config} (h : steps n init = some c) (hs : step c = none) :
    ∃ m a, n = m + 2 ∧ steps m init = some a ∧ a.st = .E ∧ a.r 0 = false ∧ a.r 1 = true ∧ a.r 2 = true := by
  obtain ⟨hF, h1⟩ := (step_none_iff c).1 hs
  cases n with
  | zero => simp at h; subst h; cases hF
  | succ k =>
    obtain ⟨b, hb, hbc⟩ := steps_succ_last h
    obtain ⟨hAD, hb0, hcr⟩ := f_entry hbc hF
    have hb1 : b.r 1 = true := by rw [hcr] at h1; exact h1
    cases k with
    | zero => simp at hb; subst hb; simp [init, blankCfg, blank] at hb0
    | succ m =>
      obtain ⟨a, ha, hab⟩ := steps_succ_last hb
      rcases hAD with hA | hD
      · obtain ⟨hE, ha0, hbr⟩ := a_entry hab hA
        refine ⟨m, a, rfl, ha, hE, ha0, ?_, ?_⟩
        · have : b.r 0 = a.r 1 := by rw [hbr]; rfl
          rw [← this]; exact hb0
        · have : b.r 1 = a.r 2 := by rw [hbr]; rfl
          rw [← this]; exact hb1
      · have := d_right_zero hab hD
        rw [this] at hb1; cases hb1

/-- The halt needs a 1 two cells right of an E on a 0; in particular the machine halts from blank tape only if
`E>0 1 1` occurs in the run. -/
theorem halts_imp_e011 (hh : HaltsFromBlank) :
    ∃ m a, steps m init = some a ∧ a.st = .E ∧ a.r 0 = false ∧ a.r 1 = true ∧ a.r 2 = true := by
  obtain ⟨n, c, h, hs⟩ := hh
  obtain ⟨m, a, -, ha, hrest⟩ := halt_from_e011 h hs
  exact ⟨m, a, ha, hrest⟩

/-- After 18 steps from blank tape the tape is `1 0 1 0 1 0 1 F>0`, checked by the kernel. -/
theorem blank_at_18 :
    steps 18 init = some (FCfg.toCfg ⟨[true, false, true, false, true, false, true], [], .F⟩) :=
  blank_reaches trans (by decide +kernel)

/-- 20,000 steps from blank tape without a halt, checked by Lean's kernel alone. -/
theorem blank_runs_20000 : ∃ c, steps 20000 init = some c :=
  blank_runs trans (by decide +kernel)

/-- 10,000,000 steps from blank tape without a halt, by compiled evaluation. -/
theorem blank_runs_10M : ∃ c, steps 10000000 init = some c :=
  blank_runs trans (by native_decide)

end BB6e
