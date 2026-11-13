import Machine
import Family

/-!
# 1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF is the machine `T` of the family file

`Family.lean` (the same file in the three folders of the family) proves the relations between `T`, its shadow
`1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF` (`M1`) and `1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF` (`M3`, which
is `T` started in state B).  This file ties this folder's generated `Machine.lean` to the table `tT` there.
-/

namespace H51101

open TM

/-- The states of `Machine.lean` as the states of the family file (same names). -/
def toF : St → G12Blocks3.St6
  | .A => .A | .B => .B | .C => .C | .D => .D | .E => .E | .F => .F

theorem renames : G12Blocks3.Renames trans G12Blocks3.tT toF := by
  intro q y; cases q <;> cases y <;> rfl

/-- This machine halts from blank tape iff the family's `T` does. -/
theorem halts_iff_T : HaltsFromBlank ↔ TM.Halts G12Blocks3.tT (blankCfg .A) :=
  (G12Blocks3.ren_halts trans G12Blocks3.tT toF renames init).symm

/-- If this machine halts, so does the seven-state shared part `S`: the shadow `M1` makes the same run up to that
point (`G12Blocks3.shadow`). -/
theorem halts_imp_star : HaltsFromBlank → TM.Halts G12Blocks3.tS (blankCfg .A) := fun h =>
  G12Blocks3.star_halts_iff.mpr (Or.inr (halts_iff_T.mp h))

/-- `S` runs 10,000 steps from blank tape (kernel), so `M1` and this machine agree on them. -/
theorem star_runs_kernel : ∃ c, TM.steps G12Blocks3.tS 10000 (blankCfg .A) = some c :=
  blank_runs G12Blocks3.tS (by decide +kernel)

/-- `S` runs 10^7 steps from blank tape (`native_decide`). -/
theorem star_runs_native : ∃ c, TM.steps G12Blocks3.tS 10000000 (blankCfg .A) = some c :=
  blank_runs G12Blocks3.tS (by native_decide)

/-- So for the first 10^7 steps the shadow `M1` and this machine have the same tape and head at every step. -/
theorem same_first_steps (n : Nat) (hn : n ≤ 10000000) :
    ∃ c, TM.steps G12Blocks3.tM1 n (blankCfg .A) = some (G12Blocks3.cmap G12Blocks3.phi1 c) ∧
      TM.steps G12Blocks3.tT n (blankCfg .A) = some (G12Blocks3.cmap G12Blocks3.phi2 c) := by
  obtain ⟨c, hc⟩ := star_runs_native
  obtain ⟨c', hc'⟩ := steps_le G12Blocks3.tS (a := n) (b := 10000000 - n) (by
    rw [show n + (10000000 - n) = 10000000 by omega]; exact hc)
  exact ⟨c', G12Blocks3.shadow hc'⟩

end H51101
