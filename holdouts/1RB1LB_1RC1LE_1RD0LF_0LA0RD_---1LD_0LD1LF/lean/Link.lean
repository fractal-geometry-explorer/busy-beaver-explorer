import Machine
import Family

/-!
# 1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF is the shadow `M1` of the family file

`Family.lean` (the same file in the three folders of the family) proves that this machine and
`1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF` (`T`) make the same run as long as the seven-state machine `S` runs.
This file ties this folder's generated `Machine.lean` to the table `tM1` there.
-/

namespace H111363

open TM

def toF : St → G12Blocks3.St6
  | .A => .A | .B => .B | .C => .C | .D => .D | .E => .E | .F => .F

theorem renames : G12Blocks3.Renames trans G12Blocks3.tM1 toF := by
  intro q y; cases q <;> cases y <;> rfl

theorem halts_iff_M1 : HaltsFromBlank ↔ TM.Halts G12Blocks3.tM1 (blankCfg .A) :=
  (G12Blocks3.ren_halts trans G12Blocks3.tM1 toF renames init).symm

/-- If this machine halts, so does `S`. -/
theorem halts_imp_star : HaltsFromBlank → TM.Halts G12Blocks3.tS (blankCfg .A) := fun h =>
  G12Blocks3.star_halts_iff.mpr (Or.inl (halts_iff_M1.mp h))

/-- If neither this machine nor `T` halts, they make the same run (same tape and head at every step). -/
theorem same_run_as_T (h1 : ¬ HaltsFromBlank) (h2 : ¬ TM.Halts G12Blocks3.tT (blankCfg .A)) (n : Nat) :
    ∃ c, TM.steps G12Blocks3.tM1 n (blankCfg .A) = some (G12Blocks3.cmap G12Blocks3.phi1 c) ∧
      TM.steps G12Blocks3.tT n (blankCfg .A) = some (G12Blocks3.cmap G12Blocks3.phi2 c) :=
  G12Blocks3.same_run (fun hs => (G12Blocks3.star_halts_iff.mp hs).elim (fun h => h1 (halts_iff_M1.mpr h)) h2) n

end H111363
