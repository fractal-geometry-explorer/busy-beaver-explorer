import Machine
import Family

/-!
# 1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF is `T` started in state B

`Family.lean` (the same file in the three folders of the family) proves that this machine is
`1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF` (`T`) with its states renamed (A→D, B→A, C→B, D→C, E→E, F→F), so that
its run from blank tape is the run of `T` from blank tape in state B.  This file ties this folder's generated
`Machine.lean` to the table `tM3` there.
-/

namespace H72232

open TM

def toF : St → G12Blocks3.St6
  | .A => .A | .B => .B | .C => .C | .D => .D | .E => .E | .F => .F

theorem renames : G12Blocks3.Renames trans G12Blocks3.tM3 toF := by
  intro q y; cases q <;> cases y <;> rfl

/-- This machine halts from blank tape iff `T` halts from blank tape started in state B. -/
theorem halts_iff_T_from_B : HaltsFromBlank ↔ TM.Halts G12Blocks3.tT (blankCfg .B) :=
  (G12Blocks3.ren_halts trans G12Blocks3.tM3 toF renames init).symm.trans G12Blocks3.m3_iff

end H72232
