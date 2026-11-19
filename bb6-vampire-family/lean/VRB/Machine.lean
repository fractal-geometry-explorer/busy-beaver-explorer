import Core.Ctx

/-!
# The core with F0 = 1RB

`1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1RB---`, i.e. `Core.trans` with F0 = 1RB.  Not itself a holdout: the holdouts are this table started in a given
state, renamed (`Machines/`).
-/

namespace VRB

open TM

/-- F0 of this variant. -/
abbrev f0 : Bool × Dir × Core.St := (true, .R, .B)
abbrev trans := Core.trans f0
abbrev step := TM.step trans
abbrev steps := TM.steps trans
/-- The table as text. -/
def text : String := "1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1RB---"

end VRB
