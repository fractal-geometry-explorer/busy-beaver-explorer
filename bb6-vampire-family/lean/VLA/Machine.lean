import Core.Ctx

/-!
# The core with F0 = 1LA

`1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---`, i.e. `Core.trans` with F0 = 1LA.  Not itself a holdout: the holdouts are this table started in a given
state, renamed (`Machines/`).
-/

namespace VLA

open TM

/-- F0 of this variant. -/
abbrev f0 : Bool × Dir × Core.St := (true, .L, .A)
abbrev trans := Core.trans f0
abbrev step := TM.step trans
abbrev steps := TM.steps trans
/-- The table as text. -/
def text : String := "1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---"

end VLA
