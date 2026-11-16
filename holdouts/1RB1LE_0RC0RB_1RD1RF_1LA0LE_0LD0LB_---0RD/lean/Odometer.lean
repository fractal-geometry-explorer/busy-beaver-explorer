import VisitR

/-! # The odometer at the right end of 1RB1LE_0RC0RB_1RD1RF_1LA0LE_0LD0LB_---0RD

Read the cells right of the odometer's low end in tokens of four cells: `e0 = 0111`, `e1 = 0000`, `e2 = 0110`
(digit values 0, 1, 2, lowest digit nearest the head).  A visit in state B adds one in base 3: trailing 2s become 0s
and the first digit that is not 2 goes up by one; the visit always comes out in state D.  Blank tape is `e1 e1 e1 …`,
an endless row of digits 1, so a carry always stops; there is no overflow.  For every number of digits, from the rows
of `VisitR.lean`. -/

namespace H65208

open TM

def e0 : List Bool := [false, true, true, true]
def e1 : List Bool := [false, false, false, false]
def e2 : List Bool := [false, true, true, false]

/-- A carry through k digits 2, given that the visit of the rest comes out in D. -/
theorem o_carry (k : Nat) {x x' : Tape} (h : Vis .B x .D x') :
    Vis .B (rep k e2 x) .D (rep k e0 x') := by
  induction k with
  | zero => exact h
  | succ k ih => exact v_B_0110_Bd ih

/-- A visit in state B: k digits 2 then a 0 become k digits 0 then a 1. -/
theorem o_inc0 (k : Nat) (y : Tape) : Vis .B (rep k e2 (app e0 y)) .D (rep k e0 (app e1 y)) :=
  o_carry k v_B_0111_none

/-- A visit in state B: k digits 2 then a 1 become k digits 0 then a 2. -/
theorem o_inc1 (k : Nat) (y : Tape) : Vis .B (rep k e2 (app e1 y)) .D (rep k e0 (app e2 y)) :=
  o_carry k v_B_0000_none

/-- k digits 2 then blank tape become k digits 0, a 2, and blank tape. -/
theorem o_inc_blank (k : Nat) : Vis .B (rep k e2 blank) .D (rep k e0 (app e2 blank)) := by
  have h := o_inc1 k blank
  simp only [e1, app, cons_false_blank] at h
  exact h

end H65208
