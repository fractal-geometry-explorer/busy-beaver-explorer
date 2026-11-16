import TM

/-!
# The mirror machine of 1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA

1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA is the mirror image (left and right exchanged) of the table
1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD with its states renamed (A, B, C, D, E, F of this table are C, D, E, A, B, F
there).  So its run from blank tape is the mirror image of the run of this table from blank tape *in state D*
(`Mirror.lean`).  This file is that table, started in D; it is a copy of
`holdouts/1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/lean/Machine.lean` with `init` changed.  Halting transitions: B1.
-/

namespace H163738M

open TM

/-- The states. -/
inductive St where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

/-- The transition table of 1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD: (write, move, next state); `none` halts. -/
def trans : St → Bool → Option (Bool × Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true => some (false, .L, .E)
  | .B, false => some (true, .R, .C)
  | .B, true => none
  | .C, false => some (false, .R, .D)
  | .C, true => some (false, .R, .E)
  | .D, false => some (true, .L, .E)
  | .D, true => some (false, .R, .B)
  | .E, false => some (false, .L, .A)
  | .E, true => some (false, .L, .F)
  | .F, false => some (false, .R, .C)
  | .F, true => some (false, .L, .D)

/-- The machine's text form, as the table above was generated from. -/
def text : String := "1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD"

abbrev Config := TM.Cfg St
abbrev step := TM.step trans
abbrev steps := TM.steps trans
abbrev fstep := TM.fstep trans
abbrev fsteps := TM.fsteps trans
/-- The configuration of the run from blank tape, in state D. -/
abbrev init : Config := TM.blankCfg .D
/-- The machine halts from blank tape. -/
abbrev HaltsFromBlank : Prop := TM.Halts trans init

end H163738M
