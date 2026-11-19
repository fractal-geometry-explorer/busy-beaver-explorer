import TM

/-!
# The core of the vampire family, with F0 as a parameter

    A 1RB0LA   B 0RC0RB   C 1LD1LA   D 1LC1RE   E 1RF0RD   F f0 ---

The seven holdouts of the family are this table with f0 = 1LC, 1LA or 1RB, started in A, E or F, after renaming the
states (and, for one of them, mirroring the tape): `Machines/`.  `trans f0` is the table; F reading 1 halts.
-/

namespace Core

open TM

/-- The states. -/
inductive St where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

/-- The core's transition table, with `f0` (write, move, next state) for state F reading 0. -/
def trans (f0 : Bool × Dir × St) : St → Bool → Option (Bool × Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true => some (false, .L, .A)
  | .B, false => some (false, .R, .C)
  | .B, true => some (false, .R, .B)
  | .C, false => some (true, .L, .D)
  | .C, true => some (true, .L, .A)
  | .D, false => some (true, .L, .C)
  | .D, true => some (true, .R, .E)
  | .E, false => some (true, .R, .F)
  | .E, true => some (false, .R, .D)
  | .F, false => some f0
  | .F, true => none

abbrev Config := TM.Cfg St

section
variable (f0 : Bool × Dir × St)
abbrev steps := TM.steps (trans f0)
end

end Core
