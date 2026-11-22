import TM

/-!
# The watched twin

The table of 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF (bbchallenge id 75625, `H121862.Twin.trans` in `Twin.lean`)
with one more state, G, that watches the cell after `B> 0`:

* B on 0 writes 0 and moves right, as in the twin, but into G instead of C;
* G on 0 does what C does on 0 (`1LD`); G on 1 halts (the twin's C would do `1LE`).

So the watched twin runs the twin's run cell for cell (reading G as C), and halts exactly when the twin stands in B
with a 1 in one of the two cells ahead: B on 1 (where the twin halts too) or `B> 0 1` (where the twin goes on, and
1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF halts one step later).  Those are the breaks of `Twin.lean`.

The files next to this one (`py/port_watch.py`) are the twin's own `Pascal.lean` ... `Race.lean`, unchanged except
for the namespace `H75625W`.  They check for this table because none of their lemmas passes B except on `B> 0 0`,
where G does what C does.
-/

namespace H75625W

open TM

inductive St where
  | A | B | C | D | E | F | G
  deriving DecidableEq, Repr

def trans : St → Bool → Option (Bool × Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true => some (false, .R, .E)
  | .B, false => some (false, .R, .G)
  | .B, true => none
  | .C, false => some (true, .L, .D)
  | .C, true => some (true, .L, .E)
  | .D, false => some (true, .L, .E)
  | .D, true => some (true, .L, .D)
  | .E, false => some (true, .R, .F)
  | .E, true => some (false, .L, .C)
  | .F, false => some (true, .R, .A)
  | .F, true => some (true, .R, .F)
  | .G, false => some (true, .L, .D)
  | .G, true => none

abbrev Config := TM.Cfg St
abbrev step := TM.step trans
abbrev steps := TM.steps trans
abbrev init : Config := TM.blankCfg .A
abbrev HaltsFromBlank : Prop := TM.Halts trans init

end H75625W
