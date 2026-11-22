import Map

/-!
# The same table from other start states: three more holdouts

1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA, 1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE--- and
1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD--- are this machine's table mirrored (left and right swapped) with the states
renamed, started in this table's state F, C and B. Their tables are copied below exactly as generated in their own
`lean/Machine.lean` (namespaces H17454, H58362, H104936); `TM.halts_of_map` with `TM.mirrorCfg` turns each one's run
from blank tape into this table's run from blank tape in the other state, which reaches a phase start after a few
steps. So `not_halts_from` applies to each: if the orbit of `phi` from that phase start stays covered, the holdout
does not halt.
-/

namespace H17454

/-- The states. -/
inductive St where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

/-- The transition table of 1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA (as in its `lean/Machine.lean`). -/
def trans : St → Bool → Option (Bool × TM.Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true => none
  | .B, false => some (false, .R, .C)
  | .B, true => some (false, .R, .E)
  | .C, false => some (true, .R, .D)
  | .C, true => some (true, .R, .F)
  | .D, false => some (true, .L, .E)
  | .D, true => some (false, .L, .B)
  | .E, false => some (true, .R, .C)
  | .E, true => some (false, .L, .D)
  | .F, false => some (true, .R, .C)
  | .F, true => some (true, .R, .A)

end H17454

namespace H58362

/-- The states. -/
inductive St where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

/-- The transition table of 1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE--- (as in its `lean/Machine.lean`). -/
def trans : St → Bool → Option (Bool × TM.Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true => some (true, .R, .D)
  | .B, false => some (true, .L, .C)
  | .B, true => some (false, .L, .E)
  | .C, false => some (true, .R, .A)
  | .C, true => some (false, .L, .B)
  | .D, false => some (true, .R, .A)
  | .D, true => some (true, .R, .F)
  | .E, false => some (false, .R, .A)
  | .E, true => some (false, .R, .C)
  | .F, false => some (true, .R, .E)
  | .F, true => none

end H58362

namespace H104936

/-- The states. -/
inductive St where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

/-- The transition table of 1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD--- (as in its `lean/Machine.lean`). -/
def trans : St → Bool → Option (Bool × TM.Dir × St)
  | .A, false => some (true, .R, .B)
  | .A, true => some (false, .L, .C)
  | .B, false => some (true, .R, .C)
  | .B, true => some (true, .R, .E)
  | .C, false => some (true, .L, .A)
  | .C, true => some (false, .L, .D)
  | .D, false => some (false, .R, .B)
  | .D, true => some (false, .R, .A)
  | .E, false => some (true, .R, .B)
  | .E, true => some (true, .R, .F)
  | .F, false => some (true, .R, .D)
  | .F, true => none

end H104936

namespace H103424

open TM

/-- This table's states as H17454's (mirrored): A D, B E, C C, D F, E B, F A. -/
def to17454 : St → H17454.St
  | .A => .D | .B => .E | .C => .C | .D => .F | .E => .B | .F => .A

/-- This table's states as H58362's (mirrored): A B, B C, C A, D D, E E, F F. -/
def to58362 : St → H58362.St
  | .A => .B | .B => .C | .C => .A | .D => .D | .E => .E | .F => .F

/-- This table's states as H104936's (mirrored): A C, B A, C B, D E, E D, F F. -/
def to104936 : St → H104936.St
  | .A => .C | .B => .A | .C => .B | .D => .E | .E => .D | .F => .F

theorem iso17454 (q : St) (b : Bool) :
    H17454.trans (to17454 q) b = (trans q b).map (fun t => (t.1, t.2.1.flip, to17454 t.2.2)) := by
  cases q <;> cases b <;> rfl

theorem iso58362 (q : St) (b : Bool) :
    H58362.trans (to58362 q) b = (trans q b).map (fun t => (t.1, t.2.1.flip, to58362 t.2.2)) := by
  cases q <;> cases b <;> rfl

theorem iso104936 (q : St) (b : Bool) :
    H104936.trans (to104936 q) b = (trans q b).map (fun t => (t.1, t.2.1.flip, to104936 t.2.2)) := by
  cases q <;> cases b <;> rfl

/-- 1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA halts from blank tape iff this table does from state F. -/
theorem halts17454_iff : Halts H17454.trans (blankCfg .A) ↔ Halts trans (blankCfg .F) := by
  have h := halts_of_map trans H17454.trans (mirrorCfg to17454) (step_mirrorCfg trans H17454.trans to17454 iso17454)
    (blankCfg .F)
  rw [mirrorCfg_blank] at h
  exact h.symm

theorem halts58362_iff : Halts H58362.trans (blankCfg .A) ↔ Halts trans (blankCfg .C) := by
  have h := halts_of_map trans H58362.trans (mirrorCfg to58362) (step_mirrorCfg trans H58362.trans to58362 iso58362)
    (blankCfg .C)
  rw [mirrorCfg_blank] at h
  exact h.symm

theorem halts104936_iff : Halts H104936.trans (blankCfg .A) ↔ Halts trans (blankCfg .B) := by
  have h := halts_of_map trans H104936.trans (mirrorCfg to104936)
    (step_mirrorCfg trans H104936.trans to104936 iso104936) (blankCfg .B)
  rw [mirrorCfg_blank] at h
  exact h.symm

set_option maxRecDepth 20000 in
/-- This table from blank tape in state F reaches PS(11, [6]) at step 108. -/
theorem blankF : steps 108 (blankCfg .F) = some (PS 11 (enc [6])) := rfl
set_option maxRecDepth 20000 in
/-- In state C: PS(15, []) at step 92. -/
theorem blankC : steps 92 (blankCfg .C) = some (PS 15 (enc [])) := rfl
/-- In state B: PS(5, []) at step 15. -/
theorem blankB : steps 15 (blankCfg .B) = some (PS 5 (enc [])) := rfl

/-- 1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA does not halt if the orbit of `phi` from PS(11, [6]) stays covered. -/
theorem not_halts17454 (h : ∀ n, ∃ s, orbit phi (11, [6]) n = some s) : ¬ Halts H17454.trans (blankCfg .A) := by
  rw [halts17454_iff]
  exact not_halts_from blankF h

/-- 1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE--- does not halt if the orbit of `phi` from PS(15, []) stays covered. -/
theorem not_halts58362 (h : ∀ n, ∃ s, orbit phi (15, []) n = some s) : ¬ Halts H58362.trans (blankCfg .A) := by
  rw [halts58362_iff]
  exact not_halts_from blankC h

/-- 1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD--- does not halt if the orbit of `phi` from PS(5, []) stays covered. -/
theorem not_halts104936 (h : ∀ n, ∃ s, orbit phi (5, []) n = some s) : ¬ Halts H104936.trans (blankCfg .A) := by
  rw [halts104936_iff]
  exact not_halts_from blankB h

end H103424
