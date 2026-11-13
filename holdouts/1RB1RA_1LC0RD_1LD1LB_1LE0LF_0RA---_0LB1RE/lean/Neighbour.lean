import Machine

/-!
# 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE: how the machine proved in busycoq sits in this table

Written by hand (round 6).  busycoq proves (`CTLv2.v`, `nonhalt17`) that 1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1LB
never halts from blank tape.  That machine is this table mirrored (left and right exchanged) and started in state D
(its states A, B, C, D, E, F are D, E, A, B, C, F here).  `neighbour_start` says what that start amounts to in this
machine's own terms: from blank tape in state D, three steps lead to state A on blank tape with a single 1 on the
cell to its left.  So the proved machine is this machine started on the tape `1 A>0` instead of `A>0`; nothing here
says the two runs ever meet.
-/

namespace H56722

open TM

/-- Blank tape in state D reaches, in three steps, state A with one 1 on its left and blank tape elsewhere. -/
theorem neighbour_start :
    steps 3 (TM.blankCfg .D) = some ⟨cons true (cons false blank), blank, .A⟩ :=
  rfl

/-- The same configuration without the redundant blank cell. -/
theorem neighbour_start' :
    steps 3 (TM.blankCfg .D) = some ⟨cons true blank, blank, .A⟩ := by
  rw [neighbour_start, cons_false_blank]

end H56722
