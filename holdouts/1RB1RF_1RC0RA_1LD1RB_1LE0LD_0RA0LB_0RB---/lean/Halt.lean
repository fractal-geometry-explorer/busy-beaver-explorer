import Machine

/-!
# 1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB---: the two halting patterns, and what the entry E0 does

Written by hand (round 6).  The machines proved in busycoq (pull request 36) have the same table except for the
entry E0 (state E reading 0): `1LA`, `1LB` or `1RB` there, `0RA` here.  `e0_event` is what this machine does each
time that entry is used; `halt_c` and `halt_b` are the two local patterns from which it halts.  Reading the table
backwards these are the only two: F is entered only from A on a 1, and A is entered only from B on a 1 (`halt_b`) or
from E on a 0, E only from D on a 0, and a D that leaves a 1 on its right was entered from C on a 0 (`halt_c`).
-/

namespace H22262

open TM

/-- The entry E0 at work: D, erasing leftwards, reads a 0 that has another 0 on its left and a 0 on its right.
Four steps later (D0, E0, A1, F0) the three cells read 0 1 0 and B is on the next cell to the right. -/
theorem e0_event (L R : Tape) :
    steps 4 ⟨cons false L, cons false (cons false R), .D⟩ = some ⟨cons false (cons true (cons false L)), R, .B⟩ :=
  rfl

/-- First halting pattern: C reads a 0 with two 0s on its left.  After C0, D0, E0, A1 the head is in F on a 1. -/
theorem halt_c (L R : Tape) :
    ∃ c, steps 4 ⟨cons false (cons false L), cons false R, .C⟩ = some c ∧ step c = none :=
  ⟨⟨cons true (cons false L), cons true R, .F⟩, rfl, rfl⟩

/-- Second halting pattern: B reads 1 1 1.  After B1, A1 the head is in F on a 1. -/
theorem halt_b (L R : Tape) :
    ∃ c, steps 2 ⟨L, cons true (cons true (cons true R)), .B⟩ = some c ∧ step c = none :=
  ⟨⟨cons true (cons false L), cons true R, .F⟩, rfl, rfl⟩

end H22262
