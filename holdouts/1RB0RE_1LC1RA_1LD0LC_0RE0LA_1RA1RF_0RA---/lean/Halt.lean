import Machine

/-!
# 1RB0RE_1LC1RA_1LD0LC_0RE0LA_1RA1RF_0RA---: the two halting patterns, and what the entry D0 does

Written by hand (round 6).  This is the table of 1RB1RF_1RC0RA_1LD1RB_1LE0LD_0RA0LB_0RB--- started in that machine's
state B (its states B, C, D, E, A, F are A, B, C, D, E, F here).  The machines proved in busycoq (pull request 36)
have the same table except for the entry D0 (state D reading 0): `1LA` or `1RA` there, `0RE` here.  `d0_event` is
what this machine does each time that entry is used; `halt_b` and `halt_a` are the two local patterns from which it
halts.  Reading the table backwards these are the only two: F is entered only from E on a 1, and E is entered only
from A on a 1 (`halt_a`) or from D on a 0, D only from C on a 0, and a C that leaves a 1 on its right was entered
from B on a 0 (`halt_b`).
-/

namespace H113824

open TM

/-- The entry D0 at work: C, erasing leftwards, reads a 0 that has another 0 on its left and a 0 on its right.
Four steps later (C0, D0, E1, F0) the three cells read 0 1 0 and A is on the next cell to the right. -/
theorem d0_event (L R : Tape) :
    steps 4 ⟨cons false L, cons false (cons false R), .C⟩ = some ⟨cons false (cons true (cons false L)), R, .A⟩ :=
  rfl

/-- First halting pattern: B reads a 0 with two 0s on its left.  After B0, C0, D0, E1 the head is in F on a 1. -/
theorem halt_b (L R : Tape) :
    ∃ c, steps 4 ⟨cons false (cons false L), cons false R, .B⟩ = some c ∧ step c = none :=
  ⟨⟨cons true (cons false L), cons true R, .F⟩, rfl, rfl⟩

/-- Second halting pattern: A reads 1 1 1.  After A1, E1 the head is in F on a 1. -/
theorem halt_a (L R : Tape) :
    ∃ c, steps 2 ⟨L, cons true (cons true (cons true R)), .A⟩ = some c ∧ step c = none :=
  ⟨⟨cons true (cons false L), cons true R, .F⟩, rfl, rfl⟩

end H113824
