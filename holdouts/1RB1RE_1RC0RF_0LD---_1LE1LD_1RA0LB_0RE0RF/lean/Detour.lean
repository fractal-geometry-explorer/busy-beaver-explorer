import Machine

/-!
# 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF: the detour that separates it from PR 93's machine

Mirrored and with its states renamed, this machine is the table of DeepMind's busycoq PR 93 (module M598, which halts)
with that table's halt removed, started in the same state, except for one step.  In this machine's own orientation
that step is B reading 0: PR 93's machine writes 1 and moves left into D (one step).  Here B writes 1 and moves right
into C, and then

* if the next cell holds 0, C writes 0 and moves back left, and D, reading the 1 just written, writes 1 and moves
  left: after three steps the machine is exactly where PR 93's machine is after its one step (`detour`);
* if the next cell holds 1, C reads it and the machine halts (`detour_halt`).

So this machine halts from blank tape exactly when the run of PR 93's machine (with its own halt replaced by a
step that keeps going) has B reading 0 with a 1 to its right, written in this orientation.  `PR93Rules.lean` proves
that none of the engine's 44 macro rules ever does that, whatever the tape around.
-/

namespace H50436

open TM

/-- B reading 0 with 0 to its right: three steps that end where PR 93's single step (B0 = 1LD there) ends. -/
theorem detour (x : Bool) (L R : Tape) :
    steps 3 ⟨cons x L, cons false (cons false R), .B⟩ = some ⟨L, cons x (cons true (cons false R)), .D⟩ := by
  cases x <;> rfl

/-- B reading 0 with 1 to its right: after one step C reads 1, which halts. -/
theorem detour_halt (L R : Tape) :
    steps 1 ⟨L, cons false (cons true R), .B⟩ = some ⟨cons true L, cons true R, .C⟩ ∧
      step ⟨cons true L, cons true R, .C⟩ = none := ⟨rfl, rfl⟩

end H50436
