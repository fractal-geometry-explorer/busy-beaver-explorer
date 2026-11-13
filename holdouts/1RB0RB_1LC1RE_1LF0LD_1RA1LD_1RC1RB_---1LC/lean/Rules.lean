import Machine

/-! The halting configuration of 1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC: the sample with the hole at position 1 halts, whatever the rest of the tape. Proved by `bbtools.symtm`; tapes in Lean are listed from the head outward. -/

namespace H53489

open TM

/-- From `D> 1 0 R` with blank tape to the left (the sample with the hole at position 1), the machine reaches F on a 0 in 7 steps, whatever R is. -/
theorem to_halt (R : Tape) :
    steps (7) ⟨blank, cons true (cons false (R)), .D⟩ = some ⟨blank, cons false (cons true (cons true (cons true (cons true (R))))), .F⟩ := by
  have hn : 7 = 7 := by omega
  have h0 : steps 7 ⟨blank, cons true (cons false (R)), .D⟩ = some ⟨blank, cons false (cons true (cons true (cons true (cons true (R))))), .F⟩ := rfl
  exact steps_congr trans hn (h0)

/-- So every sample with the hole at position 1 halts (on the next step), whatever the rest of the tape. -/
theorem halts_family (R : Tape) : TM.Halts trans ⟨blank, cons true (cons false R), .D⟩ :=
  ⟨_, _, to_halt R, rfl⟩

end H53489
