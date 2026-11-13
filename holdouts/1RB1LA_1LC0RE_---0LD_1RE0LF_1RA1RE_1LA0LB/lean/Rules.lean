import Machine

/-! # Run rules of 1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB

The tape is a list of blocks of 1s. E runs right over a block (E1 -> 1RE) and A runs left over one (A1 -> 1LA); every other move happens at the edges of blocks.

Written by `bbtools.symtm.prove` (the trace of a symbolic run, checked by the kernel). -/

namespace H140043

open TM

/-- E runs right over a block of 1s, one step a cell. -/
theorem e_run (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .E⟩ = some ⟨rep (n) [true] (L), R, .E⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .E⟩ = some ⟨app [] (app [true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .E⟩ = some ⟨rep (n) [true] (L), R, .E⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)


/-- A runs left over a block of 1s, one step a cell. -/
theorem a_run (n : Nat) (L R : Tape) :
    steps (n) ⟨rep (n) [true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨rep (n) [true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true] (R)), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)


end H140043
