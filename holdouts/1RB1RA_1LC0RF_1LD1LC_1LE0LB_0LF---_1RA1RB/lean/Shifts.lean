import Machine

/-! # Shift rules: the head crosses a run of a repeated word, for any length of the run

Proved by `bbtools.symtm.prove` (re-run `py/` scripts or symtm to regenerate). -/

namespace H7085

open TM

/-- State A runs right through a block of 1s (`L A> (1)^n R` becomes `L (1)^n A> R`.) -/
theorem cross_ones_right (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .A⟩ = some ⟨rep (n) [true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .A⟩ = some ⟨app [] (app [true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .A⟩ = some ⟨rep (n) [true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- State C runs left through a block of 1s (`L (1)^n C> 1 R` becomes `L C> 1 (1)^n R`.) -/
theorem cross_ones_left (n : Nat) (L R : Tape) :
    steps (n) ⟨rep (n) [true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨rep (n) [true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

end H7085
