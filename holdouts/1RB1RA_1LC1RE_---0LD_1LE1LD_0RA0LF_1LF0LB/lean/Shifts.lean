import Machine

/-! # Shift rules: the head crosses a run of a repeated word, for any length of the run

Proved by `bbtools.symtm.prove` (re-run `py/` scripts or symtm to regenerate). -/

namespace H92364

open TM

/-- State A runs right through a block of 1s (`L A> (1)^n R` becomes `L (1)^n A> R`.) -/
theorem cross_ones_right (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .A⟩ = some ⟨rep (n) [true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .A⟩ = some ⟨app [] (app [true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .A⟩ = some ⟨rep (n) [true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- State D runs left through a block of 1s (`L (1)^n D> 1 R` becomes `L D> 1 (1)^n R`.) -/
theorem cross_ones_left (n : Nat) (L R : Tape) :
    steps (n) ⟨rep (n) [true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [true] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [true] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨rep (n) [true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [true] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

end H92364
