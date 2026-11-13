import Machine

/-! # Crossing rules of 1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC

The tape is made of domains of the pairs `01` and `10`. Moving right, E and A cross a domain at once, flipping its phase (`01` <-> `10`).

Written by `bbtools.symtm.prove` (the trace of a symbolic run, checked by the kernel). -/

namespace H18046

open TM

/-- E crosses pairs `01`, leaving pairs `10`. -/
theorem e_cross (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [false, true] (R), .E⟩ = some ⟨rep (n) [false, true] (L), R, .E⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .E⟩ = some ⟨app [] (app [false, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [false, true] (R), .E⟩ = some ⟨rep (n) [false, true] (L), R, .E⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)


/-- A crosses pairs `10`, leaving pairs `01`. -/
theorem a_cross (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, false] (R), .A⟩ = some ⟨rep (n) [true, false] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .A⟩ = some ⟨app [] (app [true, false] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, false] (R), .A⟩ = some ⟨rep (n) [true, false] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)


end H18046
