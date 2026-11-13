import Machine

/-! # Crossing rules of 1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---

Much of the tape is pairs `01` / `10`. D and E cross them to the right and E and C to the left, a whole run at once, D and E flipping the phase of the pairs.

Written by `bbtools.symtm.prove` (the trace of a symbolic run, checked by the kernel). -/

namespace H71372

open TM

/-- D crosses pairs `01` to the right, leaving `10`. -/
theorem d_cross (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [false, true] (R), .D⟩ = some ⟨rep (n) [false, true] (L), R, .D⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .D⟩ = some ⟨app [] (app [false, true] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [false, true] (R), .D⟩ = some ⟨rep (n) [false, true] (L), R, .D⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)


/-- E crosses pairs `10` to the right, leaving `01`. -/
theorem e_cross (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, false] (R), .E⟩ = some ⟨rep (n) [true, false] (L), R, .E⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .E⟩ = some ⟨app [] (app [true, false] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, false] (R), .E⟩ = some ⟨rep (n) [true, false] (L), R, .E⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)


/-- E crosses pairs `01` to the left. -/
theorem e_back (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [true, false] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .E⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [false, true] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [true, false] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .E⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)


/-- C crosses pairs `10` to the left. -/
theorem c_back (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [false, true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, false] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [false, true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)


end H71372
