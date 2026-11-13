import Machine

/-! # Crossing rules of 1RB0RA_0RC1LD_0LD0RE_1LB1LE_1RA0LF_0LC---

The tape is built from four-cell words with a single 1 (`0001` and its shifts) and their partners with three 1s (`1101`, `0111`). Moving left, D, C and B cross whole runs of the one-1 words without changing them.

Written by `bbtools.symtm.prove` (the trace of a symbolic run, checked by the kernel). -/

namespace H110703

open TM

/-- D crosses copies of `0001` to the left. -/
theorem d_cross (n : Nat) (L R : Tape) :
    steps (8 * n) ⟨rep (n) [true, false, false, false] (L), cons false (R), .D⟩ = some ⟨L, cons false (rep (n) [false, false, false, true] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 8 ⟨app [true, false, false, false] L, app [false] R, .D⟩ = some ⟨L, app [false] (app [false, false, false, true] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 8) ⟨rep (n) [true, false, false, false] (L), cons false (R), .D⟩ = some ⟨L, cons false (rep (n) [false, false, false, true] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 8) (by omega) (h0)


/-- C crosses copies of `0010` to the left. -/
theorem c_cross (n : Nat) (L R : Tape) :
    steps (8 * n) ⟨rep (n) [false, true, false, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [false, false, true, false] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 8 ⟨app [false, true, false, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [false, false, true, false] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 8) ⟨rep (n) [false, true, false, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [false, false, true, false] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 8) (by omega) (h0)


/-- B crosses copies of `1000` to the left. -/
theorem b_cross (n : Nat) (L R : Tape) :
    steps (8 * n) ⟨rep (n) [false, false, false, true] (L), cons true (R), .B⟩ = some ⟨L, cons true (rep (n) [true, false, false, false] (R)), .B⟩ := by
  have c0 : ∀ L R : Tape, steps 8 ⟨app [false, false, false, true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [true, false, false, false] R), .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 8) ⟨rep (n) [false, false, false, true] (L), cons true (R), .B⟩ = some ⟨L, cons true (rep (n) [true, false, false, false] (R)), .B⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 8) (by omega) (h0)


end H110703
