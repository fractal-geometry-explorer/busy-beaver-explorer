import Machine

/-! The long crossings of 1RB1RD_1LC0RD_0LE1RD_1RA0RB_---1LF_1RA0LF. Written by `py/rules.py` (`bbtools.symtm.prove` and `TM.cross_l`); checked by the kernel. -/

namespace H71111

open TM

/-- Going right through the bulk: B, with 01111 behind it, turns every word 01010000000 into 01111111111, 53 steps a word. -/
theorem bulk_right (n : Nat) (L R : Tape) :
    steps (53 * n + 53) ⟨cons true (cons true (cons true (cons true (cons false (L))))), rep (n + 1) [false, true, false, true, false, false, false, false, false, false, false] (R), .B⟩ = some ⟨cons true (rep (n + 1) [true, true, true, false, true, true, true, true, true, true, true] (cons true (cons true (cons true (cons false (L)))))), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 53 ⟨app [true] L, app [false, true, false, true, false, false, false, false, false, false, false] R, .B⟩ = some ⟨app [true] (app [true, true, true, false, true, true, true, true, true, true, true] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 53) ⟨cons true (cons true (cons true (cons true (cons false (L))))), rep (n + 1) [false, true, false, true, false, false, false, false, false, false, false] (R), .B⟩ = some ⟨cons true (rep (n + 1) [true, true, true, false, true, true, true, true, true, true, true] (cons true (cons true (cons true (cons false (L)))))), R, .B⟩ :=
    cross_r trans c0 (n + 1) (cons true (cons true (cons true (cons false (L))))) (R)
  exact steps_congr trans (a := (n + 1) * 53) (by omega) (h0)

/-- Coming back through the bulk: F, on the first of twelve 0s, turns every word 01111111111 on its left into 10100000000 on its right, 19 steps a word. -/
theorem bulk_left (n : Nat) (L R : Tape) :
    steps (n * 19) ⟨rep n [true, true, true, true, true, true, true, true, true, true, false] L, app [false, false, false, false, false, false, false, false, false, false, false, false] R, .F⟩ = some ⟨L, app [false, false, false, false, false, false, false, false, false, false, false, false] (rep n [true, false, true, false, false, false, false, false, false, false, false] R), .F⟩ := by
  have c0 : ∀ L R : Tape, steps 19 ⟨app [true, true, true, true, true, true, true, true, true, true, false] L, app [false, false, false, false, false, false, false, false, false, false, false, false] R, .F⟩ = some ⟨L, app [false, false, false, false, false, false, false, false, false, false, false, false] (app [true, false, true, false, false, false, false, false, false, false, false] R), .F⟩ :=
    fun _ _ => rfl
  exact cross_l trans c0 n L R

/-- In the counter list: F, on the first of four 0s, turns every 011 on its left into 101 on its right, 11 steps a word. -/
theorem list_left (n : Nat) (L R : Tape) :
    steps (n * 11) ⟨rep n [true, true, false] L, app [false, false, false, false] R, .F⟩ = some ⟨L, app [false, false, false, false] (rep n [true, false, true] R), .F⟩ := by
  have c0 : ∀ L R : Tape, steps 11 ⟨app [true, true, false] L, app [false, false, false, false] R, .F⟩ = some ⟨L, app [false, false, false, false] (app [true, false, true] R), .F⟩ :=
    fun _ _ => rfl
  exact cross_l trans c0 n L R

end H71111
