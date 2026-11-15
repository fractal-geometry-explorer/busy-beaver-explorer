import Machine

/-! The two sweeps through the block of 1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC. Written by `py/rules.py` with `bbtools.symtm.prove`; checked by the kernel. -/

namespace H151599

open TM

/-- The leftward sweep: the block of words 01011111 becomes a block of words 11101000. -/
theorem sweep_left (n : Nat) (L : Tape) :
    steps (38 * n + 118) ⟨cons true (cons true (rep (n + 3) [true, true, true, true, true, false, true, false] (L))), cons false (blank), .B⟩ = some ⟨L, cons true (rep (n + 3) [true, true, false, true, false, false, false, true] (cons true (cons false (cons true (blank))))), .D⟩ := by
  have h0 : steps 4 ⟨cons true (cons true (rep (n + 3) [true, true, true, true, true, false, true, false] (L))), cons false (blank), .B⟩ = some ⟨rep (n + 3) [true, true, true, true, true, false, true, false] (L), cons true (cons true (cons false (cons true (blank)))), .D⟩ := rfl
  have c1 : ∀ L R : Tape, steps 38 ⟨app [true, true, true, true, true, false, true, false] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [true, true, false, true, false, false, false, true] R), .D⟩ := fun _ _ => rfl
  have h1 : steps ((n + 3) * 38) ⟨rep (n + 3) [true, true, true, true, true, false, true, false] (L), cons true (cons true (cons false (cons true (blank)))), .D⟩ = some ⟨L, cons true (rep (n + 3) [true, true, false, true, false, false, false, true] (cons true (cons false (cons true (blank))))), .D⟩ :=
    cross_l trans c1 (n + 3) (L) (cons true (cons false (cons true (blank))))
  exact steps_congr trans (a := 4 + ((n + 3) * 38)) (by omega) (steps_seq trans h0 (h1))

/-- The way back: with 010111 on its left, B converts the block of words 11101000 into words 11010111 (the words 01011111 again, re-bracketed), 26 steps a word, for every tape on both sides. -/
theorem sweep_right (n : Nat) (L R : Tape) :
    steps (26 * n + 26) ⟨cons true (cons true (cons true (cons false (cons true (cons false (L)))))), rep (n + 1) [true, true, true, false, true, false, false, false] (R), .B⟩ = some ⟨cons true (cons true (cons true (cons false (cons true (cons false (rep (n) [true, true, true, false, true, false, true, true] (cons true (cons true (cons true (cons false (cons true (cons false (cons true (cons true (L))))))))))))))), R, .B⟩ := by
  have h0 : steps 23 ⟨cons true (cons true (cons true (cons false (cons true (cons false (L)))))), rep (n + 1) [true, true, true, false, true, false, false, false] (R), .B⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (cons true (cons false (cons true (cons false (cons true (cons true (L))))))))))), cons false (cons false (cons false (rep (n) [true, true, true, false, true, false, false, false] (R)))), .F⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (cons false (cons true (cons true (cons true (cons false (cons true (cons false (cons true (cons true (L))))))))))), cons false (cons false (cons false (rep (n) [true, true, true, false, true, false, false, false] (R)))), .F⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (cons true (cons false (cons true (cons false (cons true (cons true (L))))))))))), rep (n) [false, false, false, true, true, true, false, true] (cons false (cons false (cons false (R)))), .F⟩ := by
    simp only [steps_zero, show cons false (cons false (cons false (rep (n) [true, true, true, false, true, false, false, false] (R)))) = rep (n) [false, false, false, true, true, true, false, true] (cons false (cons false (cons false (R)))) from
      rep_rotate (n) [false, false, false] [true, true, true, false, true, false, false, false] [false, false, false, true, true, true, false, true] rfl (R)]
  have c2 : ∀ L R : Tape, steps 26 ⟨app [false, true, false] L, app [false, false, false, true, true, true, false, true] R, .F⟩ = some ⟨app [false, true, false] (app [true, true, true, false, true, false, true, true] L), R, .F⟩ := fun _ _ => rfl
  have h2 : steps ((n) * 26) ⟨cons false (cons true (cons false (cons true (cons true (cons true (cons false (cons true (cons false (cons true (cons true (L))))))))))), rep (n) [false, false, false, true, true, true, false, true] (cons false (cons false (cons false (R)))), .F⟩ = some ⟨cons false (cons true (cons false (rep (n) [true, true, true, false, true, false, true, true] (cons true (cons true (cons true (cons false (cons true (cons false (cons true (cons true (L)))))))))))), cons false (cons false (cons false (R))), .F⟩ :=
    cross_r trans c2 (n) (cons true (cons true (cons true (cons false (cons true (cons false (cons true (cons true (L))))))))) (cons false (cons false (cons false (R))))
  have h3 : steps 3 ⟨cons false (cons true (cons false (rep (n) [true, true, true, false, true, false, true, true] (cons true (cons true (cons true (cons false (cons true (cons false (cons true (cons true (L)))))))))))), cons false (cons false (cons false (R))), .F⟩ = some ⟨cons true (cons true (cons true (cons false (cons true (cons false (rep (n) [true, true, true, false, true, false, true, true] (cons true (cons true (cons true (cons false (cons true (cons false (cons true (cons true (L))))))))))))))), R, .B⟩ := rfl
  exact steps_congr trans (a := 23 + (0 + ((n) * 26 + (3)))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

end H151599
