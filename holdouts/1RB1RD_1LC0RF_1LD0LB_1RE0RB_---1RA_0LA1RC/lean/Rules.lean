import Machine

/-! Writes lean/Rules.lean: shift rules of 1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC. Written by `py/rules.py` with `bbtools.symtm.prove`; checked by the kernel. -/

namespace H92170

open TM

/-- C walks left over ones without changing them (five steps a cell). -/
theorem walk (n : Nat) (L R : Tape) :
    steps (5 * n + 5) ⟨rep (n) [true] (cons true (L)), cons true (R), .C⟩ = some ⟨L, cons true (cons true (rep (n) [true] (R))), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 5 ⟨app [true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 5) ⟨rep (n) [true] (cons true (L)), cons true (R), .C⟩ = some ⟨cons true (L), cons true (rep (n) [true] (R)), .C⟩ :=
    cross_l trans c0 (n) (cons true (L)) (R)
  have h1 : steps 5 ⟨cons true (L), cons true (rep (n) [true] (R)), .C⟩ = some ⟨L, cons true (cons true (rep (n) [true] (R))), .C⟩ := rfl
  exact steps_congr trans (a := (n) * 5 + (5)) (by omega) (steps_seq trans h0 (h1))

/-- C walks left through a block of words 1111110: every 0 moves one cell to the right. -/
theorem words_left (n : Nat) (L R : Tape) :
    steps (27 * n + 32) ⟨rep (n + 1) [true, true, true, true, true, true, false] (cons true (L)), cons true (R), .C⟩ = some ⟨L, cons true (cons true (rep (n) [false, true, true, true, true, true, true] (cons false (cons true (cons true (cons true (cons true (cons true (cons true (R)))))))))), .C⟩ := by
  have h0 : steps 31 ⟨rep (n + 1) [true, true, true, true, true, true, false] (cons true (L)), cons true (R), .C⟩ = some ⟨rep (n) [true, true, true, true, true, true, false] (cons true (L)), cons false (cons false (cons true (cons true (cons true (cons true (cons true (cons true (R)))))))), .B⟩ := rfl
  have c1 : ∀ L R : Tape, steps 27 ⟨app [true, true, true, true, true, true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [false, true, true, true, true, true, true] R), .B⟩ := fun _ _ => rfl
  have h1 : steps ((n) * 27) ⟨rep (n) [true, true, true, true, true, true, false] (cons true (L)), cons false (cons false (cons true (cons true (cons true (cons true (cons true (cons true (R)))))))), .B⟩ = some ⟨cons true (L), cons false (rep (n) [false, true, true, true, true, true, true] (cons false (cons true (cons true (cons true (cons true (cons true (cons true (R))))))))), .B⟩ :=
    cross_l trans c1 (n) (cons true (L)) (cons false (cons true (cons true (cons true (cons true (cons true (cons true (R))))))))
  have h2 : steps 1 ⟨cons true (L), cons false (rep (n) [false, true, true, true, true, true, true] (cons false (cons true (cons true (cons true (cons true (cons true (cons true (R))))))))), .B⟩ = some ⟨L, cons true (cons true (rep (n) [false, true, true, true, true, true, true] (cons false (cons true (cons true (cons true (cons true (cons true (cons true (R)))))))))), .C⟩ := rfl
  exact steps_congr trans (a := 31 + ((n) * 27 + (1))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- The glider 110 (B on its first cell) passes a block of words 1111110 and leaves it unchanged. -/
theorem glider (n : Nat) (L R : Tape) :
    steps (21 * n) ⟨L, cons true (cons true (cons false (rep (n) [true, true, true, true, true, true, false] (R)))), .B⟩ = some ⟨rep (n) [false, true, true, true, true, true, true] (L), cons true (cons true (cons false (R))), .B⟩ := by
  have h0 : steps 0 ⟨L, cons true (cons true (cons false (rep (n) [true, true, true, true, true, true, false] (R)))), .B⟩ = some ⟨L, rep (n) [true, true, false, true, true, true, true] (cons true (cons true (cons false (R)))), .B⟩ := by
    simp only [steps_zero, show cons true (cons true (cons false (rep (n) [true, true, true, true, true, true, false] (R)))) = rep (n) [true, true, false, true, true, true, true] (cons true (cons true (cons false (R)))) from
      rep_rotate (n) [true, true, false] [true, true, true, true, true, true, false] [true, true, false, true, true, true, true] rfl (R)]
  have c1 : ∀ L R : Tape, steps 21 ⟨app [] L, app [true, true, false, true, true, true, true] R, .B⟩ = some ⟨app [] (app [false, true, true, true, true, true, true] L), R, .B⟩ := fun _ _ => rfl
  have h1 : steps ((n) * 21) ⟨L, rep (n) [true, true, false, true, true, true, true] (cons true (cons true (cons false (R)))), .B⟩ = some ⟨rep (n) [false, true, true, true, true, true, true] (L), cons true (cons true (cons false (R))), .B⟩ :=
    cross_r trans c1 (n) (L) (cons true (cons true (cons false (R))))
  exact steps_congr trans (a := 0 + ((n) * 21)) (by omega) (steps_seq trans h0 (h1))

/-- E turns a run of ones into words of five ones. -/
theorem ones_to_words (n : Nat) (L R : Tape) :
    steps (32 * n + 32) ⟨L, cons true (cons true (cons true (cons true (cons true (cons true (cons true (rep (n) [true, true, true, true, true, true] (R)))))))), .E⟩ = some ⟨cons true (cons true (cons true (cons true (cons false (rep (n) [true, true, true, true, true, false] (cons true (L))))))), cons true (R), .E⟩ := by
  have h0 : steps 4 ⟨L, cons true (cons true (cons true (cons true (cons true (cons true (cons true (rep (n) [true, true, true, true, true, true] (R)))))))), .E⟩ = some ⟨cons false (cons false (cons true (cons true (L)))), cons true (cons true (cons true (rep (n) [true, true, true, true, true, true] (R)))), .F⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons false (cons true (cons true (L)))), cons true (cons true (cons true (rep (n) [true, true, true, true, true, true] (R)))), .F⟩ = some ⟨cons false (cons false (cons true (cons true (L)))), rep (n) [true, true, true, true, true, true] (cons true (cons true (cons true (R)))), .F⟩ := by
    simp only [steps_zero, show cons true (cons true (cons true (rep (n) [true, true, true, true, true, true] (R)))) = rep (n) [true, true, true, true, true, true] (cons true (cons true (cons true (R)))) from
      rep_rotate (n) [true, true, true] [true, true, true, true, true, true] [true, true, true, true, true, true] rfl (R)]
  have c2 : ∀ L R : Tape, steps 32 ⟨app [false, false, true] L, app [true, true, true, true, true, true] R, .F⟩ = some ⟨app [false, false, true] (app [true, true, true, true, true, false] L), R, .F⟩ := fun _ _ => rfl
  have h2 : steps ((n) * 32) ⟨cons false (cons false (cons true (cons true (L)))), rep (n) [true, true, true, true, true, true] (cons true (cons true (cons true (R)))), .F⟩ = some ⟨cons false (cons false (cons true (rep (n) [true, true, true, true, true, false] (cons true (L))))), cons true (cons true (cons true (R))), .F⟩ :=
    cross_r trans c2 (n) (cons true (L)) (cons true (cons true (cons true (R))))
  have h3 : steps 28 ⟨cons false (cons false (cons true (rep (n) [true, true, true, true, true, false] (cons true (L))))), cons true (cons true (cons true (R))), .F⟩ = some ⟨cons true (cons true (cons true (cons true (cons false (rep (n) [true, true, true, true, true, false] (cons true (L))))))), cons true (R), .E⟩ := rfl
  exact steps_congr trans (a := 4 + (0 + ((n) * 32 + (28)))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

end H92170
