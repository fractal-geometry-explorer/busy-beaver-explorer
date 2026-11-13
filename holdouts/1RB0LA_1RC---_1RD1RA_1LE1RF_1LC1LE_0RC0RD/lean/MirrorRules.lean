import MirrorMachine

/-! The three local rules of the tick, written by `bbtools.symtm.prove` (from `holdouts/1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD/py/counter.py`). -/

namespace H44966M

open TM

/-- The sweep: `0^4 D> 1^(5+4n) 0` becomes the counter at zero, `0 1 1 0 0 0 (0000)^n 1 1 1 1 E>`. -/
theorem rule_sweep (n : Nat) (L R : Tape) :
    steps (4 * n + 20) ⟨cons false (cons false (cons false (cons false (L)))), cons true (cons true (cons true (cons true (cons true (rep (n) [true, true, true, true] (cons false (R))))))), .D⟩ = some ⟨cons true (cons true (cons true (cons true (rep (n) [false, false, false, false] (cons false (cons false (cons false (cons true (cons true (cons false (L))))))))))), R, .E⟩ := by
  have h0 : steps 10 ⟨cons false (cons false (cons false (cons false (L)))), cons true (cons true (cons true (cons true (cons true (rep (n) [true, true, true, true] (cons false (R))))))), .D⟩ = some ⟨cons false (cons false (cons false (cons true (cons true (cons false (L)))))), cons true (cons true (cons true (rep (n) [true, true, true, true] (cons false (R))))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons false (cons false (cons true (cons true (cons false (L)))))), cons true (cons true (cons true (rep (n) [true, true, true, true] (cons false (R))))), .A⟩ = some ⟨cons false (cons false (cons false (cons true (cons true (cons false (L)))))), rep (n) [true, true, true, true] (cons true (cons true (cons true (cons false (R))))), .A⟩ := by
    simp only [steps_zero, show cons true (cons true (cons true (rep (n) [true, true, true, true] (cons false (R))))) = rep (n) [true, true, true, true] (cons true (cons true (cons true (cons false (R))))) from
      rep_rotate (n) [true, true, true] [true, true, true, true] [true, true, true, true] rfl (cons false (R))]
  have c2 : ∀ L R : Tape, steps 4 ⟨app [] L, app [true, true, true, true] R, .A⟩ = some ⟨app [] (app [false, false, false, false] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((n) * 4) ⟨cons false (cons false (cons false (cons true (cons true (cons false (L)))))), rep (n) [true, true, true, true] (cons true (cons true (cons true (cons false (R))))), .A⟩ = some ⟨rep (n) [false, false, false, false] (cons false (cons false (cons false (cons true (cons true (cons false (L))))))), cons true (cons true (cons true (cons false (R)))), .A⟩ :=
    cross_r trans c2 (n) (cons false (cons false (cons false (cons true (cons true (cons false (L))))))) (cons true (cons true (cons true (cons false (R)))))
  have h3 : steps 10 ⟨rep (n) [false, false, false, false] (cons false (cons false (cons false (cons true (cons true (cons false (L))))))), cons true (cons true (cons true (cons false (R)))), .A⟩ = some ⟨cons true (cons true (cons true (cons true (rep (n) [false, false, false, false] (cons false (cons false (cons false (cons true (cons true (cons false (L))))))))))), R, .E⟩ := rfl
  exact steps_congr trans (a := 10 + (0 + ((n) * 4 + (10)))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

/-- The increment: back from an excursion, the head adds one to the counter (n trailing ones) and enters the word again. -/
theorem rule_inc (n : Nat) (L R : Tape) :
    steps (18 * n + 33) ⟨cons true (cons true (cons true (rep (n) [false, false, false, true] (cons false (cons false (cons false (cons false (L)))))))), cons true (R), .F⟩ = some ⟨cons true (cons true (cons true (cons true (cons false (rep (n) [false, false, false, false] (cons false (cons false (cons true (L))))))))), R, .E⟩ := by
  have h0 : steps 2 ⟨cons true (cons true (cons true (rep (n) [false, false, false, true] (cons false (cons false (cons false (cons false (L)))))))), cons true (R), .F⟩ = some ⟨cons true (rep (n) [false, false, false, true] (cons false (cons false (cons false (cons false (L)))))), cons true (cons true (cons false (R))), .F⟩ := rfl
  have h1 : steps 0 ⟨cons true (rep (n) [false, false, false, true] (cons false (cons false (cons false (cons false (L)))))), cons true (cons true (cons false (R))), .F⟩ = some ⟨rep (n) [true, false, false, false] (cons true (cons false (cons false (cons false (cons false (L)))))), cons true (cons true (cons false (R))), .F⟩ := by
    simp only [steps_zero, show cons true (rep (n) [false, false, false, true] (cons false (cons false (cons false (cons false (L)))))) = rep (n) [true, false, false, false] (cons true (cons false (cons false (cons false (cons false (L)))))) from
      rep_rotate (n) [true] [false, false, false, true] [true, false, false, false] rfl (cons false (cons false (cons false (cons false (L)))))]
  have c2 : ∀ L R : Tape, steps 14 ⟨app [true, false, false, false] L, app [true] R, .F⟩ = some ⟨L, app [true] (app [true, true, true, true] R), .F⟩ := fun _ _ => rfl
  have h2 : steps ((n) * 14) ⟨rep (n) [true, false, false, false] (cons true (cons false (cons false (cons false (cons false (L)))))), cons true (cons true (cons false (R))), .F⟩ = some ⟨cons true (cons false (cons false (cons false (cons false (L))))), cons true (rep (n) [true, true, true, true] (cons true (cons false (R)))), .F⟩ :=
    cross_l trans c2 (n) (cons true (cons false (cons false (cons false (cons false (L)))))) (cons true (cons false (R)))
  have h3 : steps 20 ⟨cons true (cons false (cons false (cons false (cons false (L))))), cons true (rep (n) [true, true, true, true] (cons true (cons false (R)))), .F⟩ = some ⟨cons false (cons false (cons true (L))), cons true (cons true (cons true (rep (n) [true, true, true, true] (cons true (cons false (R)))))), .A⟩ := rfl
  have h4 : steps 0 ⟨cons false (cons false (cons true (L))), cons true (cons true (cons true (rep (n) [true, true, true, true] (cons true (cons false (R)))))), .A⟩ = some ⟨cons false (cons false (cons true (L))), rep (n) [true, true, true, true] (cons true (cons true (cons true (cons true (cons false (R)))))), .A⟩ := by
    simp only [steps_zero, show cons true (cons true (cons true (rep (n) [true, true, true, true] (cons true (cons false (R)))))) = rep (n) [true, true, true, true] (cons true (cons true (cons true (cons true (cons false (R)))))) from
      rep_rotate (n) [true, true, true] [true, true, true, true] [true, true, true, true] rfl (cons true (cons false (R)))]
  have c5 : ∀ L R : Tape, steps 4 ⟨app [] L, app [true, true, true, true] R, .A⟩ = some ⟨app [] (app [false, false, false, false] L), R, .A⟩ := fun _ _ => rfl
  have h5 : steps ((n) * 4) ⟨cons false (cons false (cons true (L))), rep (n) [true, true, true, true] (cons true (cons true (cons true (cons true (cons false (R)))))), .A⟩ = some ⟨rep (n) [false, false, false, false] (cons false (cons false (cons true (L)))), cons true (cons true (cons true (cons true (cons false (R))))), .A⟩ :=
    cross_r trans c5 (n) (cons false (cons false (cons true (L)))) (cons true (cons true (cons true (cons true (cons false (R))))))
  have h6 : steps 11 ⟨rep (n) [false, false, false, false] (cons false (cons false (cons true (L)))), cons true (cons true (cons true (cons true (cons false (R))))), .A⟩ = some ⟨cons true (cons true (cons true (cons true (cons false (rep (n) [false, false, false, false] (cons false (cons false (cons true (L))))))))), R, .E⟩ := rfl
  exact steps_congr trans (a := 2 + (0 + ((n) * 14 + (20 + (0 + ((n) * 4 + (11))))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (h6)))))))

/-- The finish: back from the last excursion with the counter full, the head fills the block: `D> 1^(9+4n) 0`. -/
theorem rule_fin (n : Nat) (L R : Tape) :
    steps (14 * n + 27) ⟨cons true (cons true (cons true (rep (n) [false, false, false, true] (cons false (cons false (cons false (cons true (cons true (cons false (L)))))))))), cons true (R), .F⟩ = some ⟨L, cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (rep (n) [true, true, true, true] (cons true (cons false (R))))))))))), .D⟩ := by
  have h0 : steps 2 ⟨cons true (cons true (cons true (rep (n) [false, false, false, true] (cons false (cons false (cons false (cons true (cons true (cons false (L)))))))))), cons true (R), .F⟩ = some ⟨cons true (rep (n) [false, false, false, true] (cons false (cons false (cons false (cons true (cons true (cons false (L)))))))), cons true (cons true (cons false (R))), .F⟩ := rfl
  have h1 : steps 0 ⟨cons true (rep (n) [false, false, false, true] (cons false (cons false (cons false (cons true (cons true (cons false (L)))))))), cons true (cons true (cons false (R))), .F⟩ = some ⟨rep (n) [true, false, false, false] (cons true (cons false (cons false (cons false (cons true (cons true (cons false (L)))))))), cons true (cons true (cons false (R))), .F⟩ := by
    simp only [steps_zero, show cons true (rep (n) [false, false, false, true] (cons false (cons false (cons false (cons true (cons true (cons false (L)))))))) = rep (n) [true, false, false, false] (cons true (cons false (cons false (cons false (cons true (cons true (cons false (L)))))))) from
      rep_rotate (n) [true] [false, false, false, true] [true, false, false, false] rfl (cons false (cons false (cons false (cons true (cons true (cons false (L)))))))]
  have c2 : ∀ L R : Tape, steps 14 ⟨app [true, false, false, false] L, app [true] R, .F⟩ = some ⟨L, app [true] (app [true, true, true, true] R), .F⟩ := fun _ _ => rfl
  have h2 : steps ((n) * 14) ⟨rep (n) [true, false, false, false] (cons true (cons false (cons false (cons false (cons true (cons true (cons false (L)))))))), cons true (cons true (cons false (R))), .F⟩ = some ⟨cons true (cons false (cons false (cons false (cons true (cons true (cons false (L))))))), cons true (rep (n) [true, true, true, true] (cons true (cons false (R)))), .F⟩ :=
    cross_l trans c2 (n) (cons true (cons false (cons false (cons false (cons true (cons true (cons false (L)))))))) (cons true (cons false (R)))
  have h3 : steps 25 ⟨cons true (cons false (cons false (cons false (cons true (cons true (cons false (L))))))), cons true (rep (n) [true, true, true, true] (cons true (cons false (R)))), .F⟩ = some ⟨L, cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (rep (n) [true, true, true, true] (cons true (cons false (R))))))))))), .D⟩ := rfl
  exact steps_congr trans (a := 2 + (0 + ((n) * 14 + (25)))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

end H44966M
