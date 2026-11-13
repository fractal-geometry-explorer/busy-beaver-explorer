import Machine

/-! # The sweep rule of the outer counter, proved by `bbtools.symtm.prove` -/

namespace H55074

open TM

/-- One sweep of a phase: the block of 1s at the right end grows by 6 and the block of 0s on its left shrinks by 4 (in 10b+38 steps). The final tape is 1^(2b+12) written out as the prover leaves it. -/
theorem sweep (a b : Nat) (L : Tape) :
    steps (10 * b + 38) ⟨rep (b + 3) [true, true] (rep (a + 2) [false, false] (L)), blank, .A⟩ = some ⟨cons true (cons true (cons true (rep (b + 1) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (rep (a) [false, false] (L)))))))))))), blank, .A⟩ := by
  have h0 : steps 8 ⟨rep (b + 3) [true, true] (rep (a + 2) [false, false] (L)), blank, .A⟩ = some ⟨rep (b + 1) [true, true] (rep (a + 2) [false, false] (L)), cons true (cons true (cons false (cons true (cons true (cons true (blank)))))), .F⟩ := rfl
  have c1 : ∀ L R : Tape, steps 8 ⟨app [true, true] L, app [true, true, false] R, .F⟩ = some ⟨L, app [true, true, false] (app [true, true] R), .F⟩ := fun _ _ => rfl
  have h1 : steps ((b + 1) * 8) ⟨rep (b + 1) [true, true] (rep (a + 2) [false, false] (L)), cons true (cons true (cons false (cons true (cons true (cons true (blank)))))), .F⟩ = some ⟨rep (a + 2) [false, false] (L), cons true (cons true (cons false (rep (b + 1) [true, true] (cons true (cons true (cons true (blank))))))), .F⟩ :=
    cross_l trans c1 (b + 1) (rep (a + 2) [false, false] (L)) (cons true (cons true (cons true (blank))))
  have h2 : steps 17 ⟨rep (a + 2) [false, false] (L), cons true (cons true (cons false (rep (b + 1) [true, true] (cons true (cons true (cons true (blank))))))), .F⟩ = some ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (rep (a) [false, false] (L)))))))), rep (b + 1) [true, true] (cons true (cons true (cons true (blank)))), .A⟩ := rfl
  have c3 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .A⟩ = some ⟨app [] (app [true, true] L), R, .A⟩ := fun _ _ => rfl
  have h3 : steps ((b + 1) * 2) ⟨cons true (cons true (cons true (cons true (cons true (cons true (cons true (rep (a) [false, false] (L)))))))), rep (b + 1) [true, true] (cons true (cons true (cons true (blank)))), .A⟩ = some ⟨rep (b + 1) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (rep (a) [false, false] (L))))))))), cons true (cons true (cons true (blank))), .A⟩ :=
    cross_r trans c3 (b + 1) (cons true (cons true (cons true (cons true (cons true (cons true (cons true (rep (a) [false, false] (L))))))))) (cons true (cons true (cons true (blank))))
  have h4 : steps 3 ⟨rep (b + 1) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (rep (a) [false, false] (L))))))))), cons true (cons true (cons true (blank))), .A⟩ = some ⟨cons true (cons true (cons true (rep (b + 1) [true, true] (cons true (cons true (cons true (cons true (cons true (cons true (cons true (rep (a) [false, false] (L)))))))))))), blank, .A⟩ := rfl
  exact steps_congr trans (a := 8 + ((b + 1) * 8 + (17 + ((b + 1) * 2 + (3))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

end H55074
