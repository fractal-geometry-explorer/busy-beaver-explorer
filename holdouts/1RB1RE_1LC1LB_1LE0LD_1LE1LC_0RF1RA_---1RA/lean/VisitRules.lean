import Machine

/-! The moves of one visit of the left end, each for every value of its counts and every tape in its contexts. Written by `py/visit_rules.py` with `bbtools.symtm.prove`; checked by the kernel. -/

namespace H175628

open TM

/-- The first five steps of a visit. -/
theorem enter (R : Tape) :
    steps (5) ⟨blank, cons false (R), .B⟩ = some ⟨cons true (cons true (cons false (blank))), R, .E⟩ := by
  have h0 : steps 5 ⟨blank, cons false (R), .B⟩ = some ⟨cons true (cons true (cons false (blank))), R, .E⟩ := rfl
  exact steps_congr trans (a := 5) (by omega) (h0)

/-- E crosses the rest of an even run and enters the next run, which is even. -/
theorem scan_even (a : Nat) (L R : Tape) :
    steps (2 * a + 3) ⟨L, rep (a) [true, true] (cons false (cons true (cons true (R)))), .E⟩ = some ⟨cons true (cons true (cons false (rep (a) [true, true] (L)))), R, .E⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((a) * 2) ⟨L, rep (a) [true, true] (cons false (cons true (cons true (R)))), .E⟩ = some ⟨rep (a) [true, true] (L), cons false (cons true (cons true (R))), .E⟩ :=
    cross_r trans c0 (a) (L) (cons false (cons true (cons true (R))))
  have h1 : steps 3 ⟨rep (a) [true, true] (L), cons false (cons true (cons true (R))), .E⟩ = some ⟨cons true (cons true (cons false (rep (a) [true, true] (L)))), R, .E⟩ := rfl
  exact steps_congr trans (a := (a) * 2 + (3)) (by omega) (steps_seq trans h0 (h1))

/-- E reaches an odd run followed by another run: the two are joined and B returns to the 0 before them. -/
theorem scan_odd (a b : Nat) (L R : Tape) :
    steps (2 * a + 4 * b + 6) ⟨L, rep (a) [true, true] (cons false (cons true (rep (b) [true, true] (cons false (cons true (R)))))), .E⟩ = some ⟨rep (a) [true, true] (L), cons false (cons true (cons true (rep (b) [true, true] (cons true (R))))), .B⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((a) * 2) ⟨L, rep (a) [true, true] (cons false (cons true (rep (b) [true, true] (cons false (cons true (R)))))), .E⟩ = some ⟨rep (a) [true, true] (L), cons false (cons true (rep (b) [true, true] (cons false (cons true (R))))), .E⟩ :=
    cross_r trans c0 (a) (L) (cons false (cons true (rep (b) [true, true] (cons false (cons true (R))))))
  have h1 : steps 2 ⟨rep (a) [true, true] (L), cons false (cons true (rep (b) [true, true] (cons false (cons true (R))))), .E⟩ = some ⟨cons true (cons false (rep (a) [true, true] (L))), rep (b) [true, true] (cons false (cons true (R))), .A⟩ := rfl
  have c2 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .A⟩ = some ⟨app [] (app [true, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((b) * 2) ⟨cons true (cons false (rep (a) [true, true] (L))), rep (b) [true, true] (cons false (cons true (R))), .A⟩ = some ⟨rep (b) [true, true] (cons true (cons false (rep (a) [true, true] (L)))), cons false (cons true (R)), .A⟩ :=
    cross_r trans c2 (b) (cons true (cons false (rep (a) [true, true] (L)))) (cons false (cons true (R)))
  have h3 : steps 2 ⟨rep (b) [true, true] (cons true (cons false (rep (a) [true, true] (L)))), cons false (cons true (R)), .A⟩ = some ⟨rep (b) [true, true] (cons true (cons false (rep (a) [true, true] (L)))), cons true (cons true (R)), .B⟩ := rfl
  have c4 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h4 : steps ((b) * 2) ⟨rep (b) [true, true] (cons true (cons false (rep (a) [true, true] (L)))), cons true (cons true (R)), .B⟩ = some ⟨cons true (cons false (rep (a) [true, true] (L))), cons true (rep (b) [true, true] (cons true (R))), .B⟩ :=
    cross_l trans c4 (b) (cons true (cons false (rep (a) [true, true] (L)))) (cons true (R))
  have h5 : steps 2 ⟨cons true (cons false (rep (a) [true, true] (L))), cons true (rep (b) [true, true] (cons true (R))), .B⟩ = some ⟨rep (a) [true, true] (L), cons false (cons true (cons true (rep (b) [true, true] (cons true (R))))), .B⟩ := rfl
  exact steps_congr trans (a := (a) * 2 + (2 + ((b) * 2 + (2 + ((b) * 2 + (2)))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (h5))))))

/-- E reaches an odd run followed by two 0s. -/
theorem scan_last (a b : Nat) (L R : Tape) :
    steps (2 * a + 4 * b + 6) ⟨L, rep (a) [true, true] (cons false (cons true (rep (b) [true, true] (cons false (cons false (R)))))), .E⟩ = some ⟨rep (a) [true, true] (L), cons false (cons true (cons false (rep (b) [true, false] (cons true (R))))), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((a) * 2) ⟨L, rep (a) [true, true] (cons false (cons true (rep (b) [true, true] (cons false (cons false (R)))))), .E⟩ = some ⟨rep (a) [true, true] (L), cons false (cons true (rep (b) [true, true] (cons false (cons false (R))))), .E⟩ :=
    cross_r trans c0 (a) (L) (cons false (cons true (rep (b) [true, true] (cons false (cons false (R))))))
  have h1 : steps 2 ⟨rep (a) [true, true] (L), cons false (cons true (rep (b) [true, true] (cons false (cons false (R))))), .E⟩ = some ⟨cons true (cons false (rep (a) [true, true] (L))), rep (b) [true, true] (cons false (cons false (R))), .A⟩ := rfl
  have c2 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .A⟩ = some ⟨app [] (app [true, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((b) * 2) ⟨cons true (cons false (rep (a) [true, true] (L))), rep (b) [true, true] (cons false (cons false (R))), .A⟩ = some ⟨rep (b) [true, true] (cons true (cons false (rep (a) [true, true] (L)))), cons false (cons false (R)), .A⟩ :=
    cross_r trans c2 (b) (cons true (cons false (rep (a) [true, true] (L)))) (cons false (cons false (R)))
  have h3 : steps 2 ⟨rep (b) [true, true] (cons true (cons false (rep (a) [true, true] (L)))), cons false (cons false (R)), .A⟩ = some ⟨rep (b) [true, true] (cons true (cons false (rep (a) [true, true] (L)))), cons true (cons true (R)), .C⟩ := rfl
  have c4 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, false] R), .C⟩ := fun _ _ => rfl
  have h4 : steps ((b) * 2) ⟨rep (b) [true, true] (cons true (cons false (rep (a) [true, true] (L)))), cons true (cons true (R)), .C⟩ = some ⟨cons true (cons false (rep (a) [true, true] (L))), cons true (rep (b) [true, false] (cons true (R))), .C⟩ :=
    cross_l trans c4 (b) (cons true (cons false (rep (a) [true, true] (L)))) (cons true (R))
  have h5 : steps 2 ⟨cons true (cons false (rep (a) [true, true] (L))), cons true (rep (b) [true, false] (cons true (R))), .C⟩ = some ⟨rep (a) [true, true] (L), cons false (cons true (cons false (rep (b) [true, false] (cons true (R))))), .C⟩ := rfl
  exact steps_congr trans (a := (a) * 2 + (2 + ((b) * 2 + (2 + ((b) * 2 + (2)))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (h5))))))

/-- E reaches two 0s: F is on a 0. -/
theorem scan_halt (a : Nat) (L R : Tape) :
    steps (2 * a + 1) ⟨L, rep (a) [true, true] (cons false (cons false (R))), .E⟩ = some ⟨cons false (rep (a) [true, true] (L)), cons false (R), .F⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .E⟩ = some ⟨app [] (app [true, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((a) * 2) ⟨L, rep (a) [true, true] (cons false (cons false (R))), .E⟩ = some ⟨rep (a) [true, true] (L), cons false (cons false (R)), .E⟩ :=
    cross_r trans c0 (a) (L) (cons false (cons false (R)))
  have h1 : steps 1 ⟨rep (a) [true, true] (L), cons false (cons false (R)), .E⟩ = some ⟨cons false (rep (a) [true, true] (L)), cons false (R), .F⟩ := rfl
  exact steps_congr trans (a := (a) * 2 + (1)) (by omega) (steps_seq trans h0 (h1))

/-- B fills the 0 and C, D turn the even run on the left into units. -/
theorem fillzig (t : Nat) (L R : Tape) :
    steps (2 * t + 3) ⟨cons true (cons true (rep (t) [true, true] (cons false (L)))), cons false (R), .B⟩ = some ⟨L, cons false (cons true (rep (t) [false, true] (cons false (cons true (R))))), .C⟩ := by
  have h0 : steps 2 ⟨cons true (cons true (rep (t) [true, true] (cons false (L)))), cons false (R), .B⟩ = some ⟨rep (t) [true, true] (cons false (L)), cons true (cons false (cons true (R))), .D⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [false, true] R), .D⟩ := fun _ _ => rfl
  have h1 : steps ((t) * 2) ⟨rep (t) [true, true] (cons false (L)), cons true (cons false (cons true (R))), .D⟩ = some ⟨cons false (L), cons true (rep (t) [false, true] (cons false (cons true (R)))), .D⟩ :=
    cross_l trans c1 (t) (cons false (L)) (cons false (cons true (R)))
  have h2 : steps 1 ⟨cons false (L), cons true (rep (t) [false, true] (cons false (cons true (R)))), .D⟩ = some ⟨L, cons false (cons true (rep (t) [false, true] (cons false (cons true (R))))), .C⟩ := rfl
  exact steps_congr trans (a := 2 + ((t) * 2 + (1))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- C fills the 0; the run on the left takes two units and B returns to the 0 before it. -/
theorem stage (c : Nat) (L R : Tape) :
    steps (2 * c + 11) ⟨cons true (cons true (rep (c) [true, true] (cons false (L)))), cons false (cons true (cons false (cons true (R)))), .C⟩ = some ⟨L, cons false (cons true (rep (c) [true, true] (cons true (cons true (cons true (cons true (cons true (R)))))))), .B⟩ := by
  have h0 : steps 10 ⟨cons true (cons true (rep (c) [true, true] (cons false (L)))), cons false (cons true (cons false (cons true (R)))), .C⟩ = some ⟨rep (c) [true, true] (cons false (L)), cons true (cons true (cons true (cons true (cons true (cons true (R)))))), .B⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h1 : steps ((c) * 2) ⟨rep (c) [true, true] (cons false (L)), cons true (cons true (cons true (cons true (cons true (cons true (R)))))), .B⟩ = some ⟨cons false (L), cons true (rep (c) [true, true] (cons true (cons true (cons true (cons true (cons true (R))))))), .B⟩ :=
    cross_l trans c1 (c) (cons false (L)) (cons true (cons true (cons true (cons true (cons true (R))))))
  have h2 : steps 1 ⟨cons false (L), cons true (rep (c) [true, true] (cons true (cons true (cons true (cons true (cons true (R))))))), .B⟩ = some ⟨L, cons false (cons true (rep (c) [true, true] (cons true (cons true (cons true (cons true (cons true (R)))))))), .B⟩ := rfl
  exact steps_congr trans (a := 10 + ((c) * 2 + (1))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- At the left end five units become a 6 and a 4. -/
theorem left_end (R : Tape) :
    steps (44) ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))))))), .C⟩ = some ⟨blank, cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons false (cons true (cons true (cons true (cons true (cons false (R))))))))))))), .B⟩ := by
  have h0 : steps 44 ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))))))), .C⟩ = some ⟨blank, cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons false (cons true (cons true (cons true (cons true (cons false (R))))))))))))), .B⟩ := rfl
  exact steps_congr trans (a := 44) (by omega) (h0)

end H175628
