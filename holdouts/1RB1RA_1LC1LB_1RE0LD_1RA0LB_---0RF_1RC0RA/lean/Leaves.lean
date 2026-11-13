import Machine

/-! Leaf rules -/

namespace H139325

open TM

/-- One round. -/
theorem l_round (b : Nat) (L R : Tape) :
    steps (2 * b + 11) ⟨L, cons true (cons true (rep (b) [true] (cons true (cons true (cons false (cons false (R))))))), .E⟩ = some ⟨cons true (L), cons true (cons true (rep (b) [true] (cons false (cons false (cons true (R)))))), .E⟩ := by
  have hn : 2 + ((b) * 1 + (6 + ((b) * 1 + (3)))) = 2 * b + 11 := by omega
  have h0 : steps 2 ⟨L, cons true (cons true (rep (b) [true] (cons true (cons true (cons false (cons false (R))))))), .E⟩ = some ⟨cons false (cons false (L)), rep (b) [true] (cons true (cons true (cons false (cons false (R))))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .A⟩ = some ⟨app [] (app [true] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((b) * 1) ⟨cons false (cons false (L)), rep (b) [true] (cons true (cons true (cons false (cons false (R))))), .A⟩ = some ⟨rep (b) [true] (cons false (cons false (L))), cons true (cons true (cons false (cons false (R)))), .A⟩ :=
    cross_r trans c1 (b) (cons false (cons false (L))) (cons true (cons true (cons false (cons false (R)))))
  have h2 : steps 6 ⟨rep (b) [true] (cons false (cons false (L))), cons true (cons true (cons false (cons false (R)))), .A⟩ = some ⟨rep (b) [true] (cons false (cons false (L))), cons true (cons false (cons false (cons true (R)))), .B⟩ := rfl
  have c3 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [true] R), .B⟩ := fun _ _ => rfl
  have h3 : steps ((b) * 1) ⟨rep (b) [true] (cons false (cons false (L))), cons true (cons false (cons false (cons true (R)))), .B⟩ = some ⟨cons false (cons false (L)), cons true (rep (b) [true] (cons false (cons false (cons true (R))))), .B⟩ :=
    cross_l trans c3 (b) (cons false (cons false (L))) (cons false (cons false (cons true (R))))
  have h4 : steps 3 ⟨cons false (cons false (L)), cons true (rep (b) [true] (cons false (cons false (cons true (R))))), .B⟩ = some ⟨cons true (L), cons true (cons true (rep (b) [true] (cons false (cons false (cons true (R)))))), .E⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- One round. -/
theorem l_three (L R : Tape) :
    steps (9) ⟨L, cons true (cons true (cons true (cons false (cons false (R))))), .E⟩ = some ⟨cons true (L), cons true (cons false (cons false (cons true (R)))), .E⟩ := by
  have hn : 9 = 9 := by omega
  have h0 : steps 9 ⟨L, cons true (cons true (cons true (cons false (cons false (R))))), .E⟩ = some ⟨cons true (L), cons true (cons false (cons false (cons true (R)))), .E⟩ := rfl
  exact steps_congr trans hn (h0)

/-- two -/
theorem l_two (L R : Tape) :
    steps (10) ⟨L, cons true (cons true (cons false (cons false (R)))), .E⟩ = some ⟨L, cons false (cons true (cons true (cons true (R)))), .B⟩ := by
  have hn : 10 = 10 := by omega
  have h0 : steps 10 ⟨L, cons true (cons true (cons false (cons false (R)))), .E⟩ = some ⟨L, cons false (cons true (cons true (cons true (R)))), .B⟩ := rfl
  exact steps_congr trans hn (h0)

/-- one -/
theorem l_one (L R : Tape) :
    steps (3) ⟨L, cons true (cons false (cons false (R))), .E⟩ = some ⟨cons true (cons true (cons false (L))), R, .E⟩ := by
  have hn : 3 = 3 := by omega
  have h0 : steps 3 ⟨L, cons true (cons false (cons false (R))), .E⟩ = some ⟨cons true (cons true (cons false (L))), R, .E⟩ := rfl
  exact steps_congr trans hn (h0)

/-- sweep -/
theorem l_sw (f : Nat) (L R : Tape) :
    steps (f + 4) ⟨cons true (cons true (cons true (rep (f) [true] (cons false (L))))), cons false (R), .B⟩ = some ⟨L, cons false (cons true (rep (f) [true] (cons false (cons false (cons true (R)))))), .B⟩ := by
  have hn : 3 + ((f) * 1 + (1)) = f + 4 := by omega
  have h0 : steps 3 ⟨cons true (cons true (cons true (rep (f) [true] (cons false (L))))), cons false (R), .B⟩ = some ⟨rep (f) [true] (cons false (L)), cons true (cons false (cons false (cons true (R)))), .B⟩ := rfl
  have c1 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [true] R), .B⟩ := fun _ _ => rfl
  have h1 : steps ((f) * 1) ⟨rep (f) [true] (cons false (L)), cons true (cons false (cons false (cons true (R)))), .B⟩ = some ⟨cons false (L), cons true (rep (f) [true] (cons false (cons false (cons true (R))))), .B⟩ :=
    cross_l trans c1 (f) (cons false (L)) (cons false (cons false (cons true (R))))
  have h2 : steps 1 ⟨cons false (L), cons true (rep (f) [true] (cons false (cons false (cons true (R))))), .B⟩ = some ⟨L, cons false (cons true (rep (f) [true] (cons false (cons false (cons true (R)))))), .B⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- sweep -/
theorem l_sw2 (L R : Tape) :
    steps (3) ⟨cons true (cons true (cons false (L))), cons false (R), .B⟩ = some ⟨L, cons false (cons false (cons false (cons true (R)))), .B⟩ := by
  have hn : 3 = 3 := by omega
  have h0 : steps 3 ⟨cons true (cons true (cons false (L))), cons false (R), .B⟩ = some ⟨L, cons false (cons false (cons false (cons true (R)))), .B⟩ := rfl
  exact steps_congr trans hn (h0)

/-- sweep1 -/
theorem l_sw1 (L R : Tape) :
    steps (6) ⟨cons true (cons false (L)), cons false (R), .B⟩ = some ⟨L, cons true (cons true (cons true (R))), .B⟩ := by
  have hn : 6 = 6 := by omega
  have h0 : steps 6 ⟨cons true (cons false (L)), cons false (R), .B⟩ = some ⟨L, cons true (cons true (cons true (R))), .B⟩ := rfl
  exact steps_congr trans hn (h0)

/-- sweep0 -/
theorem l_sw0 (L R : Tape) :
    steps (2) ⟨cons false (L), cons false (R), .B⟩ = some ⟨cons true (L), cons true (R), .E⟩ := by
  have hn : 2 = 2 := by omega
  have h0 : steps 2 ⟨cons false (L), cons false (R), .B⟩ = some ⟨cons true (L), cons true (R), .E⟩ := rfl
  exact steps_congr trans hn (h0)

end H139325
