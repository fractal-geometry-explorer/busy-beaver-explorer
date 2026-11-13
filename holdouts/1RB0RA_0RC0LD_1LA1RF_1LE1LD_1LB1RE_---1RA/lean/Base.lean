import Machine

/-! The five basic rules of the recursion, written by `bbtools.symtm.prove`. -/

namespace H48098

open TM

theorem ruleP (c i : Nat) (L R : Tape) :
    steps (2 * i + 11) ⟨L, cons false (rep (2 * i + 5) [true] (cons false (rep (c + 1) [true] (R)))), .B⟩ = some ⟨rep (2 * i) [false] (cons true (cons true (cons false (L)))), cons false (cons true (cons true (cons true (cons false (rep (c) [true] (R)))))), .B⟩ := by
  have h0 : steps 3 ⟨L, cons false (rep (2 * i + 5) [true] (cons false (rep (c + 1) [true] (R)))), .B⟩ = some ⟨cons true (cons true (cons false (L))), rep (2 * i + 3) [true] (cons false (rep (c + 1) [true] (R))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .A⟩ = some ⟨app [] (app [false] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((2 * i + 3) * 1) ⟨cons true (cons true (cons false (L))), rep (2 * i + 3) [true] (cons false (rep (c + 1) [true] (R))), .A⟩ = some ⟨rep (2 * i + 3) [false] (cons true (cons true (cons false (L)))), cons false (rep (c + 1) [true] (R)), .A⟩ :=
    cross_r trans c1 (2 * i + 3) (cons true (cons true (cons false (L)))) (cons false (rep (c + 1) [true] (R)))
  have h2 : steps 5 ⟨rep (2 * i + 3) [false] (cons true (cons true (cons false (L)))), cons false (rep (c + 1) [true] (R)), .A⟩ = some ⟨rep (2 * i) [false] (cons true (cons true (cons false (L)))), cons false (cons true (cons true (cons true (cons false (rep (c) [true] (R)))))), .B⟩ := rfl
  exact steps_congr trans (a := 3 + ((2 * i + 3) * 1 + (5))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

theorem ruleM1 (c : Nat) (L R : Tape) :
    steps (18) ⟨cons false (cons false (L)), cons false (rep (3) [true] (cons false (rep (c + 1) [true] (R)))), .B⟩ = some ⟨L, cons false (cons true (cons true (cons true (cons true (cons true (cons false (cons true (rep (c) [true] (R))))))))), .B⟩ := by
  have h0 : steps 3 ⟨cons false (cons false (L)), cons false (rep (3) [true] (cons false (rep (c + 1) [true] (R)))), .B⟩ = some ⟨cons true (cons true (cons false (cons false (cons false (L))))), rep (1) [true] (cons false (rep (c + 1) [true] (R))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .A⟩ = some ⟨app [] (app [false] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((1) * 1) ⟨cons true (cons true (cons false (cons false (cons false (L))))), rep (1) [true] (cons false (rep (c + 1) [true] (R))), .A⟩ = some ⟨rep (1) [false] (cons true (cons true (cons false (cons false (cons false (L)))))), cons false (rep (c + 1) [true] (R)), .A⟩ :=
    cross_r trans c1 (1) (cons true (cons true (cons false (cons false (cons false (L)))))) (cons false (rep (c + 1) [true] (R)))
  have h2 : steps 14 ⟨rep (1) [false] (cons true (cons true (cons false (cons false (cons false (L)))))), cons false (rep (c + 1) [true] (R)), .A⟩ = some ⟨L, cons false (cons true (cons true (cons true (cons true (cons true (cons false (cons true (rep (c) [true] (R))))))))), .B⟩ := rfl
  exact steps_congr trans (a := 3 + ((1) * 1 + (14))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

theorem ruleX0 (c : Nat) (L R : Tape) :
    steps (11) ⟨cons true (cons true (cons false (L))), cons false (rep (3) [true] (cons false (rep (c + 1) [true] (R)))), .B⟩ = some ⟨cons true (cons true (cons true (cons true (cons false (cons true (cons true (cons false (L)))))))), cons false (rep (c) [true] (R)), .E⟩ := by
  have h0 : steps 3 ⟨cons true (cons true (cons false (L))), cons false (rep (3) [true] (cons false (rep (c + 1) [true] (R)))), .B⟩ = some ⟨cons true (cons true (cons false (cons true (cons true (cons false (L)))))), rep (1) [true] (cons false (rep (c + 1) [true] (R))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .A⟩ = some ⟨app [] (app [false] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((1) * 1) ⟨cons true (cons true (cons false (cons true (cons true (cons false (L)))))), rep (1) [true] (cons false (rep (c + 1) [true] (R))), .A⟩ = some ⟨rep (1) [false] (cons true (cons true (cons false (cons true (cons true (cons false (L))))))), cons false (rep (c + 1) [true] (R)), .A⟩ :=
    cross_r trans c1 (1) (cons true (cons true (cons false (cons true (cons true (cons false (L))))))) (cons false (rep (c + 1) [true] (R)))
  have h2 : steps 7 ⟨rep (1) [false] (cons true (cons true (cons false (cons true (cons true (cons false (L))))))), cons false (rep (c + 1) [true] (R)), .A⟩ = some ⟨cons true (cons true (cons true (cons true (cons false (cons true (cons true (cons false (L)))))))), cons false (rep (c) [true] (R)), .E⟩ := rfl
  exact steps_congr trans (a := 3 + ((1) * 1 + (7))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

theorem ruleY (c s : Nat) (L R : Tape) :
    steps (4 * s + 7) ⟨rep (2 * s + 2) [true] (cons false (cons true (cons true (cons false (L))))), cons false (rep (c) [true] (R)), .E⟩ = some ⟨rep (2 * s) [true] (cons true (cons true (cons true (cons true (cons false (L)))))), cons false (cons true (rep (c) [true] (R))), .E⟩ := by
  have h0 : steps 2 ⟨rep (2 * s + 2) [true] (cons false (cons true (cons true (cons false (L))))), cons false (rep (c) [true] (R)), .E⟩ = some ⟨rep (2 * s) [true] (cons false (cons true (cons true (cons false (L))))), cons true (cons false (cons true (rep (c) [true] (R)))), .D⟩ := rfl
  have c1 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [true] R), .D⟩ := fun _ _ => rfl
  have h1 : steps ((2 * s) * 1) ⟨rep (2 * s) [true] (cons false (cons true (cons true (cons false (L))))), cons true (cons false (cons true (rep (c) [true] (R)))), .D⟩ = some ⟨cons false (cons true (cons true (cons false (L)))), cons true (rep (2 * s) [true] (cons false (cons true (rep (c) [true] (R))))), .D⟩ :=
    cross_l trans c1 (2 * s) (cons false (cons true (cons true (cons false (L))))) (cons false (cons true (rep (c) [true] (R))))
  have h2 : steps 5 ⟨cons false (cons true (cons true (cons false (L)))), cons true (rep (2 * s) [true] (cons false (cons true (rep (c) [true] (R))))), .D⟩ = some ⟨cons true (cons true (cons true (cons true (cons false (L))))), rep (2 * s) [true] (cons false (cons true (rep (c) [true] (R)))), .E⟩ := rfl
  have c3 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .E⟩ = some ⟨app [] (app [true] L), R, .E⟩ := fun _ _ => rfl
  have h3 : steps ((2 * s) * 1) ⟨cons true (cons true (cons true (cons true (cons false (L))))), rep (2 * s) [true] (cons false (cons true (rep (c) [true] (R)))), .E⟩ = some ⟨rep (2 * s) [true] (cons true (cons true (cons true (cons true (cons false (L)))))), cons false (cons true (rep (c) [true] (R))), .E⟩ :=
    cross_r trans c3 (2 * s) (cons true (cons true (cons true (cons true (cons false (L)))))) (cons false (cons true (rep (c) [true] (R))))
  exact steps_congr trans (a := 2 + ((2 * s) * 1 + (5 + ((2 * s) * 1)))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

theorem ruleZ (c s : Nat) (L R : Tape) :
    steps (2 * s + 5) ⟨rep (2 * s + 2) [true] (cons false (cons false (cons false (L)))), cons false (rep (c) [true] (R)), .E⟩ = some ⟨L, cons false (cons true (cons true (cons true (rep (2 * s) [true] (cons false (cons true (rep (c) [true] (R)))))))), .B⟩ := by
  have h0 : steps 2 ⟨rep (2 * s + 2) [true] (cons false (cons false (cons false (L)))), cons false (rep (c) [true] (R)), .E⟩ = some ⟨rep (2 * s) [true] (cons false (cons false (cons false (L)))), cons true (cons false (cons true (rep (c) [true] (R)))), .D⟩ := rfl
  have c1 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [true] R), .D⟩ := fun _ _ => rfl
  have h1 : steps ((2 * s) * 1) ⟨rep (2 * s) [true] (cons false (cons false (cons false (L)))), cons true (cons false (cons true (rep (c) [true] (R)))), .D⟩ = some ⟨cons false (cons false (cons false (L))), cons true (rep (2 * s) [true] (cons false (cons true (rep (c) [true] (R))))), .D⟩ :=
    cross_l trans c1 (2 * s) (cons false (cons false (cons false (L)))) (cons false (cons true (rep (c) [true] (R))))
  have h2 : steps 3 ⟨cons false (cons false (cons false (L))), cons true (rep (2 * s) [true] (cons false (cons true (rep (c) [true] (R))))), .D⟩ = some ⟨L, cons false (cons true (cons true (cons true (rep (2 * s) [true] (cons false (cons true (rep (c) [true] (R)))))))), .B⟩ := rfl
  exact steps_congr trans (a := 2 + ((2 * s) * 1 + (3))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (h2)))

end H48098
