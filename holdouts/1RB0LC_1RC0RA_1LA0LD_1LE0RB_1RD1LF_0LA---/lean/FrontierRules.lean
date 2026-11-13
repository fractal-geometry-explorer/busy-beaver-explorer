import Machine

/-! The frontier rules of the left-end phase of 1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---, written by `tools/py/bbtools/symtm.py` and checked by the kernel; see `py/gen_frontier.py` for what they mean. Regenerate with `py/gen_frontier.py`. -/

namespace H14847

open TM

/-- Frontier rule `tuG1`: `L 1 1 0 1 0 A> (01)^a+3 1 R` to `L 1 1 0 1 0 A> 1 1 (01)^a+2 0 R`. -/
theorem tuG1 (a : Nat) (L R : Tape) :
    steps (4 * a + 12) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (a + 3) [false, true] (cons true (R)), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (rep (a + 3) [true, false] (R)), .A⟩ := by
  have hn : (a + 3) * 2 + ((a + 3) * 2) = 4 * a + 12 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((a + 3) * 2) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (a + 3) [false, true] (cons true (R)), .A⟩ = some ⟨rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons true (R), .A⟩ :=
    cross_r trans c0 (a + 3) (cons false (cons true (cons false (cons true (cons true (L)))))) (cons true (R))
  have c1 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h1 : steps ((a + 3) * 2) ⟨rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons true (R), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (rep (a + 3) [true, false] (R)), .A⟩ :=
    cross_l trans c1 (a + 3) (cons false (cons true (cons false (cons true (cons true (L)))))) (R)
  exact steps_congr trans hn (steps_seq trans h0 (h1))

/-- Frontier rule `teG1`: `0^inf A> (01)^a+3 1 R` to `0^inf A> (01)^a+4 0 R`. -/
theorem teG1 (a : Nat) (R : Tape) :
    steps (4 * a + 14) ⟨blank, rep (a + 3) [false, true] (cons true (R)), .A⟩ = some ⟨blank, cons false (cons true (cons false (rep (a + 3) [true, false] (R)))), .A⟩ := by
  have hn : (a + 3) * 2 + ((a + 3) * 2 + (2)) = 4 * a + 14 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((a + 3) * 2) ⟨blank, rep (a + 3) [false, true] (cons true (R)), .A⟩ = some ⟨rep (a + 3) [false, true] (blank), cons true (R), .A⟩ :=
    cross_r trans c0 (a + 3) (blank) (cons true (R))
  have c1 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h1 : steps ((a + 3) * 2) ⟨rep (a + 3) [false, true] (blank), cons true (R), .A⟩ = some ⟨blank, cons true (rep (a + 3) [true, false] (R)), .A⟩ :=
    cross_l trans c1 (a + 3) (blank) (R)
  have h2 : steps 2 ⟨blank, cons true (rep (a + 3) [true, false] (R)), .A⟩ = some ⟨blank, cons false (cons true (cons false (rep (a + 3) [true, false] (R)))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- Frontier rule `tuG2`: `L 1 1 0 1 0 A> (01)^a+3 0 0 1 0 1 R` to `L 1 1 0 1 0 A> 1 1 (01)^a+4 1 R`. -/
theorem tuG2 (a : Nat) (L R : Tape) :
    steps (4 * a + 20) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons true (R)))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (rep (a + 3) [false, true] (cons false (cons true (cons true (R)))))), .A⟩ := by
  have hn : (a + 3) * 2 + (7 + (0 + ((a + 3) * 2 + (1)))) = 4 * a + 20 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((a + 3) * 2) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons true (R)))))), .A⟩ = some ⟨rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (cons false (cons true (cons false (cons true (R))))), .A⟩ :=
    cross_r trans c0 (a + 3) (cons false (cons true (cons false (cons true (cons true (L)))))) (cons false (cons false (cons true (cons false (cons true (R))))))
  have h1 : steps 7 ⟨rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (cons false (cons true (cons false (cons true (R))))), .A⟩ = some ⟨cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons true (R)))), .C⟩ := rfl
  have h2 : steps 0 ⟨cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons true (R)))), .C⟩ = some ⟨rep (a + 3) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons true (R)))), .C⟩ := by
    simp only [steps_zero, show cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L))))))) = rep (a + 3) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (L))))))) from
      rep_rotate (a + 3) [true] [false, true] [true, false] rfl (cons false (cons true (cons false (cons true (cons true (L))))))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [false, true] R), .C⟩ := fun _ _ => rfl
  have h3 : steps ((a + 3) * 2) ⟨rep (a + 3) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons true (R)))), .C⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (rep (a + 3) [false, true] (cons false (cons true (cons true (R))))), .C⟩ :=
    cross_l trans c3 (a + 3) (cons true (cons false (cons true (cons false (cons true (cons true (L))))))) (cons false (cons true (cons true (R))))
  have h4 : steps 1 ⟨cons true (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (rep (a + 3) [false, true] (cons false (cons true (cons true (R))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (rep (a + 3) [false, true] (cons false (cons true (cons true (R)))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- Frontier rule `teG2`: `0^inf A> (01)^a+3 0 0 1 0 1 R` to `0^inf A> (01)^a+6 1 R`. -/
theorem teG2 (a : Nat) (R : Tape) :
    steps (4 * a + 22) ⟨blank, rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons true (R)))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (rep (a + 3) [false, true] (cons false (cons true (cons true (R)))))))), .A⟩ := by
  have hn : (a + 3) * 2 + (7 + (0 + ((a + 3) * 2 + (3)))) = 4 * a + 22 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((a + 3) * 2) ⟨blank, rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons true (R)))))), .A⟩ = some ⟨rep (a + 3) [false, true] (blank), cons false (cons false (cons true (cons false (cons true (R))))), .A⟩ :=
    cross_r trans c0 (a + 3) (blank) (cons false (cons false (cons true (cons false (cons true (R))))))
  have h1 : steps 7 ⟨rep (a + 3) [false, true] (blank), cons false (cons false (cons true (cons false (cons true (R))))), .A⟩ = some ⟨cons true (rep (a + 3) [false, true] (blank)), cons false (cons false (cons true (cons true (R)))), .C⟩ := rfl
  have h2 : steps 0 ⟨cons true (rep (a + 3) [false, true] (blank)), cons false (cons false (cons true (cons true (R)))), .C⟩ = some ⟨rep (a + 3) [true, false] (cons true (blank)), cons false (cons false (cons true (cons true (R)))), .C⟩ := by
    simp only [steps_zero, show cons true (rep (a + 3) [false, true] (blank)) = rep (a + 3) [true, false] (cons true (blank)) from
      rep_rotate (a + 3) [true] [false, true] [true, false] rfl (blank)]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [false, true] R), .C⟩ := fun _ _ => rfl
  have h3 : steps ((a + 3) * 2) ⟨rep (a + 3) [true, false] (cons true (blank)), cons false (cons false (cons true (cons true (R)))), .C⟩ = some ⟨cons true (blank), cons false (rep (a + 3) [false, true] (cons false (cons true (cons true (R))))), .C⟩ :=
    cross_l trans c3 (a + 3) (cons true (blank)) (cons false (cons true (cons true (R))))
  have h4 : steps 3 ⟨cons true (blank), cons false (rep (a + 3) [false, true] (cons false (cons true (cons true (R))))), .C⟩ = some ⟨blank, cons false (cons true (cons false (cons true (rep (a + 3) [false, true] (cons false (cons true (cons true (R)))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- Frontier rule `tuK`: `L 1 1 0 1 0 A> (01)^a+3 0 0 1 0 0 1 R` to `L 1 1 0 1 0 A> 1 1 (01)^a+5 R`. -/
theorem tuK (a : Nat) (L R : Tape) :
    steps (4 * a + 20) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons false (cons true (R))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (R))))))), .A⟩ := by
  have hn : (a + 3) * 2 + (7 + (0 + ((a + 3) * 2 + (1)))) = 4 * a + 20 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((a + 3) * 2) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons false (cons true (R))))))), .A⟩ = some ⟨rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (cons false (cons true (cons false (cons false (cons true (R)))))), .A⟩ :=
    cross_r trans c0 (a + 3) (cons false (cons true (cons false (cons true (cons true (L)))))) (cons false (cons false (cons true (cons false (cons false (cons true (R)))))))
  have h1 : steps 7 ⟨rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (cons false (cons true (cons false (cons false (cons true (R)))))), .A⟩ = some ⟨cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons false (cons true (R))))), .C⟩ := rfl
  have h2 : steps 0 ⟨cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons false (cons true (R))))), .C⟩ = some ⟨rep (a + 3) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons false (cons true (R))))), .C⟩ := by
    simp only [steps_zero, show cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L))))))) = rep (a + 3) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (L))))))) from
      rep_rotate (a + 3) [true] [false, true] [true, false] rfl (cons false (cons true (cons false (cons true (cons true (L))))))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [false, true] R), .C⟩ := fun _ _ => rfl
  have h3 : steps ((a + 3) * 2) ⟨rep (a + 3) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons false (cons true (R))))), .C⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (R)))))), .C⟩ :=
    cross_l trans c3 (a + 3) (cons true (cons false (cons true (cons false (cons true (cons true (L))))))) (cons false (cons true (cons false (cons true (R)))))
  have h4 : steps 1 ⟨cons true (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (R)))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (R))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- Frontier rule `teK`: `0^inf A> (01)^a+3 0 0 1 0 0 1 R` to `0^inf A> (01)^a+7 R`. -/
theorem teK (a : Nat) (R : Tape) :
    steps (4 * a + 22) ⟨blank, rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons false (cons true (R))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (R))))))))), .A⟩ := by
  have hn : (a + 3) * 2 + (7 + (0 + ((a + 3) * 2 + (3)))) = 4 * a + 22 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((a + 3) * 2) ⟨blank, rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons false (cons true (R))))))), .A⟩ = some ⟨rep (a + 3) [false, true] (blank), cons false (cons false (cons true (cons false (cons false (cons true (R)))))), .A⟩ :=
    cross_r trans c0 (a + 3) (blank) (cons false (cons false (cons true (cons false (cons false (cons true (R)))))))
  have h1 : steps 7 ⟨rep (a + 3) [false, true] (blank), cons false (cons false (cons true (cons false (cons false (cons true (R)))))), .A⟩ = some ⟨cons true (rep (a + 3) [false, true] (blank)), cons false (cons false (cons true (cons false (cons true (R))))), .C⟩ := rfl
  have h2 : steps 0 ⟨cons true (rep (a + 3) [false, true] (blank)), cons false (cons false (cons true (cons false (cons true (R))))), .C⟩ = some ⟨rep (a + 3) [true, false] (cons true (blank)), cons false (cons false (cons true (cons false (cons true (R))))), .C⟩ := by
    simp only [steps_zero, show cons true (rep (a + 3) [false, true] (blank)) = rep (a + 3) [true, false] (cons true (blank)) from
      rep_rotate (a + 3) [true] [false, true] [true, false] rfl (blank)]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [false, true] R), .C⟩ := fun _ _ => rfl
  have h3 : steps ((a + 3) * 2) ⟨rep (a + 3) [true, false] (cons true (blank)), cons false (cons false (cons true (cons false (cons true (R))))), .C⟩ = some ⟨cons true (blank), cons false (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (R)))))), .C⟩ :=
    cross_l trans c3 (a + 3) (cons true (blank)) (cons false (cons true (cons false (cons true (R)))))
  have h4 : steps 3 ⟨cons true (blank), cons false (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (R)))))), .C⟩ = some ⟨blank, cons false (cons true (cons false (cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (R))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- Frontier rule `tuH`: `L 1 1 0 1 0 A> (01)^a+3 0 0 0 1 R` to `L 1 1 0 1 0 A> 1 1 (01)^a 0 0 1 1 0 0 1 1 R`. -/
theorem tuH (a : Nat) (L R : Tape) :
    steps (4 * a + 16) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (a + 3) [false, true] (cons false (cons false (cons false (cons true (R))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (rep (a + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R))))))))), .A⟩ := by
  have hn : (a + 3) * 2 + (8 + ((a + 1) * 2)) = 4 * a + 16 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((a + 3) * 2) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (a + 3) [false, true] (cons false (cons false (cons false (cons true (R))))), .A⟩ = some ⟨rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (cons false (cons false (cons true (R)))), .A⟩ :=
    cross_r trans c0 (a + 3) (cons false (cons true (cons false (cons true (cons true (L)))))) (cons false (cons false (cons false (cons true (R)))))
  have h1 : steps 8 ⟨rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (cons false (cons false (cons true (R)))), .A⟩ = some ⟨rep (a + 1) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R)))))))), .A⟩ := rfl
  have c2 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h2 : steps ((a + 1) * 2) ⟨rep (a + 1) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R)))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (rep (a + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R))))))))), .A⟩ :=
    cross_l trans c2 (a + 1) (cons false (cons true (cons false (cons true (cons true (L)))))) (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R))))))))
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- Frontier rule `teH`: `0^inf A> (01)^a+3 0 0 0 1 R` to `0^inf A> (01)^a+2 0 0 1 1 0 0 1 1 R`. -/
theorem teH (a : Nat) (R : Tape) :
    steps (4 * a + 18) ⟨blank, rep (a + 3) [false, true] (cons false (cons false (cons false (cons true (R))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (rep (a + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R))))))))))), .A⟩ := by
  have hn : (a + 3) * 2 + (8 + ((a + 1) * 2 + (2))) = 4 * a + 18 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((a + 3) * 2) ⟨blank, rep (a + 3) [false, true] (cons false (cons false (cons false (cons true (R))))), .A⟩ = some ⟨rep (a + 3) [false, true] (blank), cons false (cons false (cons false (cons true (R)))), .A⟩ :=
    cross_r trans c0 (a + 3) (blank) (cons false (cons false (cons false (cons true (R)))))
  have h1 : steps 8 ⟨rep (a + 3) [false, true] (blank), cons false (cons false (cons false (cons true (R)))), .A⟩ = some ⟨rep (a + 1) [false, true] (blank), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R)))))))), .A⟩ := rfl
  have c2 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h2 : steps ((a + 1) * 2) ⟨rep (a + 1) [false, true] (blank), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R)))))))), .A⟩ = some ⟨blank, cons true (rep (a + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R))))))))), .A⟩ :=
    cross_l trans c2 (a + 1) (blank) (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R))))))))
  have h3 : steps 2 ⟨blank, cons true (rep (a + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R))))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (rep (a + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

/-- Frontier rule `tuX0`: `L 1 1 0 1 0 A> (01)^a+3 0 0 0 0 R` to `L 1 1 0 1 0 A> 1 1 (01)^a 0 0 1 1 0 0 1 0 R`. -/
theorem tuX0 (a : Nat) (L R : Tape) :
    steps (4 * a + 16) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (a + 3) [false, true] (cons false (cons false (cons false (cons false (R))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (rep (a + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R))))))))), .A⟩ := by
  have hn : (a + 3) * 2 + (8 + ((a + 1) * 2)) = 4 * a + 16 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((a + 3) * 2) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (a + 3) [false, true] (cons false (cons false (cons false (cons false (R))))), .A⟩ = some ⟨rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (cons false (cons false (cons false (R)))), .A⟩ :=
    cross_r trans c0 (a + 3) (cons false (cons true (cons false (cons true (cons true (L)))))) (cons false (cons false (cons false (cons false (R)))))
  have h1 : steps 8 ⟨rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (cons false (cons false (cons false (R)))), .A⟩ = some ⟨rep (a + 1) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R)))))))), .A⟩ := rfl
  have c2 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h2 : steps ((a + 1) * 2) ⟨rep (a + 1) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R)))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (rep (a + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R))))))))), .A⟩ :=
    cross_l trans c2 (a + 1) (cons false (cons true (cons false (cons true (cons true (L)))))) (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R))))))))
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- Frontier rule `teX0`: `0^inf A> (01)^a+3 0 0 0 0 R` to `0^inf A> (01)^a+2 0 0 1 1 0 0 1 0 R`. -/
theorem teX0 (a : Nat) (R : Tape) :
    steps (4 * a + 18) ⟨blank, rep (a + 3) [false, true] (cons false (cons false (cons false (cons false (R))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (rep (a + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R))))))))))), .A⟩ := by
  have hn : (a + 3) * 2 + (8 + ((a + 1) * 2 + (2))) = 4 * a + 18 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((a + 3) * 2) ⟨blank, rep (a + 3) [false, true] (cons false (cons false (cons false (cons false (R))))), .A⟩ = some ⟨rep (a + 3) [false, true] (blank), cons false (cons false (cons false (cons false (R)))), .A⟩ :=
    cross_r trans c0 (a + 3) (blank) (cons false (cons false (cons false (cons false (R)))))
  have h1 : steps 8 ⟨rep (a + 3) [false, true] (blank), cons false (cons false (cons false (cons false (R)))), .A⟩ = some ⟨rep (a + 1) [false, true] (blank), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R)))))))), .A⟩ := rfl
  have c2 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h2 : steps ((a + 1) * 2) ⟨rep (a + 1) [false, true] (blank), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R)))))))), .A⟩ = some ⟨blank, cons true (rep (a + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R))))))))), .A⟩ :=
    cross_l trans c2 (a + 1) (blank) (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R))))))))
  have h3 : steps 2 ⟨blank, cons true (rep (a + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R))))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (rep (a + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

/-- Frontier rule `tuX1`: `L 1 1 0 1 0 A> (01)^a+3 0 0 1 0 0 0 R` to `L 1 1 0 1 0 A> 1 1 (01)^a+4 0 0 R`. -/
theorem tuX1 (a : Nat) (L R : Tape) :
    steps (4 * a + 20) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons false (cons false (R))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons false (R))))))), .A⟩ := by
  have hn : (a + 3) * 2 + (7 + (0 + ((a + 3) * 2 + (1)))) = 4 * a + 20 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((a + 3) * 2) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons false (cons false (R))))))), .A⟩ = some ⟨rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (cons false (cons true (cons false (cons false (cons false (R)))))), .A⟩ :=
    cross_r trans c0 (a + 3) (cons false (cons true (cons false (cons true (cons true (L)))))) (cons false (cons false (cons true (cons false (cons false (cons false (R)))))))
  have h1 : steps 7 ⟨rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (cons false (cons true (cons false (cons false (cons false (R)))))), .A⟩ = some ⟨cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons false (cons false (R))))), .C⟩ := rfl
  have h2 : steps 0 ⟨cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons false (cons false (R))))), .C⟩ = some ⟨rep (a + 3) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons false (cons false (R))))), .C⟩ := by
    simp only [steps_zero, show cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons true (cons true (L))))))) = rep (a + 3) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (L))))))) from
      rep_rotate (a + 3) [true] [false, true] [true, false] rfl (cons false (cons true (cons false (cons true (cons true (L))))))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [false, true] R), .C⟩ := fun _ _ => rfl
  have h3 : steps ((a + 3) * 2) ⟨rep (a + 3) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons false (cons false (R))))), .C⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (rep (a + 3) [false, true] (cons false (cons true (cons false (cons false (R)))))), .C⟩ :=
    cross_l trans c3 (a + 3) (cons true (cons false (cons true (cons false (cons true (cons true (L))))))) (cons false (cons true (cons false (cons false (R)))))
  have h4 : steps 1 ⟨cons true (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (rep (a + 3) [false, true] (cons false (cons true (cons false (cons false (R)))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons false (R))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- Frontier rule `teX1`: `0^inf A> (01)^a+3 0 0 1 0 0 0 R` to `0^inf A> (01)^a+6 0 0 R`. -/
theorem teX1 (a : Nat) (R : Tape) :
    steps (4 * a + 22) ⟨blank, rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons false (cons false (R))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons false (R))))))))), .A⟩ := by
  have hn : (a + 3) * 2 + (7 + (0 + ((a + 3) * 2 + (3)))) = 4 * a + 22 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((a + 3) * 2) ⟨blank, rep (a + 3) [false, true] (cons false (cons false (cons true (cons false (cons false (cons false (R))))))), .A⟩ = some ⟨rep (a + 3) [false, true] (blank), cons false (cons false (cons true (cons false (cons false (cons false (R)))))), .A⟩ :=
    cross_r trans c0 (a + 3) (blank) (cons false (cons false (cons true (cons false (cons false (cons false (R)))))))
  have h1 : steps 7 ⟨rep (a + 3) [false, true] (blank), cons false (cons false (cons true (cons false (cons false (cons false (R)))))), .A⟩ = some ⟨cons true (rep (a + 3) [false, true] (blank)), cons false (cons false (cons true (cons false (cons false (R))))), .C⟩ := rfl
  have h2 : steps 0 ⟨cons true (rep (a + 3) [false, true] (blank)), cons false (cons false (cons true (cons false (cons false (R))))), .C⟩ = some ⟨rep (a + 3) [true, false] (cons true (blank)), cons false (cons false (cons true (cons false (cons false (R))))), .C⟩ := by
    simp only [steps_zero, show cons true (rep (a + 3) [false, true] (blank)) = rep (a + 3) [true, false] (cons true (blank)) from
      rep_rotate (a + 3) [true] [false, true] [true, false] rfl (blank)]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [false, true] R), .C⟩ := fun _ _ => rfl
  have h3 : steps ((a + 3) * 2) ⟨rep (a + 3) [true, false] (cons true (blank)), cons false (cons false (cons true (cons false (cons false (R))))), .C⟩ = some ⟨cons true (blank), cons false (rep (a + 3) [false, true] (cons false (cons true (cons false (cons false (R)))))), .C⟩ :=
    cross_l trans c3 (a + 3) (cons true (blank)) (cons false (cons true (cons false (cons false (R)))))
  have h4 : steps 3 ⟨cons true (blank), cons false (rep (a + 3) [false, true] (cons false (cons true (cons false (cons false (R)))))), .C⟩ = some ⟨blank, cons false (cons true (cons false (cons true (rep (a + 3) [false, true] (cons false (cons true (cons false (cons false (R))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- Frontier rule `seG10`: `0^inf A> 1 R` to `0^inf A> 0 1 0 R`. -/
theorem seG10 (R : Tape) :
    steps (2) ⟨blank, cons true (R), .A⟩ = some ⟨blank, cons false (cons true (cons false (R))), .A⟩ := by
  have hn : 2 = 2 := by omega
  have h0 : steps 2 ⟨blank, cons true (R), .A⟩ = some ⟨blank, cons false (cons true (cons false (R))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `suG11`: `L 1 1 0 1 0 A> 0 1 1 R` to `L 1 1 0 1 0 A> 1 1 0 R`. -/
theorem suG11 (L R : Tape) :
    steps (4) ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons true (R))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (R))), .A⟩ := by
  have hn : 4 = 4 := by omega
  have h0 : steps 4 ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons true (R))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (R))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seG11`: `0^inf A> 0 1 1 R` to `0^inf A> 0 1 0 1 0 R`. -/
theorem seG11 (R : Tape) :
    steps (6) ⟨blank, cons false (cons true (cons true (R))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (R))))), .A⟩ := by
  have hn : 6 = 6 := by omega
  have h0 : steps 6 ⟨blank, cons false (cons true (cons true (R))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (R))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `suG12`: `L 1 1 0 1 0 A> 0 1 0 1 1 R` to `L 1 1 0 1 0 A> 1 1 0 1 0 R`. -/
theorem suG12 (L R : Tape) :
    steps (8) ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons false (cons true (cons true (R))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (R))))), .A⟩ := by
  have hn : 8 = 8 := by omega
  have h0 : steps 8 ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons false (cons true (cons true (R))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (R))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seG12`: `0^inf A> 0 1 0 1 1 R` to `0^inf A> 0 1 0 1 0 1 0 R`. -/
theorem seG12 (R : Tape) :
    steps (10) ⟨blank, cons false (cons true (cons false (cons true (cons true (R))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))), .A⟩ := by
  have hn : 10 = 10 := by omega
  have h0 : steps 10 ⟨blank, cons false (cons true (cons false (cons true (cons true (R))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `suG20`: `L 1 1 0 1 0 A> 0 0 1 0 1 R` to `L 1 1 0 1 0 A> 1 1 0 1 1 R`. -/
theorem suG20 (L R : Tape) :
    steps (8) ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons false (cons true (cons false (cons true (R))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons true (R))))), .A⟩ := by
  have hn : 8 = 8 := by omega
  have h0 : steps 8 ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons false (cons true (cons false (cons true (R))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons true (R))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seG20`: `0^inf A> 0 0 1 0 1 R` to `0^inf A> 0 1 0 1 0 1 1 R`. -/
theorem seG20 (R : Tape) :
    steps (10) ⟨blank, cons false (cons false (cons true (cons false (cons true (R))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons true (R))))))), .A⟩ := by
  have hn : 10 = 10 := by omega
  have h0 : steps 10 ⟨blank, cons false (cons false (cons true (cons false (cons true (R))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons true (R))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `suG21`: `L 1 1 0 1 0 A> 0 1 0 0 1 0 1 R` to `L 1 1 0 1 0 A> 1 1 0 1 0 1 1 R`. -/
theorem suG21 (L R : Tape) :
    steps (12) ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons false (cons false (cons true (cons false (cons true (R))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons true (cons true (R))))))), .A⟩ := by
  have hn : 12 = 12 := by omega
  have h0 : steps 12 ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons false (cons false (cons true (cons false (cons true (R))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons true (cons true (R))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seG21`: `0^inf A> 0 1 0 0 1 0 1 R` to `0^inf A> 0 1 0 1 0 1 0 1 1 R`. -/
theorem seG21 (R : Tape) :
    steps (14) ⟨blank, cons false (cons true (cons false (cons false (cons true (cons false (cons true (R))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (R))))))))), .A⟩ := by
  have hn : 14 = 14 := by omega
  have h0 : steps 14 ⟨blank, cons false (cons true (cons false (cons false (cons true (cons false (cons true (R))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (R))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `suG22`: `L 1 1 0 1 0 A> 0 1 0 1 0 0 1 0 1 R` to `L 1 1 0 1 0 A> 1 1 0 1 0 1 0 1 1 R`. -/
theorem suG22 (L R : Tape) :
    steps (16) ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons true (R))))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (R))))))))), .A⟩ := by
  have hn : 16 = 16 := by omega
  have h0 : steps 16 ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons true (R))))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (R))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seG22`: `0^inf A> 0 1 0 1 0 0 1 0 1 R` to `0^inf A> 0 1 0 1 0 1 0 1 0 1 1 R`. -/
theorem seG22 (R : Tape) :
    steps (18) ⟨blank, cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons true (R))))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (R))))))))))), .A⟩ := by
  have hn : 18 = 18 := by omega
  have h0 : steps 18 ⟨blank, cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons true (R))))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (R))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `suK0`: `L 1 1 0 1 0 A> 0 0 1 0 0 1 R` to `L 1 1 0 1 0 A> 1 1 0 1 0 1 R`. -/
theorem suK0 (L R : Tape) :
    steps (8) ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons false (cons true (cons false (cons false (cons true (R)))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons true (R)))))), .A⟩ := by
  have hn : 8 = 8 := by omega
  have h0 : steps 8 ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons false (cons true (cons false (cons false (cons true (R)))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons true (R)))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seK0`: `0^inf A> 0 0 1 0 0 1 R` to `0^inf A> 0 1 0 1 0 1 0 1 R`. -/
theorem seK0 (R : Tape) :
    steps (10) ⟨blank, cons false (cons false (cons true (cons false (cons false (cons true (R)))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))), .A⟩ := by
  have hn : 10 = 10 := by omega
  have h0 : steps 10 ⟨blank, cons false (cons false (cons true (cons false (cons false (cons true (R)))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `suK1`: `L 1 1 0 1 0 A> 0 1 0 0 1 0 0 1 R` to `L 1 1 0 1 0 A> 1 1 0 1 0 1 0 1 R`. -/
theorem suK1 (L R : Tape) :
    steps (12) ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons true (R)))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))), .A⟩ := by
  have hn : 12 = 12 := by omega
  have h0 : steps 12 ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons true (R)))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seK1`: `0^inf A> 0 1 0 0 1 0 0 1 R` to `0^inf A> 0 1 0 1 0 1 0 1 0 1 R`. -/
theorem seK1 (R : Tape) :
    steps (14) ⟨blank, cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons true (R)))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))))), .A⟩ := by
  have hn : 14 = 14 := by omega
  have h0 : steps 14 ⟨blank, cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons true (R)))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `suK2`: `L 1 1 0 1 0 A> 0 1 0 1 0 0 1 0 0 1 R` to `L 1 1 0 1 0 A> 1 1 0 1 0 1 0 1 0 1 R`. -/
theorem suK2 (L R : Tape) :
    steps (16) ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons true (R)))))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))))), .A⟩ := by
  have hn : 16 = 16 := by omega
  have h0 : steps 16 ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons true (R)))))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seK2`: `0^inf A> 0 1 0 1 0 0 1 0 0 1 R` to `0^inf A> 0 1 0 1 0 1 0 1 0 1 0 1 R`. -/
theorem seK2 (R : Tape) :
    steps (18) ⟨blank, cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons true (R)))))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))))))), .A⟩ := by
  have hn : 18 = 18 := by omega
  have h0 : steps 18 ⟨blank, cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons true (R)))))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (R)))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seH0`: `0^inf A> 0 0 0 1 R` to `0^inf A> 0 1 0 1 0 1 1 1 R`. -/
theorem seH0 (R : Tape) :
    steps (14) ⟨blank, cons false (cons false (cons false (cons true (R)))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons true (R)))))))), .A⟩ := by
  have hn : 14 = 14 := by omega
  have h0 : steps 14 ⟨blank, cons false (cons false (cons false (cons true (R)))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons true (R)))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seH1`: `0^inf A> 0 1 0 0 0 1 R` to `0^inf A> 0 0 1 1 0 0 1 1 R`. -/
theorem seH1 (R : Tape) :
    steps (10) ⟨blank, cons false (cons true (cons false (cons false (cons false (cons true (R)))))), .A⟩ = some ⟨blank, cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R)))))))), .A⟩ := by
  have hn : 10 = 10 := by omega
  have h0 : steps 10 ⟨blank, cons false (cons true (cons false (cons false (cons false (cons true (R)))))), .A⟩ = some ⟨blank, cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R)))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seH2`: `0^inf A> 0 1 0 1 0 0 0 1 R` to `0^inf A> 0 1 0 0 1 1 0 0 1 1 R`. -/
theorem seH2 (R : Tape) :
    steps (14) ⟨blank, cons false (cons true (cons false (cons true (cons false (cons false (cons false (cons true (R)))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R)))))))))), .A⟩ := by
  have hn : 14 = 14 := by omega
  have h0 : steps 14 ⟨blank, cons false (cons true (cons false (cons true (cons false (cons false (cons false (cons true (R)))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (R)))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seX00`: `0^inf A> 0 0 0 0 R` to `0^inf A> 0 1 0 1 0 1 1 0 R`. -/
theorem seX00 (R : Tape) :
    steps (14) ⟨blank, cons false (cons false (cons false (cons false (R)))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (R)))))))), .A⟩ := by
  have hn : 14 = 14 := by omega
  have h0 : steps 14 ⟨blank, cons false (cons false (cons false (cons false (R)))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (R)))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seX01`: `0^inf A> 0 1 0 0 0 0 R` to `0^inf A> 0 0 1 1 0 0 1 0 R`. -/
theorem seX01 (R : Tape) :
    steps (10) ⟨blank, cons false (cons true (cons false (cons false (cons false (cons false (R)))))), .A⟩ = some ⟨blank, cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R)))))))), .A⟩ := by
  have hn : 10 = 10 := by omega
  have h0 : steps 10 ⟨blank, cons false (cons true (cons false (cons false (cons false (cons false (R)))))), .A⟩ = some ⟨blank, cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R)))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seX02`: `0^inf A> 0 1 0 1 0 0 0 0 R` to `0^inf A> 0 1 0 0 1 1 0 0 1 0 R`. -/
theorem seX02 (R : Tape) :
    steps (14) ⟨blank, cons false (cons true (cons false (cons true (cons false (cons false (cons false (cons false (R)))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R)))))))))), .A⟩ := by
  have hn : 14 = 14 := by omega
  have h0 : steps 14 ⟨blank, cons false (cons true (cons false (cons true (cons false (cons false (cons false (cons false (R)))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (R)))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `suX10`: `L 1 1 0 1 0 A> 0 0 1 0 0 0 R` to `L 1 1 0 1 0 A> 1 1 0 1 0 0 R`. -/
theorem suX10 (L R : Tape) :
    steps (8) ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons false (cons true (cons false (cons false (cons false (R)))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons false (R)))))), .A⟩ := by
  have hn : 8 = 8 := by omega
  have h0 : steps 8 ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons false (cons true (cons false (cons false (cons false (R)))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons false (R)))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seX10`: `0^inf A> 0 0 1 0 0 0 R` to `0^inf A> 0 1 0 1 0 1 0 0 R`. -/
theorem seX10 (R : Tape) :
    steps (10) ⟨blank, cons false (cons false (cons true (cons false (cons false (cons false (R)))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))), .A⟩ := by
  have hn : 10 = 10 := by omega
  have h0 : steps 10 ⟨blank, cons false (cons false (cons true (cons false (cons false (cons false (R)))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `suX11`: `L 1 1 0 1 0 A> 0 1 0 0 1 0 0 0 R` to `L 1 1 0 1 0 A> 1 1 0 1 0 1 0 0 R`. -/
theorem suX11 (L R : Tape) :
    steps (12) ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (R)))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))), .A⟩ := by
  have hn : 12 = 12 := by omega
  have h0 : steps 12 ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (R)))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seX11`: `0^inf A> 0 1 0 0 1 0 0 0 R` to `0^inf A> 0 1 0 1 0 1 0 1 0 0 R`. -/
theorem seX11 (R : Tape) :
    steps (14) ⟨blank, cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (R)))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))))), .A⟩ := by
  have hn : 14 = 14 := by omega
  have h0 : steps 14 ⟨blank, cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (R)))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `suX12`: `L 1 1 0 1 0 A> 0 1 0 1 0 0 1 0 0 0 R` to `L 1 1 0 1 0 A> 1 1 0 1 0 1 0 1 0 0 R`. -/
theorem suX12 (L R : Tape) :
    steps (16) ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (R)))))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))))), .A⟩ := by
  have hn : 16 = 16 := by omega
  have h0 : steps 16 ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (R)))))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Frontier rule `seX12`: `0^inf A> 0 1 0 1 0 0 1 0 0 0 R` to `0^inf A> 0 1 0 1 0 1 0 1 0 1 0 0 R`. -/
theorem seX12 (R : Tape) :
    steps (18) ⟨blank, cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (R)))))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))))))), .A⟩ := by
  have hn : 18 = 18 := by omega
  have h0 : steps 18 ⟨blank, cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons false (R)))))))))), .A⟩ = some ⟨blank, cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (R)))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

end H14847
