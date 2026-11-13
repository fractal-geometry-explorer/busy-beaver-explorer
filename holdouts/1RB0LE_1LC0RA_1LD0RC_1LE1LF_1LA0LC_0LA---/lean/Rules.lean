import Machine

/-! Cell-level pieces of a sweep of 1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---, written by `py/gen_rules.py` with `bbtools.symtm.prove`. -/

namespace H122192

open TM

/-- `0^inf A> 1 (10)^n+1 0 1 1 0 0 R` reaches `0^inf 1 0 (10)^n 1 1 0 1 0 1 0 1 B> R`. -/
theorem start_s (n : Nat) (R : Tape) :
    steps (2 * n + 28) ⟨blank, cons true (rep (n + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (R))))))), .A⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (rep (n) [false, true] (cons false (cons true (blank))))))))))), R, .B⟩ := by
  have hn : 4 + (0 + ((n + 1) * 2 + (22))) = 2 * n + 28 := by omega
  have h0 : steps 4 ⟨blank, cons true (rep (n + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (R))))))), .A⟩ = some ⟨cons false (cons true (blank)), cons false (rep (n + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (R))))))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (blank)), cons false (rep (n + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (R))))))), .A⟩ = some ⟨cons false (cons true (blank)), rep (n + 1) [false, true] (cons false (cons false (cons true (cons true (cons false (cons false (R))))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (n + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (R))))))) = rep (n + 1) [false, true] (cons false (cons false (cons true (cons true (cons false (cons false (R))))))) from
      rep_rotate (n + 1) [false] [true, false] [false, true] rfl (cons false (cons true (cons true (cons false (cons false (R))))))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((n + 1) * 2) ⟨cons false (cons true (blank)), rep (n + 1) [false, true] (cons false (cons false (cons true (cons true (cons false (cons false (R))))))), .A⟩ = some ⟨rep (n + 1) [false, true] (cons false (cons true (blank))), cons false (cons false (cons true (cons true (cons false (cons false (R)))))), .A⟩ :=
    cross_r trans c2 (n + 1) (cons false (cons true (blank))) (cons false (cons false (cons true (cons true (cons false (cons false (R)))))))
  have h3 : steps 22 ⟨rep (n + 1) [false, true] (cons false (cons true (blank))), cons false (cons false (cons true (cons true (cons false (cons false (R)))))), .A⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (rep (n) [false, true] (cons false (cons true (blank))))))))))), R, .B⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

/-- `0^inf A> 1 0 1 1 0 0 R` reaches `0^inf 1 1 0 1 0 1 0 1 B> R`. -/
theorem start_z (R : Tape) :
    steps (26) ⟨blank, cons true (cons false (cons true (cons true (cons false (cons false (R)))))), .A⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (blank)))))))), R, .B⟩ := by
  have hn : 26 = 26 := by omega
  have h0 : steps 26 ⟨blank, cons true (cons false (cons true (cons true (cons false (cons false (R)))))), .A⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (blank)))))))), R, .B⟩ := rfl
  exact steps_congr trans hn (h0)

/-- `L B> (10)^v+1 0 1 1 0 0 R` reaches `L (01)^v 1 0 1 0 1 0 1 B> R`. -/
theorem rb (v : Nat) (L R : Tape) :
    steps (2 * v + 23) ⟨L, rep (v + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (R)))))), .B⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (cons false (cons true (rep (v) [true, false] (L)))))))), R, .B⟩ := by
  have hn : (v + 1) * 2 + (21) = 2 * v + 23 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((v + 1) * 2) ⟨L, rep (v + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (R)))))), .B⟩ = some ⟨rep (v + 1) [true, false] (L), cons false (cons true (cons true (cons false (cons false (R))))), .B⟩ :=
    cross_r trans c0 (v + 1) (L) (cons false (cons true (cons true (cons false (cons false (R))))))
  have h1 : steps 21 ⟨rep (v + 1) [true, false] (L), cons false (cons true (cons true (cons false (cons false (R))))), .B⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (cons false (cons true (rep (v) [true, false] (L)))))))), R, .B⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (h1))

/-- `L 1 (01)^v+3 1 0 1 0 1 0 A> 1 R` reaches `L A> 1 1 0 (10)^v 0 1 1 0 0 1 0 1 0 1 0 R`. -/
theorem lbA (v : Nat) (L R : Tape) :
    steps (2 * v + 13) ⟨cons false (cons true (cons false (cons true (cons false (cons true (rep (v + 3) [true, false] (cons true (L)))))))), cons true (R), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (v) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))))))))))), .A⟩ := by
  have hn : 11 + (0 + ((v) * 2 + (2))) = 2 * v + 13 := by omega
  have h0 : steps 11 ⟨cons false (cons true (cons false (cons true (cons false (cons true (rep (v + 3) [true, false] (cons true (L)))))))), cons true (R), .A⟩ = some ⟨cons false (rep (v) [true, false] (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R)))))))))))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (rep (v) [true, false] (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R)))))))))))), .A⟩ = some ⟨rep (v) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R)))))))))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (v) [true, false] (cons true (L))) = rep (v) [false, true] (cons false (cons true (L))) from
      rep_rotate (v) [false] [true, false] [false, true] rfl (cons true (L))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h2 : steps ((v) * 2) ⟨rep (v) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R)))))))))))), .A⟩ = some ⟨cons false (cons true (L)), cons true (rep (v) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))))))))), .A⟩ :=
    cross_l trans c2 (v) (cons false (cons true (L))) (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))))))))
  have h3 : steps 2 ⟨cons false (cons true (L)), cons true (rep (v) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))))))))), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (v) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

/-- `L 1 (01)^v+3 1 0 1 0 1 0 D> 1 R` reaches `L A> 1 1 0 (10)^v 0 1 1 0 0 1 0 1 0 0 1 R`. -/
theorem lbD (v : Nat) (L R : Tape) :
    steps (2 * v + 13) ⟨cons false (cons true (cons false (cons true (cons false (cons true (rep (v + 3) [true, false] (cons true (L)))))))), cons true (R), .D⟩ = some ⟨L, cons true (cons true (cons false (rep (v) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R))))))))))))))), .A⟩ := by
  have hn : 11 + (0 + ((v) * 2 + (2))) = 2 * v + 13 := by omega
  have h0 : steps 11 ⟨cons false (cons true (cons false (cons true (cons false (cons true (rep (v + 3) [true, false] (cons true (L)))))))), cons true (R), .D⟩ = some ⟨cons false (rep (v) [true, false] (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R)))))))))))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (rep (v) [true, false] (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R)))))))))))), .A⟩ = some ⟨rep (v) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R)))))))))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (v) [true, false] (cons true (L))) = rep (v) [false, true] (cons false (cons true (L))) from
      rep_rotate (v) [false] [true, false] [false, true] rfl (cons true (L))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h2 : steps ((v) * 2) ⟨rep (v) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R)))))))))))), .A⟩ = some ⟨cons false (cons true (L)), cons true (rep (v) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R))))))))))))), .A⟩ :=
    cross_l trans c2 (v) (cons false (cons true (L))) (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R))))))))))))
  have h3 : steps 2 ⟨cons false (cons true (L)), cons true (rep (v) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R))))))))))))), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (v) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R))))))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

/-- `L 1 0 1 0 1 1 0 1 0 1 0 A> 1 R` reaches `L A> 1 0 1 1 0 0 1 0 1 0 1 0 R`. -/
theorem lb3A (L R : Tape) :
    steps (11) ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons false (cons true (L))))))))))), cons true (R), .A⟩ = some ⟨L, cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R)))))))))))), .A⟩ := by
  have hn : 11 = 11 := by omega
  have h0 : steps 11 ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons false (cons true (L))))))))))), cons true (R), .A⟩ = some ⟨L, cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R)))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- `L 1 0 1 0 1 1 0 1 0 1 0 D> 1 R` reaches `L A> 1 0 1 1 0 0 1 0 1 0 0 1 R`. -/
theorem lb3D (L R : Tape) :
    steps (11) ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons false (cons true (L))))))))))), cons true (R), .D⟩ = some ⟨L, cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R)))))))))))), .A⟩ := by
  have hn : 11 = 11 := by omega
  have h0 : steps 11 ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons false (cons true (L))))))))))), cons true (R), .D⟩ = some ⟨L, cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R)))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- `L 1 0 1 1 0 1 0 1 0 A> 1 R` reaches `L D> 1 1 0 0 1 0 1 0 1 0 R`. -/
theorem lb2A (L R : Tape) :
    steps (9) ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons true (L))))))))), cons true (R), .A⟩ = some ⟨L, cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R)))))))))), .D⟩ := by
  have hn : 9 = 9 := by omega
  have h0 : steps 9 ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons true (L))))))))), cons true (R), .A⟩ = some ⟨L, cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R)))))))))), .D⟩ := rfl
  exact steps_congr trans hn (h0)

/-- `L 1 0 1 1 0 1 0 1 0 D> 1 R` reaches `L D> 1 1 0 0 1 0 1 0 0 1 R`. -/
theorem lb2D (L R : Tape) :
    steps (9) ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons true (L))))))))), cons true (R), .D⟩ = some ⟨L, cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R)))))))))), .D⟩ := by
  have hn : 9 = 9 := by omega
  have h0 : steps 9 ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons true (L))))))))), cons true (R), .D⟩ = some ⟨L, cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R)))))))))), .D⟩ := rfl
  exact steps_congr trans hn (h0)

/-- `0^inf 1 0 (10)^n+2 1 1 0 1 0 1 0 A> 1 R` reaches `0^inf A> 1 1 0 (10)^n 0 1 1 0 0 1 0 1 0 1 0 R`. -/
theorem endA_s (n : Nat) (R : Tape) :
    steps (2 * n + 13) ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (rep (n + 2) [false, true] (cons false (cons true (blank)))))))))), cons true (R), .A⟩ = some ⟨blank, cons true (cons true (cons false (rep (n) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))))))))))), .A⟩ := by
  have hn : 11 + ((n) * 2 + (2)) = 2 * n + 13 := by omega
  have h0 : steps 11 ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (rep (n + 2) [false, true] (cons false (cons true (blank)))))))))), cons true (R), .A⟩ = some ⟨rep (n) [false, true] (cons false (cons true (blank))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R)))))))))))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h1 : steps ((n) * 2) ⟨rep (n) [false, true] (cons false (cons true (blank))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R)))))))))))), .A⟩ = some ⟨cons false (cons true (blank)), cons true (rep (n) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))))))))), .A⟩ :=
    cross_l trans c1 (n) (cons false (cons true (blank))) (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))))))))
  have h2 : steps 2 ⟨cons false (cons true (blank)), cons true (rep (n) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))))))))), .A⟩ = some ⟨blank, cons true (cons true (cons false (rep (n) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R))))))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- `0^inf 1 0 (10)^n+2 1 1 0 1 0 1 0 D> 1 R` reaches `0^inf A> 1 1 0 (10)^n 0 1 1 0 0 1 0 1 0 0 1 R`. -/
theorem endD_s (n : Nat) (R : Tape) :
    steps (2 * n + 13) ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (rep (n + 2) [false, true] (cons false (cons true (blank)))))))))), cons true (R), .D⟩ = some ⟨blank, cons true (cons true (cons false (rep (n) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R))))))))))))))), .A⟩ := by
  have hn : 11 + ((n) * 2 + (2)) = 2 * n + 13 := by omega
  have h0 : steps 11 ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (rep (n + 2) [false, true] (cons false (cons true (blank)))))))))), cons true (R), .D⟩ = some ⟨rep (n) [false, true] (cons false (cons true (blank))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R)))))))))))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h1 : steps ((n) * 2) ⟨rep (n) [false, true] (cons false (cons true (blank))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R)))))))))))), .A⟩ = some ⟨cons false (cons true (blank)), cons true (rep (n) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R))))))))))))), .A⟩ :=
    cross_l trans c1 (n) (cons false (cons true (blank))) (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R))))))))))))
  have h2 : steps 2 ⟨cons false (cons true (blank)), cons true (rep (n) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R))))))))))))), .A⟩ = some ⟨blank, cons true (cons true (cons false (rep (n) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R))))))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- `0^inf 1 0 1 0 1 1 0 1 0 1 0 A> 1 R` reaches `0^inf A> 1 0 1 1 0 0 1 0 1 0 1 0 R`. -/
theorem endA_2 (R : Tape) :
    steps (11) ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons false (cons true (blank))))))))))), cons true (R), .A⟩ = some ⟨blank, cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R)))))))))))), .A⟩ := by
  have hn : 11 = 11 := by omega
  have h0 : steps 11 ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons false (cons true (blank))))))))))), cons true (R), .A⟩ = some ⟨blank, cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R)))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- `0^inf 1 0 1 0 1 1 0 1 0 1 0 D> 1 R` reaches `0^inf A> 1 0 1 1 0 0 1 0 1 0 0 1 R`. -/
theorem endD_2 (R : Tape) :
    steps (11) ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons false (cons true (blank))))))))))), cons true (R), .D⟩ = some ⟨blank, cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R)))))))))))), .A⟩ := by
  have hn : 11 = 11 := by omega
  have h0 : steps 11 ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons true (cons false (cons true (blank))))))))))), cons true (R), .D⟩ = some ⟨blank, cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R)))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- `0^inf 1 1 0 1 0 1 0 A> 1 R` reaches `0^inf A> 1 1 0 1 0 0 1 0 1 0 1 0 R`. -/
theorem endA_0 (R : Tape) :
    steps (15) ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (blank))))))), cons true (R), .A⟩ = some ⟨blank, cons true (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R)))))))))))), .A⟩ := by
  have hn : 15 = 15 := by omega
  have h0 : steps 15 ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (blank))))))), cons true (R), .A⟩ = some ⟨blank, cons true (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (R)))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- `0^inf 1 1 0 1 0 1 0 D> 1 R` reaches `0^inf A> 1 1 0 1 0 0 1 0 1 0 0 1 R`. -/
theorem endD_0 (R : Tape) :
    steps (15) ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (blank))))))), cons true (R), .D⟩ = some ⟨blank, cons true (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R)))))))))))), .A⟩ := by
  have hn : 15 = 15 := by omega
  have h0 : steps 15 ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons true (blank))))))), cons true (R), .D⟩ = some ⟨blank, cons true (cons true (cons false (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (R)))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- `L 1 B> (10)^x+1 0 (10)^m+2 R` reaches `L A> 1 1 0 (10)^x 1 0 1 (10)^m+1 R`. -/
theorem w_pair_dot (m x : Nat) (L R : Tape) :
    steps (4 * x + 15) ⟨cons true (L), rep (x + 1) [true, false] (cons false (rep (m + 2) [true, false] (R))), .B⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons true (cons false (cons true (rep (m + 1) [true, false] (R)))))))), .A⟩ := by
  have hn : (x + 1) * 2 + (11 + (0 + ((x) * 2 + (2)))) = 4 * x + 15 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((x + 1) * 2) ⟨cons true (L), rep (x + 1) [true, false] (cons false (rep (m + 2) [true, false] (R))), .B⟩ = some ⟨rep (x + 1) [true, false] (cons true (L)), cons false (rep (m + 2) [true, false] (R)), .B⟩ :=
    cross_r trans c0 (x + 1) (cons true (L)) (cons false (rep (m + 2) [true, false] (R)))
  have h1 : steps 11 ⟨rep (x + 1) [true, false] (cons true (L)), cons false (rep (m + 2) [true, false] (R)), .B⟩ = some ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons true (cons false (cons true (rep (m + 1) [true, false] (R))))), .A⟩ := rfl
  have h2 : steps 0 ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons true (cons false (cons true (rep (m + 1) [true, false] (R))))), .A⟩ = some ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons true (cons false (cons true (rep (m + 1) [true, false] (R))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (x) [true, false] (cons true (L))) = rep (x) [false, true] (cons false (cons true (L))) from
      rep_rotate (x) [false] [true, false] [false, true] rfl (cons true (L))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h3 : steps ((x) * 2) ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons true (cons false (cons true (rep (m + 1) [true, false] (R))))), .A⟩ = some ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons true (cons false (cons true (rep (m + 1) [true, false] (R)))))), .A⟩ :=
    cross_l trans c3 (x) (cons false (cons true (L))) (cons true (cons false (cons true (rep (m + 1) [true, false] (R)))))
  have h4 : steps 2 ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons true (cons false (cons true (rep (m + 1) [true, false] (R)))))), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons true (cons false (cons true (rep (m + 1) [true, false] (R)))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- `L 1 B> (10)^x+1 1 (10)^m+2 R` reaches `L A> 1 1 (01)^x+1 0 0 (10)^m+1 R`. -/
theorem w_pair_bang (m x : Nat) (L R : Tape) :
    steps (4 * x + 7) ⟨cons true (L), rep (x + 1) [true, false] (cons true (rep (m + 2) [true, false] (R))), .B⟩ = some ⟨L, cons true (cons true (rep (x + 1) [false, true] (cons false (cons false (rep (m + 1) [true, false] (R)))))), .A⟩ := by
  have hn : (x + 1) * 2 + (2 + ((x + 1) * 2 + (1))) = 4 * x + 7 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((x + 1) * 2) ⟨cons true (L), rep (x + 1) [true, false] (cons true (rep (m + 2) [true, false] (R))), .B⟩ = some ⟨rep (x + 1) [true, false] (cons true (L)), cons true (rep (m + 2) [true, false] (R)), .B⟩ :=
    cross_r trans c0 (x + 1) (cons true (L)) (cons true (rep (m + 2) [true, false] (R)))
  have h1 : steps 2 ⟨rep (x + 1) [true, false] (cons true (L)), cons true (rep (m + 2) [true, false] (R)), .B⟩ = some ⟨rep (x + 1) [true, false] (cons true (L)), cons false (cons false (cons false (rep (m + 1) [true, false] (R)))), .E⟩ := rfl
  have c2 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [false, true] R), .E⟩ := fun _ _ => rfl
  have h2 : steps ((x + 1) * 2) ⟨rep (x + 1) [true, false] (cons true (L)), cons false (cons false (cons false (rep (m + 1) [true, false] (R)))), .E⟩ = some ⟨cons true (L), cons false (rep (x + 1) [false, true] (cons false (cons false (rep (m + 1) [true, false] (R))))), .E⟩ :=
    cross_l trans c2 (x + 1) (cons true (L)) (cons false (cons false (rep (m + 1) [true, false] (R))))
  have h3 : steps 1 ⟨cons true (L), cons false (rep (x + 1) [false, true] (cons false (cons false (rep (m + 1) [true, false] (R))))), .E⟩ = some ⟨L, cons true (cons true (rep (x + 1) [false, true] (cons false (cons false (rep (m + 1) [true, false] (R)))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

/-- `L 1 B> (10)^x+4 0 1 1 0 0 1 0 1 0^inf` reaches `L A> 1 1 0 (10)^x 0 1 1 0 0 1 0 1 0 0 1 1 0 0 1 0 1 0^inf`. -/
theorem w_append (x : Nat) (L : Tape) :
    steps (4 * x + 59) ⟨cons true (L), rep (x + 4) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank))))))))), .B⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank))))))))))))))))))))), .A⟩ := by
  have hn : (x + 4) * 2 + (30 + (19 + (0 + ((x) * 2 + (2))))) = 4 * x + 59 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((x + 4) * 2) ⟨cons true (L), rep (x + 4) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank))))))))), .B⟩ = some ⟨rep (x + 4) [true, false] (cons true (L)), cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank)))))))), .B⟩ :=
    cross_r trans c0 (x + 4) (cons true (L)) (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank)))))))))
  have h1 : steps 30 ⟨rep (x + 4) [true, false] (cons true (L)), cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank)))))))), .B⟩ = some ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (rep (x + 3) [true, false] (cons true (L)))))))))))), cons false (cons true (cons true (blank))), .E⟩ := rfl
  have h2 : steps 19 ⟨cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (rep (x + 3) [true, false] (cons true (L)))))))))))), cons false (cons true (cons true (blank))), .E⟩ = some ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank)))))))))))))))))), .A⟩ := rfl
  have h3 : steps 0 ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank)))))))))))))))))), .A⟩ = some ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank)))))))))))))))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (x) [true, false] (cons true (L))) = rep (x) [false, true] (cons false (cons true (L))) from
      rep_rotate (x) [false] [true, false] [false, true] rfl (cons true (L))]
  have c4 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h4 : steps ((x) * 2) ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank)))))))))))))))))), .A⟩ = some ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank))))))))))))))))))), .A⟩ :=
    cross_l trans c4 (x) (cons false (cons true (L))) (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank))))))))))))))))))
  have h5 : steps 2 ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank))))))))))))))))))), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank))))))))))))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (h5))))))

/-- `L 1 B> (10)^x+1 1 1 0 0 R` reaches `L A> 1 1 0 (10)^x+1 0 0 R`. -/
theorem w_p1_bd (x : Nat) (L R : Tape) :
    steps (4 * x + 7) ⟨cons true (L), rep (x + 1) [true, false] (cons true (cons true (cons false (cons false (R))))), .B⟩ = some ⟨L, cons true (cons true (cons false (rep (x + 1) [true, false] (cons false (cons false (R)))))), .A⟩ := by
  have hn : (x + 1) * 2 + (1 + (0 + ((x + 1) * 2 + (2)))) = 4 * x + 7 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((x + 1) * 2) ⟨cons true (L), rep (x + 1) [true, false] (cons true (cons true (cons false (cons false (R))))), .B⟩ = some ⟨rep (x + 1) [true, false] (cons true (L)), cons true (cons true (cons false (cons false (R)))), .B⟩ :=
    cross_r trans c0 (x + 1) (cons true (L)) (cons true (cons true (cons false (cons false (R)))))
  have h1 : steps 1 ⟨rep (x + 1) [true, false] (cons true (L)), cons true (cons true (cons false (cons false (R)))), .B⟩ = some ⟨cons false (rep (x + 1) [true, false] (cons true (L))), cons true (cons false (cons false (R))), .A⟩ := rfl
  have h2 : steps 0 ⟨cons false (rep (x + 1) [true, false] (cons true (L))), cons true (cons false (cons false (R))), .A⟩ = some ⟨rep (x + 1) [false, true] (cons false (cons true (L))), cons true (cons false (cons false (R))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (x + 1) [true, false] (cons true (L))) = rep (x + 1) [false, true] (cons false (cons true (L))) from
      rep_rotate (x + 1) [false] [true, false] [false, true] rfl (cons true (L))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h3 : steps ((x + 1) * 2) ⟨rep (x + 1) [false, true] (cons false (cons true (L))), cons true (cons false (cons false (R))), .A⟩ = some ⟨cons false (cons true (L)), cons true (rep (x + 1) [true, false] (cons false (cons false (R)))), .A⟩ :=
    cross_l trans c3 (x + 1) (cons false (cons true (L))) (cons false (cons false (R)))
  have h4 : steps 2 ⟨cons false (cons true (L)), cons true (rep (x + 1) [true, false] (cons false (cons false (R)))), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (x + 1) [true, false] (cons false (cons false (R)))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- `L 1 B> (10)^x+1 1 1 0 1 R` reaches `L A> 1 1 0 (10)^x+1 0 1 R`. -/
theorem w_p1_bb (x : Nat) (L R : Tape) :
    steps (4 * x + 7) ⟨cons true (L), rep (x + 1) [true, false] (cons true (cons true (cons false (cons true (R))))), .B⟩ = some ⟨L, cons true (cons true (cons false (rep (x + 1) [true, false] (cons false (cons true (R)))))), .A⟩ := by
  have hn : (x + 1) * 2 + (1 + (0 + ((x + 1) * 2 + (2)))) = 4 * x + 7 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((x + 1) * 2) ⟨cons true (L), rep (x + 1) [true, false] (cons true (cons true (cons false (cons true (R))))), .B⟩ = some ⟨rep (x + 1) [true, false] (cons true (L)), cons true (cons true (cons false (cons true (R)))), .B⟩ :=
    cross_r trans c0 (x + 1) (cons true (L)) (cons true (cons true (cons false (cons true (R)))))
  have h1 : steps 1 ⟨rep (x + 1) [true, false] (cons true (L)), cons true (cons true (cons false (cons true (R)))), .B⟩ = some ⟨cons false (rep (x + 1) [true, false] (cons true (L))), cons true (cons false (cons true (R))), .A⟩ := rfl
  have h2 : steps 0 ⟨cons false (rep (x + 1) [true, false] (cons true (L))), cons true (cons false (cons true (R))), .A⟩ = some ⟨rep (x + 1) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (R))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (x + 1) [true, false] (cons true (L))) = rep (x + 1) [false, true] (cons false (cons true (L))) from
      rep_rotate (x + 1) [false] [true, false] [false, true] rfl (cons true (L))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h3 : steps ((x + 1) * 2) ⟨rep (x + 1) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (R))), .A⟩ = some ⟨cons false (cons true (L)), cons true (rep (x + 1) [true, false] (cons false (cons true (R)))), .A⟩ :=
    cross_l trans c3 (x + 1) (cons false (cons true (L))) (cons false (cons true (R)))
  have h4 : steps 2 ⟨cons false (cons true (L)), cons true (rep (x + 1) [true, false] (cons false (cons true (R)))), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (x + 1) [true, false] (cons false (cons true (R)))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- `L 1 B> (10)^x+1 0 1 0 1 R` reaches `L A> 1 1 0 (10)^x 1 0 1 1 R`. -/
theorem w_p1_db (x : Nat) (L R : Tape) :
    steps (4 * x + 15) ⟨cons true (L), rep (x + 1) [true, false] (cons false (cons true (cons false (cons true (R))))), .B⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons true (cons false (cons true (cons true (R)))))))), .A⟩ := by
  have hn : (x + 1) * 2 + (11 + (0 + ((x) * 2 + (2)))) = 4 * x + 15 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((x + 1) * 2) ⟨cons true (L), rep (x + 1) [true, false] (cons false (cons true (cons false (cons true (R))))), .B⟩ = some ⟨rep (x + 1) [true, false] (cons true (L)), cons false (cons true (cons false (cons true (R)))), .B⟩ :=
    cross_r trans c0 (x + 1) (cons true (L)) (cons false (cons true (cons false (cons true (R)))))
  have h1 : steps 11 ⟨rep (x + 1) [true, false] (cons true (L)), cons false (cons true (cons false (cons true (R)))), .B⟩ = some ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons true (cons false (cons true (cons true (R))))), .A⟩ := rfl
  have h2 : steps 0 ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons true (cons false (cons true (cons true (R))))), .A⟩ = some ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons true (cons false (cons true (cons true (R))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (x) [true, false] (cons true (L))) = rep (x) [false, true] (cons false (cons true (L))) from
      rep_rotate (x) [false] [true, false] [false, true] rfl (cons true (L))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h3 : steps ((x) * 2) ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons true (cons false (cons true (cons true (R))))), .A⟩ = some ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons true (cons false (cons true (cons true (R)))))), .A⟩ :=
    cross_l trans c3 (x) (cons false (cons true (L))) (cons true (cons false (cons true (cons true (R)))))
  have h4 : steps 2 ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons true (cons false (cons true (cons true (R)))))), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons true (cons false (cons true (cons true (R)))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- `L 1 B> (10)^x+1 0 1 0 0 (10)^z 0 R` reaches `L A> 1 1 0 (10)^x 1 0 1 0 (10)^z 0 R`. -/
theorem w_p1_dd0 (x z : Nat) (L R : Tape) :
    steps (4 * x + 15) ⟨cons true (L), rep (x + 1) [true, false] (cons false (cons true (cons false (cons false (rep (z) [true, false] (cons false (R))))))), .B⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons false (R)))))))))), .A⟩ := by
  have hn : (x + 1) * 2 + (11 + (0 + ((x) * 2 + (2)))) = 4 * x + 15 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((x + 1) * 2) ⟨cons true (L), rep (x + 1) [true, false] (cons false (cons true (cons false (cons false (rep (z) [true, false] (cons false (R))))))), .B⟩ = some ⟨rep (x + 1) [true, false] (cons true (L)), cons false (cons true (cons false (cons false (rep (z) [true, false] (cons false (R)))))), .B⟩ :=
    cross_r trans c0 (x + 1) (cons true (L)) (cons false (cons true (cons false (cons false (rep (z) [true, false] (cons false (R)))))))
  have h1 : steps 11 ⟨rep (x + 1) [true, false] (cons true (L)), cons false (cons true (cons false (cons false (rep (z) [true, false] (cons false (R)))))), .B⟩ = some ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons false (R))))))), .A⟩ := rfl
  have h2 : steps 0 ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons false (R))))))), .A⟩ = some ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons false (R))))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (x) [true, false] (cons true (L))) = rep (x) [false, true] (cons false (cons true (L))) from
      rep_rotate (x) [false] [true, false] [false, true] rfl (cons true (L))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h3 : steps ((x) * 2) ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons false (R))))))), .A⟩ = some ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons false (R)))))))), .A⟩ :=
    cross_l trans c3 (x) (cons false (cons true (L))) (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons false (R)))))))
  have h4 : steps 2 ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons false (R)))))))), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons false (R)))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- `L 1 B> (10)^x+1 0 1 0 0 (10)^z 1 R` reaches `L A> 1 1 0 (10)^x 1 0 1 0 (10)^z 1 R`. -/
theorem w_p1_dd1 (x z : Nat) (L R : Tape) :
    steps (4 * x + 15) ⟨cons true (L), rep (x + 1) [true, false] (cons false (cons true (cons false (cons false (rep (z) [true, false] (cons true (R))))))), .B⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons true (R)))))))))), .A⟩ := by
  have hn : (x + 1) * 2 + (11 + (0 + ((x) * 2 + (2)))) = 4 * x + 15 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((x + 1) * 2) ⟨cons true (L), rep (x + 1) [true, false] (cons false (cons true (cons false (cons false (rep (z) [true, false] (cons true (R))))))), .B⟩ = some ⟨rep (x + 1) [true, false] (cons true (L)), cons false (cons true (cons false (cons false (rep (z) [true, false] (cons true (R)))))), .B⟩ :=
    cross_r trans c0 (x + 1) (cons true (L)) (cons false (cons true (cons false (cons false (rep (z) [true, false] (cons true (R)))))))
  have h1 : steps 11 ⟨rep (x + 1) [true, false] (cons true (L)), cons false (cons true (cons false (cons false (rep (z) [true, false] (cons true (R)))))), .B⟩ = some ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons true (R))))))), .A⟩ := rfl
  have h2 : steps 0 ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons true (R))))))), .A⟩ = some ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons true (R))))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (x) [true, false] (cons true (L))) = rep (x) [false, true] (cons false (cons true (L))) from
      rep_rotate (x) [false] [true, false] [false, true] rfl (cons true (L))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h3 : steps ((x) * 2) ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons true (R))))))), .A⟩ = some ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons true (R)))))))), .A⟩ :=
    cross_l trans c3 (x) (cons false (cons true (L))) (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons true (R)))))))
  have h4 : steps 2 ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons true (R)))))))), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons true (cons false (cons true (cons false (rep (z) [true, false] (cons true (R)))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- `L 1 B> (10)^x+1 1 1 (10)^z 0 R` reaches `L A> 1 1 0 (10)^x+1 (10)^z 0 R`. -/
theorem w_merge (x z : Nat) (L R : Tape) :
    steps (4 * x + 7) ⟨cons true (L), rep (x + 1) [true, false] (cons true (cons true (rep (z) [true, false] (cons false (R))))), .B⟩ = some ⟨L, cons true (cons true (cons false (rep (x + 1) [true, false] (rep (z) [true, false] (cons false (R)))))), .A⟩ := by
  have hn : (x + 1) * 2 + (1 + (0 + ((x + 1) * 2 + (2)))) = 4 * x + 7 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((x + 1) * 2) ⟨cons true (L), rep (x + 1) [true, false] (cons true (cons true (rep (z) [true, false] (cons false (R))))), .B⟩ = some ⟨rep (x + 1) [true, false] (cons true (L)), cons true (cons true (rep (z) [true, false] (cons false (R)))), .B⟩ :=
    cross_r trans c0 (x + 1) (cons true (L)) (cons true (cons true (rep (z) [true, false] (cons false (R)))))
  have h1 : steps 1 ⟨rep (x + 1) [true, false] (cons true (L)), cons true (cons true (rep (z) [true, false] (cons false (R)))), .B⟩ = some ⟨cons false (rep (x + 1) [true, false] (cons true (L))), cons true (rep (z) [true, false] (cons false (R))), .A⟩ := rfl
  have h2 : steps 0 ⟨cons false (rep (x + 1) [true, false] (cons true (L))), cons true (rep (z) [true, false] (cons false (R))), .A⟩ = some ⟨rep (x + 1) [false, true] (cons false (cons true (L))), cons true (rep (z) [true, false] (cons false (R))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (x + 1) [true, false] (cons true (L))) = rep (x + 1) [false, true] (cons false (cons true (L))) from
      rep_rotate (x + 1) [false] [true, false] [false, true] rfl (cons true (L))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h3 : steps ((x + 1) * 2) ⟨rep (x + 1) [false, true] (cons false (cons true (L))), cons true (rep (z) [true, false] (cons false (R))), .A⟩ = some ⟨cons false (cons true (L)), cons true (rep (x + 1) [true, false] (rep (z) [true, false] (cons false (R)))), .A⟩ :=
    cross_l trans c3 (x + 1) (cons false (cons true (L))) (rep (z) [true, false] (cons false (R)))
  have h4 : steps 2 ⟨cons false (cons true (L)), cons true (rep (x + 1) [true, false] (rep (z) [true, false] (cons false (R)))), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (x + 1) [true, false] (rep (z) [true, false] (cons false (R)))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- `L 1 B> (10)^x+1 0 1 0^inf` reaches `L A> 1 1 0 (10)^x 1 0 1 0^inf`. -/
theorem w_end_db (x : Nat) (L : Tape) :
    steps (4 * x + 15) ⟨cons true (L), rep (x + 1) [true, false] (cons false (cons true (blank))), .B⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons true (cons false (cons true (blank))))))), .A⟩ := by
  have hn : (x + 1) * 2 + (11 + (0 + ((x) * 2 + (2)))) = 4 * x + 15 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((x + 1) * 2) ⟨cons true (L), rep (x + 1) [true, false] (cons false (cons true (blank))), .B⟩ = some ⟨rep (x + 1) [true, false] (cons true (L)), cons false (cons true (blank)), .B⟩ :=
    cross_r trans c0 (x + 1) (cons true (L)) (cons false (cons true (blank)))
  have h1 : steps 11 ⟨rep (x + 1) [true, false] (cons true (L)), cons false (cons true (blank)), .B⟩ = some ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons true (cons false (cons true (blank)))), .A⟩ := rfl
  have h2 : steps 0 ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons true (cons false (cons true (blank)))), .A⟩ = some ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons true (cons false (cons true (blank)))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (x) [true, false] (cons true (L))) = rep (x) [false, true] (cons false (cons true (L))) from
      rep_rotate (x) [false] [true, false] [false, true] rfl (cons true (L))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h3 : steps ((x) * 2) ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons true (cons false (cons true (blank)))), .A⟩ = some ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons true (cons false (cons true (blank))))), .A⟩ :=
    cross_l trans c3 (x) (cons false (cons true (L))) (cons true (cons false (cons true (blank))))
  have h4 : steps 2 ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons true (cons false (cons true (blank))))), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons true (cons false (cons true (blank))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- `L 1 B> (10)^x+4 0 0 (10)^z 0 R` reaches `L A> 1 1 0 (10)^x 0 1 1 0 0 1 0 1 (10)^z 0 R`. -/
theorem w_next0 (x z : Nat) (L R : Tape) :
    steps (4 * x + 25) ⟨cons true (L), rep (x + 4) [true, false] (cons false (cons false (rep (z) [true, false] (cons false (R))))), .B⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons false (R)))))))))))))), .A⟩ := by
  have hn : (x + 4) * 2 + (15 + (0 + ((x) * 2 + (2)))) = 4 * x + 25 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((x + 4) * 2) ⟨cons true (L), rep (x + 4) [true, false] (cons false (cons false (rep (z) [true, false] (cons false (R))))), .B⟩ = some ⟨rep (x + 4) [true, false] (cons true (L)), cons false (cons false (rep (z) [true, false] (cons false (R)))), .B⟩ :=
    cross_r trans c0 (x + 4) (cons true (L)) (cons false (cons false (rep (z) [true, false] (cons false (R)))))
  have h1 : steps 15 ⟨rep (x + 4) [true, false] (cons true (L)), cons false (cons false (rep (z) [true, false] (cons false (R)))), .B⟩ = some ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons false (R))))))))))), .A⟩ := rfl
  have h2 : steps 0 ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons false (R))))))))))), .A⟩ = some ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons false (R))))))))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (x) [true, false] (cons true (L))) = rep (x) [false, true] (cons false (cons true (L))) from
      rep_rotate (x) [false] [true, false] [false, true] rfl (cons true (L))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h3 : steps ((x) * 2) ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons false (R))))))))))), .A⟩ = some ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons false (R)))))))))))), .A⟩ :=
    cross_l trans c3 (x) (cons false (cons true (L))) (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons false (R)))))))))))
  have h4 : steps 2 ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons false (R)))))))))))), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons false (R)))))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- `L 1 B> (10)^x+4 0 0 (10)^z 1 R` reaches `L A> 1 1 0 (10)^x 0 1 1 0 0 1 0 1 (10)^z 1 R`. -/
theorem w_next1 (x z : Nat) (L R : Tape) :
    steps (4 * x + 25) ⟨cons true (L), rep (x + 4) [true, false] (cons false (cons false (rep (z) [true, false] (cons true (R))))), .B⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons true (R)))))))))))))), .A⟩ := by
  have hn : (x + 4) * 2 + (15 + (0 + ((x) * 2 + (2)))) = 4 * x + 25 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((x + 4) * 2) ⟨cons true (L), rep (x + 4) [true, false] (cons false (cons false (rep (z) [true, false] (cons true (R))))), .B⟩ = some ⟨rep (x + 4) [true, false] (cons true (L)), cons false (cons false (rep (z) [true, false] (cons true (R)))), .B⟩ :=
    cross_r trans c0 (x + 4) (cons true (L)) (cons false (cons false (rep (z) [true, false] (cons true (R)))))
  have h1 : steps 15 ⟨rep (x + 4) [true, false] (cons true (L)), cons false (cons false (rep (z) [true, false] (cons true (R)))), .B⟩ = some ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons true (R))))))))))), .A⟩ := rfl
  have h2 : steps 0 ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons true (R))))))))))), .A⟩ = some ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons true (R))))))))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (x) [true, false] (cons true (L))) = rep (x) [false, true] (cons false (cons true (L))) from
      rep_rotate (x) [false] [true, false] [false, true] rfl (cons true (L))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h3 : steps ((x) * 2) ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons true (R))))))))))), .A⟩ = some ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons true (R)))))))))))), .A⟩ :=
    cross_l trans c3 (x) (cons false (cons true (L))) (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons true (R)))))))))))
  have h4 : steps 2 ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons true (R)))))))))))), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (rep (z) [true, false] (cons true (R)))))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- `L 1 B> (10)^x+4 1 0^inf` reaches `L A> 1 1 0 (10)^x+1 0 1 1 0 0 1 0 1 0^inf`. -/
theorem w_end_b (x : Nat) (L : Tape) :
    steps (4 * x + 29) ⟨cons true (L), rep (x + 4) [true, false] (cons true (blank)), .B⟩ = some ⟨L, cons true (cons true (cons false (rep (x + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank)))))))))))), .A⟩ := by
  have hn : (x + 4) * 2 + (17 + (0 + ((x + 1) * 2 + (2)))) = 4 * x + 29 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((x + 4) * 2) ⟨cons true (L), rep (x + 4) [true, false] (cons true (blank)), .B⟩ = some ⟨rep (x + 4) [true, false] (cons true (L)), cons true (blank), .B⟩ :=
    cross_r trans c0 (x + 4) (cons true (L)) (cons true (blank))
  have h1 : steps 17 ⟨rep (x + 4) [true, false] (cons true (L)), cons true (blank), .B⟩ = some ⟨cons false (rep (x + 1) [true, false] (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank))))))))), .A⟩ := rfl
  have h2 : steps 0 ⟨cons false (rep (x + 1) [true, false] (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank))))))))), .A⟩ = some ⟨rep (x + 1) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank))))))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (x + 1) [true, false] (cons true (L))) = rep (x + 1) [false, true] (cons false (cons true (L))) from
      rep_rotate (x + 1) [false] [true, false] [false, true] rfl (cons true (L))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h3 : steps ((x + 1) * 2) ⟨rep (x + 1) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank))))))))), .A⟩ = some ⟨cons false (cons true (L)), cons true (rep (x + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank)))))))))), .A⟩ :=
    cross_l trans c3 (x + 1) (cons false (cons true (L))) (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank)))))))))
  have h4 : steps 2 ⟨cons false (cons true (L)), cons true (rep (x + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank)))))))))), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (x + 1) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (blank)))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- `L 1 B> (10)^x+4 0 0 0 1 1 0 0 R` reaches `L A> 1 1 0 (10)^x 0 1 1 0 0 1 0 1 0 1 1 0 0 R`. -/
theorem w_restart2 (x : Nat) (L R : Tape) :
    steps (4 * x + 25) ⟨cons true (L), rep (x + 4) [true, false] (cons false (cons false (cons false (cons true (cons true (cons false (cons false (R)))))))), .B⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons false (R))))))))))))))))), .A⟩ := by
  have hn : (x + 4) * 2 + (15 + (0 + ((x) * 2 + (2)))) = 4 * x + 25 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((x + 4) * 2) ⟨cons true (L), rep (x + 4) [true, false] (cons false (cons false (cons false (cons true (cons true (cons false (cons false (R)))))))), .B⟩ = some ⟨rep (x + 4) [true, false] (cons true (L)), cons false (cons false (cons false (cons true (cons true (cons false (cons false (R))))))), .B⟩ :=
    cross_r trans c0 (x + 4) (cons true (L)) (cons false (cons false (cons false (cons true (cons true (cons false (cons false (R))))))))
  have h1 : steps 15 ⟨rep (x + 4) [true, false] (cons true (L)), cons false (cons false (cons false (cons true (cons true (cons false (cons false (R))))))), .B⟩ = some ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons false (R)))))))))))))), .A⟩ := rfl
  have h2 : steps 0 ⟨cons false (rep (x) [true, false] (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons false (R)))))))))))))), .A⟩ = some ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons false (R)))))))))))))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (x) [true, false] (cons true (L))) = rep (x) [false, true] (cons false (cons true (L))) from
      rep_rotate (x) [false] [true, false] [false, true] rfl (cons true (L))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h3 : steps ((x) * 2) ⟨rep (x) [false, true] (cons false (cons true (L))), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons false (R)))))))))))))), .A⟩ = some ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons false (R))))))))))))))), .A⟩ :=
    cross_l trans c3 (x) (cons false (cons true (L))) (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons false (R))))))))))))))
  have h4 : steps 2 ⟨cons false (cons true (L)), cons true (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons false (R))))))))))))))), .A⟩ = some ⟨L, cons true (cons true (cons false (rep (x) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons false (R))))))))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- `0^inf A> 1 (10)^x 0 (10)^y+2 R` reaches `0^inf A> 1 1 0 1 (01)^x 0 1 (10)^y+1 R`. -/
theorem own_pair_dot (x y : Nat) (R : Tape) :
    steps (4 * x + 18) ⟨blank, cons true (rep (x) [true, false] (cons false (rep (y + 2) [true, false] (R)))), .A⟩ = some ⟨blank, cons true (cons true (cons false (cons true (rep (x) [false, true] (cons false (cons true (rep (y + 1) [true, false] (R)))))))), .A⟩ := by
  have hn : 4 + (0 + ((x) * 2 + (11 + (0 + ((x) * 2 + (3)))))) = 4 * x + 18 := by omega
  have h0 : steps 4 ⟨blank, cons true (rep (x) [true, false] (cons false (rep (y + 2) [true, false] (R)))), .A⟩ = some ⟨cons false (cons true (blank)), cons false (rep (x) [true, false] (cons false (rep (y + 2) [true, false] (R)))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (blank)), cons false (rep (x) [true, false] (cons false (rep (y + 2) [true, false] (R)))), .A⟩ = some ⟨cons false (cons true (blank)), rep (x) [false, true] (cons false (cons false (rep (y + 2) [true, false] (R)))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (x) [true, false] (cons false (rep (y + 2) [true, false] (R)))) = rep (x) [false, true] (cons false (cons false (rep (y + 2) [true, false] (R)))) from
      rep_rotate (x) [false] [true, false] [false, true] rfl (cons false (rep (y + 2) [true, false] (R)))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((x) * 2) ⟨cons false (cons true (blank)), rep (x) [false, true] (cons false (cons false (rep (y + 2) [true, false] (R)))), .A⟩ = some ⟨rep (x) [false, true] (cons false (cons true (blank))), cons false (cons false (rep (y + 2) [true, false] (R))), .A⟩ :=
    cross_r trans c2 (x) (cons false (cons true (blank))) (cons false (cons false (rep (y + 2) [true, false] (R))))
  have h3 : steps 11 ⟨rep (x) [false, true] (cons false (cons true (blank))), cons false (cons false (rep (y + 2) [true, false] (R))), .A⟩ = some ⟨cons true (rep (x) [false, true] (cons false (cons true (blank)))), cons false (cons false (cons true (rep (y + 1) [true, false] (R)))), .E⟩ := rfl
  have h4 : steps 0 ⟨cons true (rep (x) [false, true] (cons false (cons true (blank)))), cons false (cons false (cons true (rep (y + 1) [true, false] (R)))), .E⟩ = some ⟨rep (x) [true, false] (cons true (cons false (cons true (blank)))), cons false (cons false (cons true (rep (y + 1) [true, false] (R)))), .E⟩ := by
    simp only [steps_zero, show cons true (rep (x) [false, true] (cons false (cons true (blank)))) = rep (x) [true, false] (cons true (cons false (cons true (blank)))) from
      rep_rotate (x) [true] [false, true] [true, false] rfl (cons false (cons true (blank)))]
  have c5 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [false, true] R), .E⟩ := fun _ _ => rfl
  have h5 : steps ((x) * 2) ⟨rep (x) [true, false] (cons true (cons false (cons true (blank)))), cons false (cons false (cons true (rep (y + 1) [true, false] (R)))), .E⟩ = some ⟨cons true (cons false (cons true (blank))), cons false (rep (x) [false, true] (cons false (cons true (rep (y + 1) [true, false] (R))))), .E⟩ :=
    cross_l trans c5 (x) (cons true (cons false (cons true (blank)))) (cons false (cons true (rep (y + 1) [true, false] (R))))
  have h6 : steps 3 ⟨cons true (cons false (cons true (blank))), cons false (rep (x) [false, true] (cons false (cons true (rep (y + 1) [true, false] (R))))), .E⟩ = some ⟨blank, cons true (cons true (cons false (cons true (rep (x) [false, true] (cons false (cons true (rep (y + 1) [true, false] (R)))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (h6)))))))

/-- `0^inf A> 1 (10)^x 1 (10)^y+2 R` reaches `0^inf A> 1 1 0 1 (01)^x 0 0 (10)^y+1 R`. -/
theorem own_pair_bang (x y : Nat) (R : Tape) :
    steps (4 * x + 10) ⟨blank, cons true (rep (x) [true, false] (cons true (rep (y + 2) [true, false] (R)))), .A⟩ = some ⟨blank, cons true (cons true (cons false (cons true (rep (x) [false, true] (cons false (cons false (rep (y + 1) [true, false] (R)))))))), .A⟩ := by
  have hn : 4 + (0 + ((x) * 2 + (3 + (0 + ((x) * 2 + (3)))))) = 4 * x + 10 := by omega
  have h0 : steps 4 ⟨blank, cons true (rep (x) [true, false] (cons true (rep (y + 2) [true, false] (R)))), .A⟩ = some ⟨cons false (cons true (blank)), cons false (rep (x) [true, false] (cons true (rep (y + 2) [true, false] (R)))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (blank)), cons false (rep (x) [true, false] (cons true (rep (y + 2) [true, false] (R)))), .A⟩ = some ⟨cons false (cons true (blank)), rep (x) [false, true] (cons false (cons true (rep (y + 2) [true, false] (R)))), .A⟩ := by
    simp only [steps_zero, show cons false (rep (x) [true, false] (cons true (rep (y + 2) [true, false] (R)))) = rep (x) [false, true] (cons false (cons true (rep (y + 2) [true, false] (R)))) from
      rep_rotate (x) [false] [true, false] [false, true] rfl (cons true (rep (y + 2) [true, false] (R)))]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((x) * 2) ⟨cons false (cons true (blank)), rep (x) [false, true] (cons false (cons true (rep (y + 2) [true, false] (R)))), .A⟩ = some ⟨rep (x) [false, true] (cons false (cons true (blank))), cons false (cons true (rep (y + 2) [true, false] (R))), .A⟩ :=
    cross_r trans c2 (x) (cons false (cons true (blank))) (cons false (cons true (rep (y + 2) [true, false] (R))))
  have h3 : steps 3 ⟨rep (x) [false, true] (cons false (cons true (blank))), cons false (cons true (rep (y + 2) [true, false] (R))), .A⟩ = some ⟨cons true (rep (x) [false, true] (cons false (cons true (blank)))), cons false (cons false (cons false (rep (y + 1) [true, false] (R)))), .E⟩ := rfl
  have h4 : steps 0 ⟨cons true (rep (x) [false, true] (cons false (cons true (blank)))), cons false (cons false (cons false (rep (y + 1) [true, false] (R)))), .E⟩ = some ⟨rep (x) [true, false] (cons true (cons false (cons true (blank)))), cons false (cons false (cons false (rep (y + 1) [true, false] (R)))), .E⟩ := by
    simp only [steps_zero, show cons true (rep (x) [false, true] (cons false (cons true (blank)))) = rep (x) [true, false] (cons true (cons false (cons true (blank)))) from
      rep_rotate (x) [true] [false, true] [true, false] rfl (cons false (cons true (blank)))]
  have c5 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [false, true] R), .E⟩ := fun _ _ => rfl
  have h5 : steps ((x) * 2) ⟨rep (x) [true, false] (cons true (cons false (cons true (blank)))), cons false (cons false (cons false (rep (y + 1) [true, false] (R)))), .E⟩ = some ⟨cons true (cons false (cons true (blank))), cons false (rep (x) [false, true] (cons false (cons false (rep (y + 1) [true, false] (R))))), .E⟩ :=
    cross_l trans c5 (x) (cons true (cons false (cons true (blank)))) (cons false (cons false (rep (y + 1) [true, false] (R))))
  have h6 : steps 3 ⟨cons true (cons false (cons true (blank))), cons false (rep (x) [false, true] (cons false (cons false (rep (y + 1) [true, false] (R))))), .E⟩ = some ⟨blank, cons true (cons true (cons false (cons true (rep (x) [false, true] (cons false (cons false (rep (y + 1) [true, false] (R)))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (h6)))))))

end H122192
