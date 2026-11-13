import Machine

/-! # The zig-zag of the marker of 1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---

During a pass the tape is `L 0 1^g` with the head bouncing between the right end and the marker `0`.  Two bounces
(`z_two`) move the marker 8 cells right, lower the gap by 6 and add 2 cells at the end; by induction (`z_pass`) a
marker with gap `3(e + 2j)` reaches gap `3e` after `2j` bounces, for every `j`, `e` and every tape `L` left of it.
With the first bounce after a launch (`z_c`) and the launches from the left end (`l_0`, `l_2`) this gives the whole
zig-zag of a pass in closed form (`pass_c`, `pass_l0`, `pass_l2`).

The pieces are written by `bbtools.symtm.prove` (`py/pass.py`); the induction is by hand. -/

namespace H65352

open TM

theorem z_two (m : Nat) (L : Tape) :
    steps (12 * m + 30) ⟨rep (m + 2) [true, true, true] (cons false (L)), cons true (blank), .B⟩ = some ⟨rep (m) [true, true, true] (cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (L)))))))))), cons true (blank), .B⟩ := by
  have hn : (m + 2) * 3 + (8 + ((m + 1) * 3 + (2 + ((m + 1) * 3 + (8 + ((m) * 3)))))) = 12 * m + 30 := by omega
  have c0 : ∀ L R : Tape, steps 3 ⟨app [true, true, true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [false, true, false] R), .B⟩ := fun _ _ => rfl
  have h0 : steps ((m + 2) * 3) ⟨rep (m + 2) [true, true, true] (cons false (L)), cons true (blank), .B⟩ = some ⟨cons false (L), cons true (rep (m + 2) [false, true, false] (blank)), .B⟩ :=
    cross_l trans c0 (m + 2) (cons false (L)) (blank)
  have h1 : steps 8 ⟨cons false (L), cons true (rep (m + 2) [false, true, false] (blank)), .B⟩ = some ⟨cons false (cons true (cons true (cons true (cons true (L))))), rep (m + 1) [false, true, false] (blank), .B⟩ := rfl
  have c2 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, true, false] R, .B⟩ = some ⟨app [] (app [true, true, true] L), R, .B⟩ := fun _ _ => rfl
  have h2 : steps ((m + 1) * 3) ⟨cons false (cons true (cons true (cons true (cons true (L))))), rep (m + 1) [false, true, false] (blank), .B⟩ = some ⟨rep (m + 1) [true, true, true] (cons false (cons true (cons true (cons true (cons true (L)))))), blank, .B⟩ :=
    cross_r trans c2 (m + 1) (cons false (cons true (cons true (cons true (cons true (L)))))) (blank)
  have h3 : steps 2 ⟨rep (m + 1) [true, true, true] (cons false (cons true (cons true (cons true (cons true (L)))))), blank, .B⟩ = some ⟨rep (m + 1) [true, true, true] (cons false (cons true (cons true (cons true (cons true (L)))))), cons true (cons true (blank)), .B⟩ := rfl
  have c4 : ∀ L R : Tape, steps 3 ⟨app [true, true, true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [false, true, false] R), .B⟩ := fun _ _ => rfl
  have h4 : steps ((m + 1) * 3) ⟨rep (m + 1) [true, true, true] (cons false (cons true (cons true (cons true (cons true (L)))))), cons true (cons true (blank)), .B⟩ = some ⟨cons false (cons true (cons true (cons true (cons true (L))))), cons true (rep (m + 1) [false, true, false] (cons true (blank))), .B⟩ :=
    cross_l trans c4 (m + 1) (cons false (cons true (cons true (cons true (cons true (L)))))) (cons true (blank))
  have h5 : steps 8 ⟨cons false (cons true (cons true (cons true (cons true (L))))), cons true (rep (m + 1) [false, true, false] (cons true (blank))), .B⟩ = some ⟨cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (L))))))))), rep (m) [false, true, false] (cons true (blank)), .B⟩ := rfl
  have c6 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, true, false] R, .B⟩ = some ⟨app [] (app [true, true, true] L), R, .B⟩ := fun _ _ => rfl
  have h6 : steps ((m) * 3) ⟨cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (L))))))))), rep (m) [false, true, false] (cons true (blank)), .B⟩ = some ⟨rep (m) [true, true, true] (cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (L)))))))))), cons true (blank), .B⟩ :=
    cross_r trans c6 (m) (cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (L)))))))))) (cons true (blank))
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (h6)))))))

theorem z_c (m : Nat) (L : Tape) :
    steps (6 * m + 12) ⟨cons true (rep (m + 1) [true, true, true] (cons false (L))), cons false (blank), .C⟩ = some ⟨rep (m) [true, true, true] (cons false (cons true (cons true (cons true (cons true (L)))))), cons true (blank), .B⟩ := by
  have hn : 1 + ((m + 1) * 3 + (8 + ((m) * 3))) = 6 * m + 12 := by omega
  have h0 : steps 1 ⟨cons true (rep (m + 1) [true, true, true] (cons false (L))), cons false (blank), .C⟩ = some ⟨rep (m + 1) [true, true, true] (cons false (L)), cons true (cons true (blank)), .B⟩ := rfl
  have c1 : ∀ L R : Tape, steps 3 ⟨app [true, true, true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [false, true, false] R), .B⟩ := fun _ _ => rfl
  have h1 : steps ((m + 1) * 3) ⟨rep (m + 1) [true, true, true] (cons false (L)), cons true (cons true (blank)), .B⟩ = some ⟨cons false (L), cons true (rep (m + 1) [false, true, false] (cons true (blank))), .B⟩ :=
    cross_l trans c1 (m + 1) (cons false (L)) (cons true (blank))
  have h2 : steps 8 ⟨cons false (L), cons true (rep (m + 1) [false, true, false] (cons true (blank))), .B⟩ = some ⟨cons false (cons true (cons true (cons true (cons true (L))))), rep (m) [false, true, false] (cons true (blank)), .B⟩ := rfl
  have c3 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, true, false] R, .B⟩ = some ⟨app [] (app [true, true, true] L), R, .B⟩ := fun _ _ => rfl
  have h3 : steps ((m) * 3) ⟨cons false (cons true (cons true (cons true (cons true (L))))), rep (m) [false, true, false] (cons true (blank)), .B⟩ = some ⟨rep (m) [true, true, true] (cons false (cons true (cons true (cons true (cons true (L)))))), cons true (blank), .B⟩ :=
    cross_r trans c3 (m) (cons false (cons true (cons true (cons true (cons true (L)))))) (cons true (blank))
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

theorem l_0 (m : Nat) :
    steps (6 * m + 24) ⟨rep (m + 3) [true, true, true] (blank), cons false (blank), .C⟩ = some ⟨rep (m + 2) [true, true, true] (cons false (cons true (cons true (cons false (cons true (blank)))))), cons true (blank), .B⟩ := by
  have hn : 1 + (0 + ((m + 2) * 3 + (11 + ((m + 2) * 3)))) = 6 * m + 24 := by omega
  have h0 : steps 1 ⟨rep (m + 3) [true, true, true] (blank), cons false (blank), .C⟩ = some ⟨cons true (cons true (rep (m + 2) [true, true, true] (blank))), cons true (cons true (blank)), .B⟩ := rfl
  have h1 : steps 0 ⟨cons true (cons true (rep (m + 2) [true, true, true] (blank))), cons true (cons true (blank)), .B⟩ = some ⟨rep (m + 2) [true, true, true] (cons true (cons true (blank))), cons true (cons true (blank)), .B⟩ := by
    simp only [steps_zero, show cons true (cons true (rep (m + 2) [true, true, true] (blank))) = rep (m + 2) [true, true, true] (cons true (cons true (blank))) from
      rep_rotate (m + 2) [true, true] [true, true, true] [true, true, true] rfl (blank)]
  have c2 : ∀ L R : Tape, steps 3 ⟨app [true, true, true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [false, true, false] R), .B⟩ := fun _ _ => rfl
  have h2 : steps ((m + 2) * 3) ⟨rep (m + 2) [true, true, true] (cons true (cons true (blank))), cons true (cons true (blank)), .B⟩ = some ⟨cons true (cons true (blank)), cons true (rep (m + 2) [false, true, false] (cons true (blank))), .B⟩ :=
    cross_l trans c2 (m + 2) (cons true (cons true (blank))) (cons true (blank))
  have h3 : steps 11 ⟨cons true (cons true (blank)), cons true (rep (m + 2) [false, true, false] (cons true (blank))), .B⟩ = some ⟨cons false (cons true (cons true (cons false (cons true (blank))))), rep (m + 2) [false, true, false] (cons true (blank)), .B⟩ := rfl
  have c4 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, true, false] R, .B⟩ = some ⟨app [] (app [true, true, true] L), R, .B⟩ := fun _ _ => rfl
  have h4 : steps ((m + 2) * 3) ⟨cons false (cons true (cons true (cons false (cons true (blank))))), rep (m + 2) [false, true, false] (cons true (blank)), .B⟩ = some ⟨rep (m + 2) [true, true, true] (cons false (cons true (cons true (cons false (cons true (blank)))))), cons true (blank), .B⟩ :=
    cross_r trans c4 (m + 2) (cons false (cons true (cons true (cons false (cons true (blank)))))) (cons true (blank))
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

theorem l_2 (m : Nat) :
    steps (18 * m + 78) ⟨cons true (cons true (rep (m + 3) [true, true, true] (blank))), cons false (blank), .C⟩ = some ⟨rep (m + 2) [true, true, true] (cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons false (cons true (blank)))))))))), cons true (blank), .B⟩ := by
  have hn : 1 + (0 + ((m + 3) * 3 + (3 + (0 + ((m + 3) * 3 + (2 + (0 + ((m + 3) * 3 + (11 + ((m + 3) * 3 + (2 + ((m + 3) * 3 + (8 + ((m + 2) * 3)))))))))))))) = 18 * m + 78 := by omega
  have h0 : steps 1 ⟨cons true (cons true (rep (m + 3) [true, true, true] (blank))), cons false (blank), .C⟩ = some ⟨cons true (rep (m + 3) [true, true, true] (blank)), cons true (cons true (blank)), .B⟩ := rfl
  have h1 : steps 0 ⟨cons true (rep (m + 3) [true, true, true] (blank)), cons true (cons true (blank)), .B⟩ = some ⟨rep (m + 3) [true, true, true] (cons true (blank)), cons true (cons true (blank)), .B⟩ := by
    simp only [steps_zero, show cons true (rep (m + 3) [true, true, true] (blank)) = rep (m + 3) [true, true, true] (cons true (blank)) from
      rep_rotate (m + 3) [true] [true, true, true] [true, true, true] rfl (blank)]
  have c2 : ∀ L R : Tape, steps 3 ⟨app [true, true, true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [false, true, false] R), .B⟩ := fun _ _ => rfl
  have h2 : steps ((m + 3) * 3) ⟨rep (m + 3) [true, true, true] (cons true (blank)), cons true (cons true (blank)), .B⟩ = some ⟨cons true (blank), cons true (rep (m + 3) [false, true, false] (cons true (blank))), .B⟩ :=
    cross_l trans c2 (m + 3) (cons true (blank)) (cons true (blank))
  have h3 : steps 3 ⟨cons true (blank), cons true (rep (m + 3) [false, true, false] (cons true (blank))), .B⟩ = some ⟨cons false (blank), cons true (cons false (rep (m + 3) [false, true, false] (cons true (blank)))), .C⟩ := rfl
  have h4 : steps 0 ⟨cons false (blank), cons true (cons false (rep (m + 3) [false, true, false] (cons true (blank)))), .C⟩ = some ⟨cons false (blank), rep (m + 3) [true, false, false] (cons true (cons false (cons true (blank)))), .C⟩ := by
    simp only [steps_zero, show cons true (cons false (rep (m + 3) [false, true, false] (cons true (blank)))) = rep (m + 3) [true, false, false] (cons true (cons false (cons true (blank)))) from
      rep_rotate (m + 3) [true, false] [false, true, false] [true, false, false] rfl (cons true (blank))]
  have c5 : ∀ L R : Tape, steps 3 ⟨app [] L, app [true, false, false] R, .C⟩ = some ⟨app [] (app [true, true, true] L), R, .C⟩ := fun _ _ => rfl
  have h5 : steps ((m + 3) * 3) ⟨cons false (blank), rep (m + 3) [true, false, false] (cons true (cons false (cons true (blank)))), .C⟩ = some ⟨rep (m + 3) [true, true, true] (cons false (blank)), cons true (cons false (cons true (blank))), .C⟩ :=
    cross_r trans c5 (m + 3) (cons false (blank)) (cons true (cons false (cons true (blank))))
  have h6 : steps 2 ⟨rep (m + 3) [true, true, true] (cons false (blank)), cons true (cons false (cons true (blank))), .C⟩ = some ⟨cons true (cons true (rep (m + 3) [true, true, true] (cons false (blank)))), cons true (blank), .B⟩ := rfl
  have h7 : steps 0 ⟨cons true (cons true (rep (m + 3) [true, true, true] (cons false (blank)))), cons true (blank), .B⟩ = some ⟨rep (m + 3) [true, true, true] (cons true (cons true (cons false (blank)))), cons true (blank), .B⟩ := by
    simp only [steps_zero, show cons true (cons true (rep (m + 3) [true, true, true] (cons false (blank)))) = rep (m + 3) [true, true, true] (cons true (cons true (cons false (blank)))) from
      rep_rotate (m + 3) [true, true] [true, true, true] [true, true, true] rfl (cons false (blank))]
  have c8 : ∀ L R : Tape, steps 3 ⟨app [true, true, true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [false, true, false] R), .B⟩ := fun _ _ => rfl
  have h8 : steps ((m + 3) * 3) ⟨rep (m + 3) [true, true, true] (cons true (cons true (cons false (blank)))), cons true (blank), .B⟩ = some ⟨cons true (cons true (cons false (blank))), cons true (rep (m + 3) [false, true, false] (blank)), .B⟩ :=
    cross_l trans c8 (m + 3) (cons true (cons true (cons false (blank)))) (blank)
  have h9 : steps 11 ⟨cons true (cons true (cons false (blank))), cons true (rep (m + 3) [false, true, false] (blank)), .B⟩ = some ⟨cons false (cons true (cons true (cons false (cons true (blank))))), rep (m + 3) [false, true, false] (blank), .B⟩ := rfl
  have c10 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, true, false] R, .B⟩ = some ⟨app [] (app [true, true, true] L), R, .B⟩ := fun _ _ => rfl
  have h10 : steps ((m + 3) * 3) ⟨cons false (cons true (cons true (cons false (cons true (blank))))), rep (m + 3) [false, true, false] (blank), .B⟩ = some ⟨rep (m + 3) [true, true, true] (cons false (cons true (cons true (cons false (cons true (blank)))))), blank, .B⟩ :=
    cross_r trans c10 (m + 3) (cons false (cons true (cons true (cons false (cons true (blank)))))) (blank)
  have h11 : steps 2 ⟨rep (m + 3) [true, true, true] (cons false (cons true (cons true (cons false (cons true (blank)))))), blank, .B⟩ = some ⟨rep (m + 3) [true, true, true] (cons false (cons true (cons true (cons false (cons true (blank)))))), cons true (cons true (blank)), .B⟩ := rfl
  have c12 : ∀ L R : Tape, steps 3 ⟨app [true, true, true] L, app [true] R, .B⟩ = some ⟨L, app [true] (app [false, true, false] R), .B⟩ := fun _ _ => rfl
  have h12 : steps ((m + 3) * 3) ⟨rep (m + 3) [true, true, true] (cons false (cons true (cons true (cons false (cons true (blank)))))), cons true (cons true (blank)), .B⟩ = some ⟨cons false (cons true (cons true (cons false (cons true (blank))))), cons true (rep (m + 3) [false, true, false] (cons true (blank))), .B⟩ :=
    cross_l trans c12 (m + 3) (cons false (cons true (cons true (cons false (cons true (blank)))))) (cons true (blank))
  have h13 : steps 8 ⟨cons false (cons true (cons true (cons false (cons true (blank))))), cons true (rep (m + 3) [false, true, false] (cons true (blank))), .B⟩ = some ⟨cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons false (cons true (blank))))))))), rep (m + 2) [false, true, false] (cons true (blank)), .B⟩ := rfl
  have c14 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, true, false] R, .B⟩ = some ⟨app [] (app [true, true, true] L), R, .B⟩ := fun _ _ => rfl
  have h14 : steps ((m + 2) * 3) ⟨cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons false (cons true (blank))))))))), rep (m + 2) [false, true, false] (cons true (blank)), .B⟩ = some ⟨rep (m + 2) [true, true, true] (cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons false (cons true (blank)))))))))), cons true (blank), .B⟩ :=
    cross_r trans c14 (m + 2) (cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons false (cons true (blank)))))))))) (cons true (blank))
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 (steps_seq trans h5 (steps_seq trans h6 (steps_seq trans h7 (steps_seq trans h8 (steps_seq trans h9 (steps_seq trans h10 (steps_seq trans h11 (steps_seq trans h12 (steps_seq trans h13 (h14)))))))))))))))


/-- What a launch from the left end leaves left of the marker: `1 0 1 1` and `1 0 1 1 1 1 1 1`. -/
abbrev Z0 : Tape := cons true (cons true (cons false (cons true blank)))
abbrev Z2 : Tape := cons true (cons true (cons true (cons true (cons true (cons true (cons false (cons true blank)))))))

/-- Eight 1s. -/
abbrev w8 : List Bool := [true, true, true, true, true, true, true, true]

/-- **The zig-zag.**  `2j` bounces: the marker with gap `3(m+2j)` reaches gap `3m`, leaving `1^(8j)` behind it. -/
theorem z_pass (j : Nat) : ∀ (m : Nat) (L : Tape), ∃ t,
    steps t ⟨rep (m + 2 * j) [true, true, true] (cons false L), cons true blank, .B⟩ =
      some ⟨rep m [true, true, true] (cons false (rep j w8 L)), cons true blank, .B⟩ := by
  induction j with
  | zero => intro m L; exact ⟨0, rfl⟩
  | succ j ih =>
    intro m L
    have e : m + 2 * (j + 1) = (m + 2 * j) + 2 := by omega
    rw [e]
    obtain ⟨t, h⟩ := ih m (app w8 L)
    rw [rep_app_comm] at h
    exact ⟨_, steps_seq trans (z_two (m + 2 * j) L) h⟩

/-- A pass launched with gap `3(e + 2j + 1) + 1` (head in C on the 0 right of the 1s, blank after it). -/
theorem pass_c (e j : Nat) (L : Tape) : ∃ t,
    steps t ⟨cons true (rep (e + 2 * j + 1) [true, true, true] (cons false L)), cons false blank, .C⟩ =
      some ⟨rep e [true, true, true] (cons false (rep j w8 (cons true (cons true (cons true (cons true L)))))),
        cons true blank, .B⟩ := by
  obtain ⟨t, h⟩ := z_pass j e (cons true (cons true (cons true (cons true L))))
  exact ⟨_, steps_seq trans (z_c (e + 2 * j) L) h⟩

/-- A pass launched from the left end with width `3(e + 2j + 3)` and no marker. -/
theorem pass_l0 (e j : Nat) : ∃ t,
    steps t ⟨rep (e + 2 * j + 3) [true, true, true] blank, cons false blank, .C⟩ =
      some ⟨rep e [true, true, true] (cons false (rep (j + 1) w8 Z0)), cons true blank, .B⟩ := by
  obtain ⟨t, h⟩ := z_pass (j + 1) e Z0
  have h0 := l_0 (e + 2 * j)
  have e2 : e + 2 * j + 2 = e + 2 * (j + 1) := by omega
  rw [e2] at h0
  exact ⟨_, steps_seq trans h0 h⟩

/-- A pass launched from the left end with width `3(e + 2j + 3) + 2` and no marker. -/
theorem pass_l2 (e j : Nat) : ∃ t,
    steps t ⟨cons true (cons true (rep (e + 2 * j + 3) [true, true, true] blank)), cons false blank, .C⟩ =
      some ⟨rep e [true, true, true] (cons false (rep (j + 1) w8 Z2)), cons true blank, .B⟩ := by
  obtain ⟨t, h⟩ := z_pass (j + 1) e Z2
  have h0 := l_2 (e + 2 * j)
  have e2 : e + 2 * j + 2 = e + 2 * (j + 1) := by omega
  rw [e2] at h0
  exact ⟨_, steps_seq trans h0 h⟩

end H65352
