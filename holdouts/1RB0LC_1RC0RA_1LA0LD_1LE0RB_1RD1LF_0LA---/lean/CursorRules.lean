import Machine

/-! The pieces of one round trip of the left-end (cursor) phase of 1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---, written by `tools/py/bbtools/symtm.py` from the trace and checked by the kernel; `lean/Cursor.lean` puts them together. Regenerate with `py/gen_rules.py`. -/

namespace H14847

open TM

/-- Left-end phase, moving right over one unit `(01)^b 0 0110`. -/
theorem unitR (b : Nat) (L R : Tape) :
    steps (2 * b + 15) ⟨L, rep (b) [false, true] (cons false (cons false (cons true (cons true (cons false (R)))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (rep (b) [false, true] (L)))))), R, .A⟩ := by
  have hn : (b) * 2 + (15) = 2 * b + 15 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((b) * 2) ⟨L, rep (b) [false, true] (cons false (cons false (cons true (cons true (cons false (R)))))), .A⟩ = some ⟨rep (b) [false, true] (L), cons false (cons false (cons true (cons true (cons false (R))))), .A⟩ :=
    cross_r trans c0 (b) (L) (cons false (cons false (cons true (cons true (cons false (R))))))
  have h1 : steps 15 ⟨rep (b) [false, true] (L), cons false (cons false (cons true (cons true (cons false (R))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (rep (b) [false, true] (L)))))), R, .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (h1))

/-- Left-end phase, moving left over one unit. -/
theorem unitL (b : Nat) (L R : Tape) :
    steps (2 * b + 9) ⟨cons false (cons true (cons false (cons true (cons true (rep (b + 2) [false, true] (L)))))), cons true (R), .A⟩ = some ⟨L, cons true (rep (b) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (R))))))))))), .A⟩ := by
  have hn : 9 + ((b) * 2) = 2 * b + 9 := by omega
  have h0 : steps 9 ⟨cons false (cons true (cons false (cons true (cons true (rep (b + 2) [false, true] (L)))))), cons true (R), .A⟩ = some ⟨rep (b) [false, true] (L), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (R)))))))))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h1 : steps ((b) * 2) ⟨rep (b) [false, true] (L), cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (R)))))))))), .A⟩ = some ⟨L, cons true (rep (b) [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (R))))))))))), .A⟩ :=
    cross_l trans c1 (b) (L) (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false (R))))))))))
  exact steps_congr trans hn (steps_seq trans h0 (h1))

/-- The turn at a cursor `(01)^(c+2) (10)^(d+2) 0110`. -/
theorem turnC1 (c d : Nat) (L R : Tape) :
    steps (4 * c + 8) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (c + 2) [false, true] (rep (d + 2) [true, false] (cons false (cons true (cons true (cons false (R)))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (rep (c + 1) [false, true] (cons false (cons false (rep (d + 1) [true, false] (cons false (cons true (cons true (cons false (R)))))))))), .A⟩ := by
  have hn : (c + 2) * 2 + (1 + (0 + ((c + 1) * 2 + (1)))) = 4 * c + 8 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((c + 2) * 2) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (c + 2) [false, true] (rep (d + 2) [true, false] (cons false (cons true (cons true (cons false (R)))))), .A⟩ = some ⟨rep (c + 2) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), rep (d + 2) [true, false] (cons false (cons true (cons true (cons false (R))))), .A⟩ :=
    cross_r trans c0 (c + 2) (cons false (cons true (cons false (cons true (cons true (L)))))) (rep (d + 2) [true, false] (cons false (cons true (cons true (cons false (R))))))
  have h1 : steps 1 ⟨rep (c + 2) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), rep (d + 2) [true, false] (cons false (cons true (cons true (cons false (R))))), .A⟩ = some ⟨cons true (rep (c + 1) [false, true] (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons false (rep (d + 1) [true, false] (cons false (cons true (cons true (cons false (R)))))))), .C⟩ := rfl
  have h2 : steps 0 ⟨cons true (rep (c + 1) [false, true] (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons false (rep (d + 1) [true, false] (cons false (cons true (cons true (cons false (R)))))))), .C⟩ = some ⟨rep (c + 1) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons false (rep (d + 1) [true, false] (cons false (cons true (cons true (cons false (R)))))))), .C⟩ := by
    simp only [steps_zero, show cons true (rep (c + 1) [false, true] (cons false (cons true (cons false (cons true (cons true (L))))))) = rep (c + 1) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (L))))))) from
      rep_rotate (c + 1) [true] [false, true] [true, false] rfl (cons false (cons true (cons false (cons true (cons true (L))))))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [false, true] R), .C⟩ := fun _ _ => rfl
  have h3 : steps ((c + 1) * 2) ⟨rep (c + 1) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons false (rep (d + 1) [true, false] (cons false (cons true (cons true (cons false (R)))))))), .C⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (rep (c + 1) [false, true] (cons false (cons false (rep (d + 1) [true, false] (cons false (cons true (cons true (cons false (R))))))))), .C⟩ :=
    cross_l trans c3 (c + 1) (cons true (cons false (cons true (cons false (cons true (cons true (L))))))) (cons false (cons false (rep (d + 1) [true, false] (cons false (cons true (cons true (cons false (R))))))))
  have h4 : steps 1 ⟨cons true (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (rep (c + 1) [false, true] (cons false (cons false (rep (d + 1) [true, false] (cons false (cons true (cons true (cons false (R))))))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (rep (c + 1) [false, true] (cons false (cons false (rep (d + 1) [true, false] (cons false (cons true (cons true (cons false (R)))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- The turn at a cursor `(01)^(c+2) 0 (01)^(d+2) 0 0110`. -/
theorem turnC2 (c d : Nat) (L R : Tape) :
    steps (4 * c + 16) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (c + 2) [false, true] (cons false (rep (d + 2) [false, true] (cons false (cons false (cons true (cons true (cons false (R)))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (rep (c + 2) [false, true] (cons false (cons true (cons true (rep (d) [false, true] (cons false (cons false (cons true (cons true (cons false (R)))))))))))), .A⟩ := by
  have hn : (c + 2) * 2 + (7 + (0 + ((c + 2) * 2 + (1)))) = 4 * c + 16 := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((c + 2) * 2) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (c + 2) [false, true] (cons false (rep (d + 2) [false, true] (cons false (cons false (cons true (cons true (cons false (R)))))))), .A⟩ = some ⟨rep (c + 2) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (rep (d + 2) [false, true] (cons false (cons false (cons true (cons true (cons false (R))))))), .A⟩ :=
    cross_r trans c0 (c + 2) (cons false (cons true (cons false (cons true (cons true (L)))))) (cons false (rep (d + 2) [false, true] (cons false (cons false (cons true (cons true (cons false (R))))))))
  have h1 : steps 7 ⟨rep (c + 2) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (rep (d + 2) [false, true] (cons false (cons false (cons true (cons true (cons false (R))))))), .A⟩ = some ⟨cons true (rep (c + 2) [false, true] (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons true (rep (d) [false, true] (cons false (cons false (cons true (cons true (cons false (R)))))))))), .C⟩ := rfl
  have h2 : steps 0 ⟨cons true (rep (c + 2) [false, true] (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons true (rep (d) [false, true] (cons false (cons false (cons true (cons true (cons false (R)))))))))), .C⟩ = some ⟨rep (c + 2) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons true (rep (d) [false, true] (cons false (cons false (cons true (cons true (cons false (R)))))))))), .C⟩ := by
    simp only [steps_zero, show cons true (rep (c + 2) [false, true] (cons false (cons true (cons false (cons true (cons true (L))))))) = rep (c + 2) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (L))))))) from
      rep_rotate (c + 2) [true] [false, true] [true, false] rfl (cons false (cons true (cons false (cons true (cons true (L))))))]
  have c3 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [false, true] R), .C⟩ := fun _ _ => rfl
  have h3 : steps ((c + 2) * 2) ⟨rep (c + 2) [true, false] (cons true (cons false (cons true (cons false (cons true (cons true (L))))))), cons false (cons false (cons true (cons true (rep (d) [false, true] (cons false (cons false (cons true (cons true (cons false (R)))))))))), .C⟩ = some ⟨cons true (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (rep (c + 2) [false, true] (cons false (cons true (cons true (rep (d) [false, true] (cons false (cons false (cons true (cons true (cons false (R))))))))))), .C⟩ :=
    cross_l trans c3 (c + 2) (cons true (cons false (cons true (cons false (cons true (cons true (L))))))) (cons false (cons true (cons true (rep (d) [false, true] (cons false (cons false (cons true (cons true (cons false (R))))))))))
  have h4 : steps 1 ⟨cons true (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (rep (c + 2) [false, true] (cons false (cons true (cons true (rep (d) [false, true] (cons false (cons false (cons true (cons true (cons false (R))))))))))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons true (cons true (rep (c + 2) [false, true] (cons false (cons true (cons true (rep (d) [false, true] (cons false (cons false (cons true (cons true (cons false (R)))))))))))), .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- The turn at the left end in the left-end phase. -/
theorem edgeL (R : Tape) :
    steps (2) ⟨blank, cons true (R), .A⟩ = some ⟨blank, cons false (cons true (cons false (R))), .A⟩ := by
  have hn : 2 = 2 := by omega
  have h0 : steps 2 ⟨blank, cons true (R), .A⟩ = some ⟨blank, cons false (cons true (cons false (R))), .A⟩ := rfl
  exact steps_congr trans hn (h0)

end H14847
