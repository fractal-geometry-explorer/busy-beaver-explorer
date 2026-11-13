import Machine

/-! The pieces of one round trip of the right-end regime of 1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---, written by `tools/py/bbtools/symtm.py` (`prove`, `rotate=True`) from the trace and checked by the kernel; `lean/Trip.lean` puts them together. Regenerate with `py/gen_rules.py`. -/

namespace H14847

open TM

/-- At the right end: A crosses the trailing `(1101010)^(m+1)` to the left. -/
theorem rightEnd (m : Nat) (L : Tape) :
    steps (7 * m + 10) ⟨rep (m + 1) [false, true, false, true, false, true, true] (L), blank, .A⟩ = some ⟨cons true (L), cons true (rep (m + 1) [true, false, false, true, true, false, false] (cons true (blank))), .A⟩ := by
  have hn : 3 + (0 + ((m + 1) * 7)) = 7 * m + 10 := by omega
  have h0 : steps 3 ⟨rep (m + 1) [false, true, false, true, false, true, true] (L), blank, .A⟩ = some ⟨cons true (rep (m + 1) [false, true, false, true, false, true, true] (L)), cons true (cons true (blank)), .A⟩ := rfl
  have h1 : steps 0 ⟨cons true (rep (m + 1) [false, true, false, true, false, true, true] (L)), cons true (cons true (blank)), .A⟩ = some ⟨rep (m + 1) [true, false, true, false, true, false, true] (cons true (L)), cons true (cons true (blank)), .A⟩ := by
    simp only [steps_zero, show cons true (rep (m + 1) [false, true, false, true, false, true, true] (L)) = rep (m + 1) [true, false, true, false, true, false, true] (cons true (L)) from
      rep_rotate (m + 1) [true] [false, true, false, true, false, true, true] [true, false, true, false, true, false, true] rfl (L)]
  have c2 : ∀ L R : Tape, steps 7 ⟨app [true, false, true, false, true, false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false, false, true, true, false, false] R), .A⟩ := fun _ _ => rfl
  have h2 : steps ((m + 1) * 7) ⟨rep (m + 1) [true, false, true, false, true, false, true] (cons true (L)), cons true (cons true (blank)), .A⟩ = some ⟨cons true (L), cons true (rep (m + 1) [true, false, false, true, true, false, false] (cons true (blank))), .A⟩ :=
    cross_l trans c2 (m + 1) (cons true (L)) (cons true (blank))
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- Moving left over one block `(10)^(k+2) 1`. -/
theorem crossL (k : Nat) (L R : Tape) :
    steps (2 * k + 5) ⟨cons true (rep (k + 2) [false, true] (L)), cons true (R), .A⟩ = some ⟨L, cons true (rep (k) [true, false] (cons false (cons true (cons true (cons false (cons false (R))))))), .A⟩ := by
  have hn : 5 + ((k) * 2) = 2 * k + 5 := by omega
  have h0 : steps 5 ⟨cons true (rep (k + 2) [false, true] (L)), cons true (R), .A⟩ = some ⟨rep (k) [false, true] (L), cons true (cons false (cons true (cons true (cons false (cons false (R)))))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h1 : steps ((k) * 2) ⟨rep (k) [false, true] (L), cons true (cons false (cons true (cons true (cons false (cons false (R)))))), .A⟩ = some ⟨L, cons true (rep (k) [true, false] (cons false (cons true (cons true (cons false (cons false (R))))))), .A⟩ :=
    cross_l trans c1 (k) (L) (cons false (cons true (cons true (cons false (cons false (R))))))
  exact steps_congr trans hn (steps_seq trans h0 (h1))

/-- The turn at the left end: one new cell. -/
theorem turnL (R : Tape) :
    steps (4) ⟨blank, cons true (R), .A⟩ = some ⟨cons false (cons true (blank)), cons false (R), .A⟩ := by
  have hn : 4 = 4 := by omega
  have h0 : steps 4 ⟨blank, cons true (R), .A⟩ = some ⟨cons false (cons true (blank)), cons false (R), .A⟩ := rfl
  exact steps_congr trans hn (h0)

/-- Moving right over the first block. -/
theorem crossR0 (k : Nat) (L R : Tape) :
    steps (2 * k) ⟨L, cons false (rep (k) [true, false] (R)), .A⟩ = some ⟨rep (k) [false, true] (L), cons false (R), .A⟩ := by
  have hn : 0 + ((k) * 2) = 2 * k := by omega
  have h0 : steps 0 ⟨L, cons false (rep (k) [true, false] (R)), .A⟩ = some ⟨L, rep (k) [false, true] (cons false (R)), .A⟩ := by
    simp only [steps_zero, show cons false (rep (k) [true, false] (R)) = rep (k) [false, true] (cons false (R)) from
      rep_rotate (k) [false] [true, false] [false, true] rfl (R)]
  have c1 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((k) * 2) ⟨L, rep (k) [false, true] (cons false (R)), .A⟩ = some ⟨rep (k) [false, true] (L), cons false (R), .A⟩ :=
    cross_r trans c1 (k) (L) (cons false (R))
  exact steps_congr trans hn (steps_seq trans h0 (h1))

/-- Moving right over one block, which is restored as `1 (10)^(k+2)`. -/
theorem crossR (k : Nat) (L R : Tape) :
    steps (2 * k + 15) ⟨L, cons false (cons false (cons true (cons true (cons false (cons false (rep (k) [true, false] (R))))))), .A⟩ = some ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (R), .A⟩ := by
  have hn : 15 + (0 + ((k) * 2)) = 2 * k + 15 := by omega
  have h0 : steps 15 ⟨L, cons false (cons false (cons true (cons true (cons false (cons false (rep (k) [true, false] (R))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (rep (k) [true, false] (R)), .A⟩ := rfl
  have h1 : steps 0 ⟨cons false (cons true (cons false (cons true (cons true (L))))), cons false (rep (k) [true, false] (R)), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (k) [false, true] (cons false (R)), .A⟩ := by
    simp only [steps_zero, show cons false (rep (k) [true, false] (R)) = rep (k) [false, true] (cons false (R)) from
      rep_rotate (k) [false] [true, false] [false, true] rfl (R)]
  have c2 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((k) * 2) ⟨cons false (cons true (cons false (cons true (cons true (L))))), rep (k) [false, true] (cons false (R)), .A⟩ = some ⟨rep (k) [false, true] (cons false (cons true (cons false (cons true (cons true (L)))))), cons false (R), .A⟩ :=
    cross_r trans c2 (k) (cons false (cons true (cons false (cons true (cons true (L)))))) (cons false (R))
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (h2)))

/-- Back at the right end: the trailing part becomes `(1101010)^(m+1)`. -/
theorem rightEnd2 (m : Nat) (L : Tape) :
    steps (17 * m + 17) ⟨L, cons false (cons false (cons true (cons true (cons false (cons false (rep (m) [true, false, false, true, true, false, false] (cons true (blank)))))))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons false (cons true (rep (m) [true, false, true, false, true, false, true] (cons true (L)))))))), blank, .A⟩ := by
  have hn : 5 + (0 + ((m) * 17 + (12))) = 17 * m + 17 := by omega
  have h0 : steps 5 ⟨L, cons false (cons false (cons true (cons true (cons false (cons false (rep (m) [true, false, false, true, true, false, false] (cons true (blank)))))))), .A⟩ = some ⟨cons true (cons false (cons true (L))), cons true (cons false (cons false (rep (m) [true, false, false, true, true, false, false] (cons true (blank))))), .C⟩ := rfl
  have h1 : steps 0 ⟨cons true (cons false (cons true (L))), cons true (cons false (cons false (rep (m) [true, false, false, true, true, false, false] (cons true (blank))))), .C⟩ = some ⟨cons true (cons false (cons true (L))), rep (m) [true, false, false, true, false, false, true] (cons true (cons false (cons false (cons true (blank))))), .C⟩ := by
    simp only [steps_zero, show cons true (cons false (cons false (rep (m) [true, false, false, true, true, false, false] (cons true (blank))))) = rep (m) [true, false, false, true, false, false, true] (cons true (cons false (cons false (cons true (blank))))) from
      rep_rotate (m) [true, false, false] [true, false, false, true, true, false, false] [true, false, false, true, false, false, true] rfl (cons true (blank))]
  have c2 : ∀ L R : Tape, steps 17 ⟨app [true, false] L, app [true, false, false, true, false, false, true] R, .C⟩ = some ⟨app [true, false] (app [true, false, true, false, true, false, true] L), R, .C⟩ := fun _ _ => rfl
  have h2 : steps ((m) * 17) ⟨cons true (cons false (cons true (L))), rep (m) [true, false, false, true, false, false, true] (cons true (cons false (cons false (cons true (blank))))), .C⟩ = some ⟨cons true (cons false (rep (m) [true, false, true, false, true, false, true] (cons true (L)))), cons true (cons false (cons false (cons true (blank)))), .C⟩ :=
    cross_r trans c2 (m) (cons true (L)) (cons true (cons false (cons false (cons true (blank)))))
  have h3 : steps 12 ⟨cons true (cons false (rep (m) [true, false, true, false, true, false, true] (cons true (L)))), cons true (cons false (cons false (cons true (blank)))), .C⟩ = some ⟨cons false (cons true (cons false (cons true (cons false (cons true (rep (m) [true, false, true, false, true, false, true] (cons true (L)))))))), blank, .A⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

end H14847
