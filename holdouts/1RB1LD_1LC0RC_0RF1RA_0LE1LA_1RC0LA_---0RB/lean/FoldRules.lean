import Machine

/-! # 1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB: the fold

Written by `py/fold_rules.py` with `bbtools.symtm` (a symbolic run, its trace checked by the kernel); every count, every tape R to the right. -/

namespace H170561

open TM

/-- One zig-zag of the fold: at the left end, two 1s leave the first block and three join the block after the gap of two 0s. -/
theorem fold_step (m n : Nat) (R : Tape) :
    steps (12 * n + 23) ⟨blank, cons false (rep (n + 2) [true, true] (cons false (cons false (rep (m + 1) [true] (R))))), .A⟩ = some ⟨blank, cons false (cons true (cons true (rep (n) [true, true] (cons false (cons false (cons true (cons true (cons true (rep (m + 1) [true] (R)))))))))), .A⟩ := by
  have h0 : steps 3 ⟨blank, cons false (rep (n + 2) [true, true] (cons false (cons false (rep (m + 1) [true] (R))))), .A⟩ = some ⟨cons true (cons false (cons true (blank))), rep (n + 1) [true, true] (cons false (cons false (rep (m + 1) [true] (R)))), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 10 ⟨app [true, false] L, app [true, true] R, .A⟩ = some ⟨app [true, false] (app [true, true] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((n + 1) * 10) ⟨cons true (cons false (cons true (blank))), rep (n + 1) [true, true] (cons false (cons false (rep (m + 1) [true] (R)))), .A⟩ = some ⟨cons true (cons false (rep (n + 1) [true, true] (cons true (blank)))), cons false (cons false (rep (m + 1) [true] (R))), .A⟩ :=
    cross_r trans c1 (n + 1) (cons true (blank)) (cons false (cons false (rep (m + 1) [true] (R))))
  have h2 : steps 8 ⟨cons true (cons false (rep (n + 1) [true, true] (cons true (blank)))), cons false (cons false (rep (m + 1) [true] (R))), .A⟩ = some ⟨rep (n) [true, true] (cons true (blank)), cons true (cons false (cons false (cons true (cons true (cons true (rep (m + 1) [true] (R))))))), .A⟩ := rfl
  have c3 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, true] R), .A⟩ := fun _ _ => rfl
  have h3 : steps ((n) * 2) ⟨rep (n) [true, true] (cons true (blank)), cons true (cons false (cons false (cons true (cons true (cons true (rep (m + 1) [true] (R))))))), .A⟩ = some ⟨cons true (blank), cons true (rep (n) [true, true] (cons false (cons false (cons true (cons true (cons true (rep (m + 1) [true] (R)))))))), .A⟩ :=
    cross_l trans c3 (n) (cons true (blank)) (cons false (cons false (cons true (cons true (cons true (rep (m + 1) [true] (R)))))))
  have h4 : steps 2 ⟨cons true (blank), cons true (rep (n) [true, true] (cons false (cons false (cons true (cons true (cons true (rep (m + 1) [true] (R)))))))), .A⟩ = some ⟨blank, cons false (cons true (cons true (rep (n) [true, true] (cons false (cons false (cons true (cons true (cons true (rep (m + 1) [true] (R)))))))))), .A⟩ := rfl
  exact steps_congr trans (a := 3 + ((n + 1) * 10 + (8 + ((n) * 2 + (2))))) (by omega) (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (h4)))))

/-- The last zig-zag of the fold: the first block is used up. -/
theorem fold_last (m : Nat) (R : Tape) :
    steps (11) ⟨blank, cons false (cons true (cons true (cons false (cons false (rep (m + 1) [true] (R)))))), .A⟩ = some ⟨blank, cons false (cons false (cons false (cons true (cons true (cons true (rep (m + 1) [true] (R))))))), .A⟩ := by
  have h0 : steps 11 ⟨blank, cons false (cons true (cons true (cons false (cons false (rep (m + 1) [true] (R)))))), .A⟩ = some ⟨blank, cons false (cons false (cons false (cons true (cons true (cons true (rep (m + 1) [true] (R))))))), .A⟩ := rfl
  exact steps_congr trans (a := 11) (by omega) (h0)

/-- After the fold: two new 1s at the left end, one 0 before the merged block. -/
theorem fold_open (m : Nat) (R : Tape) :
    steps (5) ⟨blank, cons false (cons false (cons false (rep (m + 1) [true] (R)))), .A⟩ = some ⟨blank, cons false (cons true (cons true (cons false (rep (m + 1) [true] (R))))), .A⟩ := by
  have h0 : steps 5 ⟨blank, cons false (cons false (cons false (rep (m + 1) [true] (R)))), .A⟩ = some ⟨blank, cons false (cons true (cons true (cons false (rep (m + 1) [true] (R))))), .A⟩ := rfl
  exact steps_congr trans (a := 5) (by omega) (h0)

/-- The split ends with M = 1 (and at least two 1s after the gap): the last 1 of the block goes left, two 1s of the next block become the carrier `0 1`. -/
theorem end1 (L R : Tape) :
    steps (11) ⟨cons true (L), cons false (cons false (cons true (cons false (cons false (cons true (cons true (R))))))), .E⟩ = some ⟨cons true (cons false (cons false (cons false (cons false (cons false (cons true (cons true (L)))))))), R, .A⟩ := by
  have h0 : steps 11 ⟨cons true (L), cons false (cons false (cons true (cons false (cons false (cons true (cons true (R))))))), .E⟩ = some ⟨cons true (cons false (cons false (cons false (cons false (cons false (cons true (cons true (L)))))))), R, .A⟩ := rfl
  exact steps_congr trans (a := 11) (by omega) (h0)

/-- The split ends with M = 3: one 1 goes left, a lone 1 stays, the carrier `0 1` starts on the next block. -/
theorem end3 (L R : Tape) :
    steps (17) ⟨cons true (L), cons false (cons false (cons true (cons true (cons true (cons false (cons false (R))))))), .E⟩ = some ⟨cons true (cons false (cons false (cons false (cons true (cons false (cons true (cons true (L)))))))), R, .A⟩ := by
  have h0 : steps 17 ⟨cons true (L), cons false (cons false (cons true (cons true (cons true (cons false (cons false (R))))))), .E⟩ = some ⟨cons true (cons false (cons false (cons false (cons true (cons false (cons true (cons true (L)))))))), R, .A⟩ := rfl
  exact steps_congr trans (a := 17) (by omega) (h0)

/-- The carrier `0 1` crosses a block of m ones to the right in 5m steps. -/
theorem carry (m : Nat) (L R : Tape) :
    steps (5 * m) ⟨cons true (cons false (L)), rep (m) [true] (cons false (R)), .A⟩ = some ⟨cons true (cons false (rep (m) [true] (L))), cons false (R), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 5 ⟨app [true, false] L, app [true] R, .A⟩ = some ⟨app [true, false] (app [true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((m) * 5) ⟨cons true (cons false (L)), rep (m) [true] (cons false (R)), .A⟩ = some ⟨cons true (cons false (rep (m) [true] (L))), cons false (R), .A⟩ :=
    cross_r trans c0 (m) (L) (cons false (R))
  exact steps_congr trans (a := (m) * 5) (by omega) (h0)

/-- A runs left over ones, two cells per two steps. -/
theorem lsweep (m : Nat) (L R : Tape) :
    steps (2 * m) ⟨rep (m) [true, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (m) [true, true] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, true] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((m) * 2) ⟨rep (m) [true, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (m) [true, true] (R)), .A⟩ :=
    cross_l trans c0 (m) (L) (R)
  exact steps_congr trans (a := (m) * 2) (by omega) (h0)

end H170561
