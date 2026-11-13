import Machine

/-! The halting family of 1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB: the configuration with the head in C on the leftmost cell of 1 1 0 1^(3m+3) (hole at position 2, length divisible by 3) halts, for every m. Proved by `bbtools.symtm`; tapes in Lean are listed from the head outward. -/

namespace H86694

open TM

/-- From `C> 1 1 0 (111)^(m+1)` with blank tape on both sides, the machine reaches F reading a 0 with blank tape to its right in 5m + 21 steps. -/
theorem to_halt (m : Nat) :
    steps (5 * m + 21) ⟨blank, cons true (cons true (cons false (rep (m + 1) [true, true, true] (blank)))), .C⟩ = some ⟨cons false (cons true (cons true (rep (m + 1) [true, true, true] (cons true (cons true (cons true (blank))))))), blank, .F⟩ := by
  have hn : 11 + (0 + ((m + 1) * 5 + (5))) = 5 * m + 21 := by omega
  have h0 : steps 11 ⟨blank, cons true (cons true (cons false (rep (m + 1) [true, true, true] (blank)))), .C⟩ = some ⟨cons true (cons true (cons true (blank))), cons true (cons true (rep (m + 1) [true, true, true] (blank))), .A⟩ := rfl
  have h1 : steps 0 ⟨cons true (cons true (cons true (blank))), cons true (cons true (rep (m + 1) [true, true, true] (blank))), .A⟩ = some ⟨cons true (cons true (cons true (blank))), rep (m + 1) [true, true, true] (cons true (cons true (blank))), .A⟩ := by
    simp only [steps_zero, show cons true (cons true (rep (m + 1) [true, true, true] (blank))) = rep (m + 1) [true, true, true] (cons true (cons true (blank))) from
      rep_rotate (m + 1) [true, true] [true, true, true] [true, true, true] rfl (blank)]
  have c2 : ∀ L R : Tape, steps 5 ⟨app [] L, app [true, true, true] R, .A⟩ = some ⟨app [] (app [true, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h2 : steps ((m + 1) * 5) ⟨cons true (cons true (cons true (blank))), rep (m + 1) [true, true, true] (cons true (cons true (blank))), .A⟩ = some ⟨rep (m + 1) [true, true, true] (cons true (cons true (cons true (blank)))), cons true (cons true (blank)), .A⟩ :=
    cross_r trans c2 (m + 1) (cons true (cons true (cons true (blank)))) (cons true (cons true (blank)))
  have h3 : steps 5 ⟨rep (m + 1) [true, true, true] (cons true (cons true (cons true (blank)))), cons true (cons true (blank)), .A⟩ = some ⟨cons false (cons true (cons true (rep (m + 1) [true, true, true] (cons true (cons true (cons true (blank))))))), blank, .F⟩ := rfl
  exact steps_congr trans hn (steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (h3))))

/-- The whole family halts: the head in C on the leftmost cell of `1 1 0 1^(3m+3)`, blank tape on both sides.
This is the sample configuration (hole at position 2, length 3m + 6) through which, by the observed map in the
README, the run from blank tape would end. -/
theorem halts_family (m : Nat) :
    TM.Halts trans ⟨blank, cons true (cons true (cons false (rep (m + 1) [true, true, true] (blank)))), .C⟩ :=
  ⟨_, _, to_halt m, rfl⟩

end H86694
