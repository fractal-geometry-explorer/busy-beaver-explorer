import Rules

/-!
# 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the binary counter counts, by induction on its width

`cfg N R` is the record in B  `0^inf B> 0 10 (1011)^N 1010 1011 R`.  Right of it is the binary counter: digit i is
the word 1010 (0) or 1111 (1) for even i and 10 (0) or 11 (1) for odd i, least significant digit first, so a pair of
digits is 101010 (both 0) or 111111 (both 1).  `inc_even`, `inc_odd` (Rules.lean) are the two carries; `count m`
runs a counter of 2m digits from all zeros to all ones (2^(2m) - 1 increments), whatever lies right of it.
-/

namespace H166286

open TM

/-- `0^inf B> 0 10 (1011)^N 1010 1011 R` -/
def cfg (N : Nat) (R : Tape) : Config :=
  ⟨blank, cons false (cons true (cons false (rep N [true, false, true, true]
    (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true R))))))))))), .B⟩

/-- m pairs of 0-digits -/
abbrev Z (m : Nat) (R : Tape) : Tape := rep m [true, false, true, false, true, false] R
/-- m pairs of 1-digits -/
abbrev O (m : Nat) (R : Tape) : Tape := rep m [true, true, true, true, true, true] R

theorem rot_x (n : Nat) (s : Tape) :
    cons true (cons false (cons true (rep n [true, true, false, true] s)))
      = rep n [true, false, true, true] (cons true (cons false (cons true s))) := by
  have h := rep_rotate n [true, false, true] [true, true, false, true] [true, false, true, true] rfl s
  simpa [app] using h

theorem rot_z (m : Nat) (s : Tape) :
    cons true (rep m [false, true, false, true, false, true] s) = rep m [true, false, true, false, true, false] (cons true s) := by
  have h := rep_rotate m [true] [false, true, false, true, false, true] [true, false, true, false, true, false] rfl s
  simpa [app] using h

theorem rot_10 (m : Nat) (s : Tape) :
    cons true (cons false (rep m [true, false, true, false, true, false] s))
      = rep m [true, false, true, false, true, false] (cons true (cons false s)) := by
  have h := rep_rotate m [true, false] [true, false, true, false, true, false] [true, false, true, false, true, false] rfl s
  simpa [app] using h

/-- Carry to an even digit: `O m (1010 R)` -> `Z m (1111 R)`, and the block gains a word. -/
theorem inc_e (N m : Nat) (R : Tape) :
    ∃ s, steps s (cfg N (O m (cons true (cons false (cons true (cons false R))))))
      = some (cfg (N + 1) (Z m (cons true (cons true (cons true (cons true R)))))) := by
  have h := inc_even m N R
  simp only [rot_z, rot_x] at h
  exact ⟨_, h⟩

/-- Carry to an odd digit: `O m (1111 10 R)` -> `Z m (1010 11 R)`. -/
theorem inc_o (N m : Nat) (R : Tape) :
    ∃ s, steps s (cfg N (O m (cons true (cons true (cons true (cons true (cons true (cons false R))))))))
      = some (cfg (N + 1) (Z m (cons true (cons false (cons true (cons false (cons true (cons true R)))))))) := by
  have h := inc_odd m N R
  simp only [rot_z, rot_x, rot_10] at h
  exact ⟨_, h⟩

theorem reach_trans {a b c : Config} (h1 : ∃ s, steps s a = some b) (h2 : ∃ s, steps s b = some c) :
    ∃ s, steps s a = some c := by
  obtain ⟨s1, h1⟩ := h1
  obtain ⟨s2, h2⟩ := h2
  exact ⟨_, steps_seq trans h1 h2⟩

theorem z_succ (m : Nat) (R : Tape) :
    Z (m + 1) R = Z m (cons true (cons false (cons true (cons false (cons true (cons false R)))))) := by
  simp only [Z]; rw [← rep_app_comm]; rfl

theorem o_succ (m : Nat) (R : Tape) :
    O (m + 1) R = O m (cons true (cons true (cons true (cons true (cons true (cons true R)))))) := by
  simp only [O]; rw [← rep_app_comm]; rfl

/-- A counter of 2m digits counts from 0 to 2^(2m) - 1: the block grows by 4^m - 1 words, R is never read. -/
theorem count (m : Nat) : ∀ N R, ∃ s, steps s (cfg N (Z m R)) = some (cfg (N + (4 ^ m - 1)) (O m R)) := by
  induction m with
  | zero => intro N R; exact ⟨0, by simp [Z, O, rep]⟩
  | succ m ih =>
    intro N R
    have hp : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by decide)
    rw [z_succ, o_succ]
    -- low half 0, digits 2m, 2m+1 = 0 0
    have s1 := ih N (cons true (cons false (cons true (cons false (cons true (cons false R))))))
    have s2 := inc_e (N + (4 ^ m - 1)) m (cons true (cons false R))
    have s3 := ih (N + (4 ^ m - 1) + 1) (cons true (cons true (cons true (cons true (cons true (cons false R))))))
    have s4 := inc_o (N + (4 ^ m - 1) + 1 + (4 ^ m - 1)) m R
    have s5 := ih (N + (4 ^ m - 1) + 1 + (4 ^ m - 1) + 1) (cons true (cons false (cons true (cons false (cons true (cons true R))))))
    have s6 := inc_e (N + (4 ^ m - 1) + 1 + (4 ^ m - 1) + 1 + (4 ^ m - 1)) m (cons true (cons true R))
    have s7 := ih (N + (4 ^ m - 1) + 1 + (4 ^ m - 1) + 1 + (4 ^ m - 1) + 1)
      (cons true (cons true (cons true (cons true (cons true (cons true R))))))
    have e : N + (4 ^ m - 1) + 1 + (4 ^ m - 1) + 1 + (4 ^ m - 1) + 1 + (4 ^ m - 1) = N + (4 ^ (m + 1) - 1) := by
      rw [Nat.pow_succ]; omega
    rw [e] at s7
    exact reach_trans s1 (reach_trans s2 (reach_trans s3 (reach_trans s4 (reach_trans s5 (reach_trans s6 s7)))))

end H166286
