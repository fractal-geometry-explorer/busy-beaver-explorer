import FoldRules

/-! # 1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB: the fold, for every size

At the left end of the tape, in state A, a first block of 2n ones followed by a gap of two 0s and a block of M ones
merges into the second block as 3n ones: `A> 0 1^(2n) 0 0 1^M R` reaches `A> 0 0 0 1^(M+3n) R` (`fold`), and then
`A> 0 1 1 0 1^(M+3n) R` (`fold_open`).  Each zig-zag of the head moves two 1s out of the first block and three into
the second (`fold_step`, `fold_last` in `FoldRules.lean`); the induction over the zig-zags is here. -/

namespace H170561

open TM

theorem ones_rep3 (m : Nat) (R : Tape) :
    cons true (cons true (cons true (rep m [true] R))) = rep (m + 3) [true] R := rfl

/-- n + 1 zig-zags: `A> 0 (11)^(n+1) 0 0 1^(m+1)` becomes `A> 0 0 0 1^(m+1+3(n+1))`. -/
theorem fold_aux (n : Nat) : ∀ (m : Nat) (R : Tape),
    ∃ t, steps t ⟨blank, cons false (rep (n + 1) [true, true] (cons false (cons false (rep (m + 1) [true] R)))), .A⟩ =
      some ⟨blank, cons false (cons false (cons false (rep (m + 1 + 3 * (n + 1)) [true] R))), .A⟩ := by
  induction n with
  | zero =>
    intro m R
    have h := fold_last m R
    rw [ones_rep3] at h
    exact ⟨_, by rw [show m + 1 + 3 * (0 + 1) = m + 1 + 3 by omega]; exact h⟩
  | succ n ih =>
    intro m R
    have h1 := fold_step m n R
    have e : cons true (cons true (rep n [true, true] (cons false (cons false (cons true (cons true (cons true
        (rep (m + 1) [true] R)))))))) = rep (n + 1) [true, true] (cons false (cons false (rep ((m + 3) + 1) [true] R))) := by
      rw [ones_rep3, show m + 1 + 3 = m + 3 + 1 by omega]; rfl
    rw [e] at h1
    obtain ⟨t, h2⟩ := ih (m + 3) R
    rw [show m + 3 + 1 + 3 * (n + 1) = m + 1 + 3 * (n + 1 + 1) by omega] at h2
    exact ⟨_, steps_seq trans h1 h2⟩

/-- **The fold.**  `A> 0 1^(2n) 0 0 1^M R` reaches `A> 0 0 0 1^(M+3n) R`, for every n, every M ≥ 1 and every R. -/
theorem fold (n M : Nat) (R : Tape) (hM : 1 ≤ M) :
    ∃ t, steps t ⟨blank, cons false (rep n [true, true] (cons false (cons false (rep M [true] R)))), .A⟩ =
      some ⟨blank, cons false (cons false (cons false (rep (M + 3 * n) [true] R))), .A⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  cases n with
  | zero => exact ⟨0, rfl⟩
  | succ n => exact fold_aux n m R

/-- The fold followed by `fold_open`: `A> 0 1^(2n) 0 0 1^M R` reaches `A> 0 1 1 0 1^(M+3n) R`. -/
theorem fold_full (n M : Nat) (R : Tape) (hM : 1 ≤ M) :
    ∃ t, steps t ⟨blank, cons false (rep n [true, true] (cons false (cons false (rep M [true] R)))), .A⟩ =
      some ⟨blank, cons false (cons true (cons true (cons false (rep (M + 3 * n) [true] R)))), .A⟩ := by
  obtain ⟨t, h1⟩ := fold n M R hM
  obtain ⟨k, hk⟩ : ∃ k, M + 3 * n = k + 1 := ⟨M + 3 * n - 1, by omega⟩
  have h2 := fold_open k R
  rw [← hk] at h2
  exact ⟨_, steps_seq trans h1 h2⟩

end H170561
