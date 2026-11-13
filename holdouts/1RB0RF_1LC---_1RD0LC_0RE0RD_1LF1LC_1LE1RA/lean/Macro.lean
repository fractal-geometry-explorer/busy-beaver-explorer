import Rules

/-!
# 1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA: the sample configuration and the proved transitions between samples

The sample configuration is `K P m = 0^inf P (10)^m C> 1 1 1 1 1 0^inf`: a short prefix word `P` at the left end,
`m` words `10`, and the head in state C at the left end of a block of five ones.  From `K P m` the machine makes
`⌊m/2⌋` round trips (`sweeps`, from the rule `sweep` of `Rules.lean`), each eating two words `10` and growing the
block of ones by 6, and then rewrites the block as words `10` (the `end_*` rules), giving the next sample.

Proved here for the prefixes `P = empty` and `P = 1` (both parities of `m`):

* `K empty (2n)     → K 1 (3n + 4)`        * `K empty (2n + 1) → K empty (3n + 7)`
* `K 1 (2n)         → K empty (3n + 4)`    * `K 1 (2n + 1)     → K 1000 (3n + 4)`

and from blank tape the run reaches `K 1 1` in 30 steps (`blank_K`).
-/

namespace H119593

open TM

/-- The sample configuration `0^inf P (10)^m C> 1 1 1 1 1 0^inf` (`P` as a left tape, nearest cell first). -/
def K (P : Tape) (m : Nat) : Config := ⟨rep m [false, true] P, cons true (rep 2 [true, true] blank), .C⟩

theorem ones_shift (j : Nat) : rep j [true, true] (cons true blank) = cons true (rep j [true, true] blank) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [rep_succ, ih]; rfl

/-- `n` round trips: `L (10)^(m+2n) C> 1 (11)^(j+1)` reaches `L (10)^m C> 1 (11)^(j+1+3n)`. -/
theorem sweeps (n j m : Nat) (L : Tape) : ∃ t,
    steps t ⟨rep (m + 2 * n) [false, true] L, cons true (rep (j + 1) [true, true] blank), .C⟩ =
      some ⟨rep m [false, true] L, cons true (rep (j + 1 + 3 * n) [true, true] blank), .C⟩ := by
  induction n generalizing j with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    have h1 := sweep j (m + 2 * n) L
    rw [ones_shift] at h1
    have e1 : m + 2 * (n + 1) = m + 2 * n + 2 := by omega
    obtain ⟨t, h2⟩ := ih (j + 3)
    have e2 : j + 3 + 1 + 3 * n = j + 1 + 3 * (n + 1) := by omega
    rw [e2] at h2
    exact ⟨_, e1 ▸ steps_seq trans h1 h2⟩

theorem K_e_even (n : Nat) : ∃ t, steps t (K blank (2 * n)) = some (K (cons true blank) (3 * n + 4)) := by
  obtain ⟨t, h1⟩ := sweeps n 1 0 blank
  have e : 1 + 1 + 3 * n = 3 * n + 2 := by omega
  rw [e, Nat.zero_add] at h1
  have h2 := end_e0 (3 * n)
  refine ⟨_, steps_seq trans h1 (h2.trans ?_)⟩
  unfold K; congr 2
  rw [show 3 * n + 4 = (3 * n + 1) + 3 from rfl, rep_add (3 * n + 1) 3]; rfl

theorem K_e_odd (n : Nat) : ∃ t, steps t (K blank (2 * n + 1)) = some (K blank (3 * n + 7)) := by
  obtain ⟨t, h1⟩ := sweeps n 1 1 blank
  have e : 1 + 1 + 3 * n = 3 * n + 2 := by omega
  rw [e, Nat.add_comm 1 (2 * n)] at h1
  have h2 := end_e1 (3 * n)
  refine ⟨_, steps_seq trans h1 (h2.trans ?_)⟩
  unfold K; congr 2
  show app [false] (rep (3 * n + 1) [true, false] _) = _
  rw [rep_rotate (3 * n + 1) [false] [true, false] [false, true] rfl]
  rw [show 3 * n + 7 = (3 * n + 1) + 6 from rfl, rep_add (3 * n + 1) 6]; rfl

theorem K_1_even (n : Nat) : ∃ t, steps t (K (cons true blank) (2 * n)) = some (K blank (3 * n + 4)) := by
  obtain ⟨t, h1⟩ := sweeps n 1 0 (cons true blank)
  have e : 1 + 1 + 3 * n = 3 * n + 2 := by omega
  rw [e, Nat.zero_add] at h1
  have h2 := end_10 (3 * n)
  refine ⟨_, steps_seq trans h1 (h2.trans ?_)⟩
  unfold K; congr 2
  show app [false] (rep (3 * n + 1) [true, false] _) = _
  rw [rep_rotate (3 * n + 1) [false] [true, false] [false, true] rfl]
  rw [show 3 * n + 4 = (3 * n + 1) + 3 from rfl, rep_add (3 * n + 1) 3]; rfl

/-- The prefix `1000` (left to right), as a left tape. -/
def P1000 : Tape := cons false (cons false (cons false (cons true blank)))

theorem K_1_odd (n : Nat) : ∃ t, steps t (K (cons true blank) (2 * n + 1)) = some (K P1000 (3 * n + 4)) := by
  obtain ⟨t, h1⟩ := sweeps n 1 1 (cons true blank)
  have e : 1 + 1 + 3 * n = 3 * n + 2 := by omega
  rw [e, Nat.add_comm 1 (2 * n)] at h1
  have h2 := end_11 (3 * n)
  refine ⟨_, steps_seq trans h1 (h2.trans ?_)⟩
  unfold K; congr 2
  rw [show 3 * n + 4 = (3 * n + 1) + 3 from rfl, rep_add (3 * n + 1) 3]; rfl

/-- From blank tape the run reaches the sample `K 1 1` (`0^inf 1 1 0 C> 1 1 1 1 1`) after 30 steps. -/
theorem blank_K : steps 30 init = some (K (cons true blank) 1) := start

end H119593
