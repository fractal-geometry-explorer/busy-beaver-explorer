import Formula

/-!
# `pre` at its A states: the carry, and where a token can appear

At A with no ones under the head, `pre` eats the first two words `0 1^w` in front of it (`py/tokens.py`).  Only the
pair `1, 2` writes new words: A turns the `1` into a block, B turns the pair into `0, 3` (`a_one_two`), and the
converter runs left through the blocks that are `1 mod 3`, each block `3j + 1` becoming the words `1, 2^j`
(`carry`).  Where it stops decides the rest.  Two of the ways it can stop are proved here, kernel only:

* at a block `3m + 3` with blocks `c, d` behind it (`row_zero`): the blocks become `c + 3, d + 2` and the words in front
  are `2^m`, the converted words, `3`, and the old words.
* past the leftmost block, every block having been `1 mod 3` (`row_end`): two new blocks `2, 2` at the left end.

Count the *tokens*: words other than 2 and nonzero blocks.  In `row_zero` the count does not go up when `d ≠ 0`, and
goes down by one when also `c ≠ 0` (`row_zero_tokens`); `row_end` raises it by exactly one (`row_end_tokens`).  The
tape grows at the left end only in the second case and in `row_zero` with `c` or `d` zero.  The pairs that write no
words: `2 1` (`two_one`), `2 3` (`two_three`), `3 2` (`three_two`), and `2 2` is `tail_two`.
-/

namespace BB6c

open TM

/-- The words `1, 2^j` that a block `3j + 1` becomes. -/
def cw (j : Nat) : List Nat := tw 1 j 0

/-- The words the converter leaves for the blocks `3 j₁ + 1, …` (nearest first): the farthest block's words first. -/
def carryW : List Nat → List Nat
  | [] => []
  | j :: js => carryW js ++ cw j

/-- The blocks `3j + 1`. -/
def ones1 (js : List Nat) : List Nat := js.map (fun j => 3 * j + 1)

/-- **The carry** (kernel only): B before a word `0`, at blocks `3 j_i + 1` and then a block `b`, goes left over them,
each becoming the words `1, 2^{j_i}`. -/
theorem carry (b : Nat) (L : List Nat) : ∀ (js : List Nat) (W : List Nat),
    Reaches (enc ⟨.B, 0, ones1 js ++ b :: L, 0 :: W⟩) (enc ⟨.B, 0, b :: L, 0 :: (carryW js ++ W)⟩)
  | [], W => ⟨0, rfl⟩
  | j :: js, W => by
    obtain ⟨c, M, hr⟩ : ∃ c M, ones1 js ++ b :: L = c :: M := by
      cases js with
      | nil => exact ⟨b, L, rfl⟩
      | cons j' js' => exact ⟨3 * j' + 1, ones1 js' ++ b :: L, rfl⟩
    have h₁ := s_b_one c j 0 M W
    rw [← hr] at h₁
    have h₂ := carry b L js (tw 1 j 0 ++ W)
    have e : carryW js ++ (tw 1 j 0 ++ W) = carryW (j :: js) ++ W := by
      simp [carryW, cw, List.append_assoc]
    rw [e] at h₂
    exact h₁.trans h₂

/-- A before the words `1, 2`: B before `0, 3` at the same blocks. -/
theorem a_one_two (a : Nat) (M W : List Nat) :
    Reaches (enc ⟨.A, 0, a :: M, 1 :: 2 :: W⟩) (enc ⟨.B, 0, a :: M, 0 :: 3 :: W⟩) := by
  have h₁ := s_a_tok 0 (a :: M) (2 :: W)
  have h₂ := s_b_one a 0 2 M W
  exact h₁.trans h₂

theorem tw_one_succ (m : Nat) : tw 1 (m + 1) 0 = 1 :: 2 :: twos m := by
  show 1 :: tw 2 m 0 = _
  rw [tw_two]; rfl

/-- **The carry stops at a block `3m + 3`** (kernel only). -/
theorem row_zero (js : List Nat) (m c d : Nat) (M R : List Nat) :
    Reaches (enc ⟨.A, 0, ones1 js ++ (3 * (m + 1)) :: c :: d :: M, 1 :: 2 :: R⟩)
      (enc ⟨.A, 0, (c + 3) :: (d + 2) :: M, twos m ++ carryW js ++ 3 :: R⟩) := by
  obtain ⟨a, M₀, hr⟩ : ∃ a M₀, ones1 js ++ (3 * (m + 1)) :: c :: d :: M = a :: M₀ := by
    cases js with
    | nil => exact ⟨_, _, rfl⟩
    | cons j js => exact ⟨_, _, rfl⟩
  have h₁ := a_one_two a M₀ R
  rw [← hr] at h₁
  have h₂ := carry (3 * (m + 1)) (c :: d :: M) js (3 :: R)
  have h₃ := s_b_zero c (m + 1) (d :: M) (carryW js ++ 3 :: R)
  rw [tw_one_succ] at h₃
  have h₄ := s_c_move 2 (d :: M) (twos m ++ (carryW js ++ 3 :: R)) c
  have h₅ := s_c_one d M ((2 + c) :: (twos m ++ (carryW js ++ 3 :: R)))
  have h₆ := s_f_tok (2 + c) 0 ((d + 2) :: M) (twos m ++ (carryW js ++ 3 :: R))
  rw [show 0 + (2 + c) + 1 = c + 3 by omega] at h₆
  have h₃' : Reaches (enc ⟨.B, 0, (3 * (m + 1)) :: c :: d :: M, 0 :: (carryW js ++ 3 :: R)⟩)
      (enc ⟨.C, 0, c :: d :: M, 1 :: 2 :: (twos m ++ (carryW js ++ 3 :: R))⟩) := by
    simpa [List.append_assoc] using h₃
  have := h₁.trans (h₂.trans (h₃'.trans (h₄.trans (h₅.trans h₆))))
  simpa [List.append_assoc] using this

/-- **The carry runs past the leftmost block** (kernel only): all blocks `1 mod 3`, the last `3j + 1`, and blank tape
beyond; two new blocks `2, 2` at the left end. -/
theorem row_end (js : List Nat) (j : Nat) (R : List Nat) :
    Reaches (enc ⟨.A, 0, ones1 js ++ [3 * j + 1, 0, 0, 0], 1 :: 2 :: R⟩)
      (enc ⟨.A, 0, [2, 2, 0], twos j ++ carryW js ++ 3 :: R⟩) := by
  obtain ⟨a, M₀, hr⟩ : ∃ a M₀, ones1 js ++ [3 * j + 1, 0, 0, 0] = a :: M₀ := by
    cases js with
    | nil => exact ⟨_, _, rfl⟩
    | cons j js => exact ⟨_, _, rfl⟩
  have h₁ := a_one_two a M₀ R
  rw [← hr] at h₁
  have h₂ := carry (3 * j + 1) [0, 0, 0] js (3 :: R)
  have e : tw 1 j 0 = 1 :: twos j := by
    cases j with
    | zero => rfl
    | succ j => rw [tw_one_succ]; rfl
  have h₃ := s_b_one 0 j 0 [0, 0] (carryW js ++ 3 :: R)
  rw [e] at h₃
  have h₄ : Reaches (enc ⟨.B, 0, [0, 0, 0], 0 :: (1 :: twos j ++ (carryW js ++ 3 :: R))⟩)
      (enc ⟨.C, 0, [0, 0], 1 :: (1 :: twos j ++ (carryW js ++ 3 :: R))⟩) :=
    s_b_zero 0 0 [0] (1 :: twos j ++ (carryW js ++ 3 :: R))
  have h₅ := s_c_one 0 [] (1 :: twos j ++ (carryW js ++ 3 :: R))
  have h₆ := s_f_tok 1 0 [0 + 2] (twos j ++ (carryW js ++ 3 :: R))
  have h₇ : enc ⟨.A, 0, [0 + 1 + 1, 0 + 2], twos j ++ (carryW js ++ 3 :: R)⟩ =
      enc ⟨.A, 0, [2, 2, 0], twos j ++ carryW js ++ 3 :: R⟩ := by
    simp only [enc, lt, rep_zero, cons_false_blank, List.append_assoc]
  have := h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆))))
  rw [h₇] at this
  exact this

/-- **The carry stops at a block `3m + 8`** (kernel only): the blocks become `3, c + 6`. -/
theorem row_two (js : List Nat) (m c : Nat) (M R : List Nat) :
    Reaches (enc ⟨.A, 0, ones1 js ++ (3 * m + 8) :: c :: M, 1 :: 2 :: R⟩)
      (enc ⟨.A, 0, 3 :: (c + 6) :: M, twos m ++ carryW js ++ 3 :: R⟩) := by
  obtain ⟨a, M₀, hr⟩ : ∃ a M₀, ones1 js ++ (3 * m + 8) :: c :: M = a :: M₀ := by
    cases js with
    | nil => exact ⟨_, _, rfl⟩
    | cons j js => exact ⟨_, _, rfl⟩
  have h₁ := a_one_two a M₀ R
  rw [← hr] at h₁
  have h₂ := carry (3 * m + 8) (c :: M) js (3 :: R)
  have h₃ := s_b_two c (m + 1) 0 M (carryW js ++ 3 :: R)
  rw [show 3 * (m + 1) + 5 = 3 * m + 8 by omega, tw_two] at h₃
  have h₄ := s_e_two (c + 3) M (2 :: (twos m ++ (carryW js ++ 3 :: R)))
  have h₅ := s_f_tok 2 0 ((c + 3 + 3) :: M) (twos m ++ (carryW js ++ 3 :: R))
  have e : twos (m + 1 + 1) ++ (carryW js ++ 3 :: R) = 2 :: 2 :: (twos m ++ (carryW js ++ 3 :: R)) := by
    simp [twos, List.replicate_succ]
  rw [e] at h₃
  rw [show c + 3 + 3 = c + 6 by omega] at h₄ h₅
  have := h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
  simpa [List.append_assoc] using this

/-! ## The pairs that write no words -/

/-- `2, 1`: the blocks `a, b` gain 3 and 2. -/
theorem two_one (a b : Nat) (M R : List Nat) :
    Reaches (enc ⟨.A, 0, a :: b :: M, 2 :: 1 :: R⟩) (enc ⟨.A, 0, (a + 3) :: (b + 2) :: M, R⟩) := by
  have h₁ := s_a_tok 1 (a :: b :: M) (1 :: R)
  have h₂ := s_b_one 0 0 1 (a :: b :: M) R
  have h₃ := s_b_zero a 0 (b :: M) (tw 1 0 1 ++ R)
  have h₄ := s_c_move 2 (b :: M) R a
  have h₅ := s_c_one b M ((2 + a) :: R)
  have h₆ := s_f_tok (2 + a) 0 ((b + 2) :: M) R
  rw [show 0 + (2 + a) + 1 = a + 3 by omega] at h₆
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆))))

/-- `2, 3`: the blocks `a, b` gain 5 and 2. -/
theorem two_three (a b : Nat) (M R : List Nat) :
    Reaches (enc ⟨.A, 0, a :: b :: M, 2 :: 3 :: R⟩) (enc ⟨.A, 0, (a + 5) :: (b + 2) :: M, R⟩) := by
  have h₁ := s_a_tok 1 (a :: b :: M) (3 :: R)
  have h₂ := s_b_one 0 0 3 (a :: b :: M) R
  have h₃ := s_b_zero a 0 (b :: M) (tw 1 0 3 ++ R)
  have h₄ := s_c_move 4 (b :: M) R a
  have h₅ := s_c_one b M ((4 + a) :: R)
  have h₆ := s_f_tok (4 + a) 0 ((b + 2) :: M) R
  rw [show 0 + (4 + a) + 1 = a + 5 by omega] at h₆
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆))))

/-- `3, 2`: a new block 4 in front of the block `a`, which gains 2. -/
theorem three_two (a : Nat) (M R : List Nat) :
    Reaches (enc ⟨.A, 0, a :: M, 3 :: 2 :: R⟩) (enc ⟨.A, 0, 4 :: (a + 2) :: M, R⟩) := by
  have h₁ := s_a_tok 2 (a :: M) (2 :: R)
  have h₂ := s_b_one 0 0 2 (0 :: a :: M) R
  have h₃ := s_b_zero 0 0 (a :: M) (tw 1 0 2 ++ R)
  have h₄ := s_c_one a M (tw 1 0 2 ++ R)
  have h₅ := s_f_tok 3 0 ((a + 2) :: M) R
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-! ## Tokens -/

/-- Words other than 2. -/
def irrW (W : List Nat) : Nat := (W.filter (· != 2)).length

/-- Nonzero blocks. -/
def nzL (L : List Nat) : Nat := (L.filter (· != 0)).length

theorem irrW_append (A B : List Nat) : irrW (A ++ B) = irrW A + irrW B := by
  simp [irrW, List.filter_append]

theorem irrW_twos (m : Nat) : irrW (twos m) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [irrW, twos, List.replicate_succ] at ih ⊢

theorem irrW_cw (j : Nat) : irrW (cw j) = 1 := by
  cases j with
  | zero => rfl
  | succ j =>
    show irrW (1 :: tw 2 j 0) = 1
    rw [tw_two]; have := irrW_twos (j + 1); simp [irrW] at this ⊢

theorem irrW_carryW : ∀ js : List Nat, irrW (carryW js) = js.length
  | [] => rfl
  | j :: js => by simp [carryW, irrW_append, irrW_carryW js, irrW_cw]

theorem nzL_ones1_append (js L : List Nat) : nzL (ones1 js ++ L) = js.length + nzL L := by
  induction js with
  | nil => simp [ones1]
  | cons j js ih => simp [ones1, nzL, List.filter_append] at ih ⊢; omega

/-- **Tokens at `row_zero`** (kernel only): they do not go up when `d ≠ 0`, and go down by one when also `c ≠ 0`. -/
theorem row_zero_tokens (js : List Nat) (m c d : Nat) (M R : List Nat) :
    nzL ((c + 3) :: (d + 2) :: M) + irrW (twos m ++ carryW js ++ 3 :: R) + (if c = 0 then 0 else 1) +
        (if d = 0 then 0 else 1) =
      nzL (ones1 js ++ (3 * (m + 1)) :: c :: d :: M) + irrW (1 :: 2 :: R) + 1 := by
  rw [nzL_ones1_append, irrW_append, irrW_append, irrW_twos, irrW_carryW]
  by_cases hc : c = 0 <;> by_cases hd : d = 0 <;> simp [nzL, irrW, hc, hd] <;> omega

/-- **Tokens at `row_end`** (kernel only): exactly one more. -/
theorem row_end_tokens (js : List Nat) (j : Nat) (R : List Nat) :
    nzL [2, 2, 0] + irrW (twos j ++ carryW js ++ 3 :: R) =
      nzL (ones1 js ++ [3 * j + 1, 0, 0, 0]) + irrW (1 :: 2 :: R) + 1 := by
  rw [nzL_ones1_append, irrW_append, irrW_append, irrW_twos, irrW_carryW]
  simp [nzL, irrW]; omega

/-- **Tokens at `row_two`** (kernel only): one more when `c = 0` (the tape grows), the same otherwise. -/
theorem row_two_tokens (js : List Nat) (m c : Nat) (M R : List Nat) :
    nzL (3 :: (c + 6) :: M) + irrW (twos m ++ carryW js ++ 3 :: R) + (if c = 0 then 0 else 1) =
      nzL (ones1 js ++ (3 * m + 8) :: c :: M) + irrW (1 :: 2 :: R) + 1 := by
  rw [nzL_ones1_append, irrW_append, irrW_append, irrW_twos, irrW_carryW]
  by_cases hc : c = 0 <;> simp [nzL, irrW, hc] <;> omega

end BB6c
