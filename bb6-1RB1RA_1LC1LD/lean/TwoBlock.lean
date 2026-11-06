import Tokens

/-!
# The recursive pass after a single block, in closed form

`py/twoblock.py` (`pre1`) gives `pre` for one block `x` left of a last block `3j` in closed form, by `x mod 18`.
Here those formulas are proved, kernel only, as statements about the machine: the pass from `K [x] (3j - 1)` reaches
the next pass start given by the formula, for every `j ≥ 1` (or `j ≥ u`).  Most of the run is on two-block tapes
`1^x 0 1^b A>0` (`notes/LAB_NOTES.md`, 5 November), so with `next_sound` these make the two-block map explicit.
-/

namespace BB6c

open TM

theorem lt_snoc0 : ∀ L : List Nat, lt (L ++ [0]) = lt L
  | [] => by simp only [List.nil_append, lt, rep_zero, cons_false_blank]
  | a :: L => by
    show rep a [true] (cons false (lt (L ++ [0]))) = rep a [true] (cons false (lt L))
    rw [lt_snoc0 L]

/-- Empty blocks at the far left are blank tape. -/
theorem enc_snoc0 (q : St) (h : Nat) (L W : List Nat) : enc ⟨q, h, L, W⟩ = enc ⟨q, h, L ++ [0], W⟩ := by
  unfold enc; rw [lt_snoc0]

theorem K_snoc0 (L : List Nat) (n : Nat) : K L n = K (L ++ [0]) n := by
  unfold K; rw [lt_snoc0]

theorem twos_succ' (m : Nat) : twos (m + 1) = 2 :: twos m := rfl

theorem K_one0 (y n : Nat) : K [y, 0] n = K [y] n := (K_snoc0 [y] n).symm

/-- **`x ≡ 0 (mod 6)`**: after a single block `6(q + 1)`, a last block `3j` becomes `2x/3 + 2 + 2j`, the block left of
it `x/3 + 2 + 2⌈j/2⌉` (kernel only). -/
theorem one_zero6 (q i : Nat) :
    Reaches (K [6 * (q + 1)] (3 * i + 2))
      (K [2 * q + 4 + 2 * ((i + 2) / 2)] (4 * q + 6 + 2 * (i + 1) - 1)) := by
  have h₀ := s_k_start (6 * (q + 1)) i []
  rw [tw_two, enc_snoc0, enc_snoc0] at h₀
  have h₁ := s_b_zero 0 (2 * (q + 1)) [0] (1 :: twos (i + 1))
  rw [show 3 * (2 * (q + 1)) = 6 * (q + 1) by omega] at h₁
  have h₂ := s_c_one 0 [] (2 :: (twos (2 * q + 1) ++ 1 :: twos (i + 1)))
  have h₃ := s_f_tok 2 0 [0 + 2] (twos (2 * q + 1) ++ 1 :: twos (i + 1))
  have h₄ := tail_iter [] (2 :: 1 :: twos (i + 1)) q (0 + 2 + 1) (0 + 2)
  have h₅ := two_one (0 + 2 + 1 + 4 * q) (0 + 2 + 2 * q) [] (twos (i + 1))
  have h₆ := tail_end (0 + 2 + 1 + 4 * q + 3) (0 + 2 + 2 * q + 2) [] (i + 1) (by omega)
  have e₁ : tw 1 (2 * (q + 1)) 0 ++ 1 :: twos (i + 1) = 1 :: 2 :: (twos (2 * q + 1) ++ 1 :: twos (i + 1)) := by
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 by omega, tw_one_succ]; rfl
  have e₂ : twos (2 * q + 1) ++ 1 :: twos (i + 1) = twos (2 * q) ++ 2 :: 1 :: twos (i + 1) := by
    rw [show twos (2 * q + 1) = twos (2 * q) ++ [2] from List.replicate_succ' ..]; simp
  rw [e₁] at h₁
  rw [← e₂] at h₄
  rw [show (0 + 2 + 1 + 4 * q + 3) = 4 * q + 6 by omega, show 0 + 2 + 2 * q + 2 = 2 * q + 4 by omega,
    show i + 1 + 1 = i + 2 from rfl] at h₆
  rw [show (0 + 2 + 1 + 4 * q + 3) = 4 * q + 6 by omega, show 0 + 2 + 2 * q + 2 = 2 * q + 4 by omega] at h₅
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆)))))

theorem twos_odd (q : Nat) (R : List Nat) : twos (2 * q + 1) ++ R = twos (2 * q) ++ 2 :: R := by
  rw [show twos (2 * q + 1) = twos (2 * q) ++ [2] from List.replicate_succ' ..]; simp

/-- **`x ≡ 4 (mod 6)`**: after a single block `6q + 4`, a last block `3j` becomes `(2x + 7)/3 + 2j`, the block left
of it `(x + 8)/3 + 2⌈j/2⌉` (kernel only). -/
theorem one_four6 (q i : Nat) :
    Reaches (K [6 * q + 4] (3 * i + 2))
      (K [2 * q + 4 + 2 * ((i + 2) / 2)] (4 * q + 5 + 2 * (i + 1) - 1)) := by
  have h₀ := s_k_start (6 * q + 4) i []
  rw [tw_two, enc_snoc0, enc_snoc0] at h₀
  have h₁ := s_b_one 0 (2 * q + 1) 0 [0] (1 :: twos (i + 1))
  rw [show 3 * (2 * q + 1) + 1 = 6 * q + 4 by omega] at h₁
  have h₂ := s_b_zero 0 0 [] (tw 1 (2 * q + 1) 0 ++ 1 :: twos (i + 1))
  rw [show 3 * 0 = 0 from rfl, enc_snoc0 .C] at h₂
  have h₃ := s_c_one 0 [] (tw 1 (2 * q + 1) 0 ++ 1 :: twos (i + 1))
  have h₄ := s_f_tok 1 0 [0 + 2] (twos (2 * q + 1) ++ 1 :: twos (i + 1))
  have h₅ := tail_iter [] (2 :: 1 :: twos (i + 1)) q (0 + 1 + 1) (0 + 2)
  rw [← twos_odd] at h₅
  have h₆ := two_one (0 + 1 + 1 + 4 * q) (0 + 2 + 2 * q) [] (twos (i + 1))
  have h₇ := tail_end (0 + 1 + 1 + 4 * q + 3) (0 + 2 + 2 * q + 2) [] (i + 1) (by omega)
  rw [show 0 + 1 + 1 + 4 * q + 3 = 4 * q + 5 by omega, show 0 + 2 + 2 * q + 2 = 2 * q + 4 by omega,
    show i + 1 + 1 = i + 2 from rfl] at h₇
  rw [show 0 + 1 + 1 + 4 * q + 3 = 4 * q + 5 by omega, show 0 + 2 + 2 * q + 2 = 2 * q + 4 by omega] at h₆
  have e : tw 1 (2 * q + 1) 0 ++ 1 :: twos (i + 1) = 1 :: (twos (2 * q + 1) ++ 1 :: twos (i + 1)) := by
    rw [tw_one_succ]; rfl
  rw [e] at h₁ h₂ h₃
  rw [show tw 1 0 0 = [1] from rfl] at h₂
  simp only [List.cons_append, List.nil_append] at h₂
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans h₇))))))

/-- **`x ≡ 5 (mod 6)`, x ≥ 11**: after a single block `6q + 11`, a last block `3j` becomes `(2x - 4)/3 + 2j`, the
block left of it `(x + 13)/3 + 2⌈j/2⌉` (kernel only). -/
theorem one_five6 (q i : Nat) :
    Reaches (K [6 * q + 11] (3 * i + 2))
      (K [2 * q + 8 + 2 * ((i + 2) / 2)] (4 * q + 6 + 2 * (i + 1) - 1)) := by
  have h₀ := s_k_start (6 * q + 11) i []
  rw [tw_two, enc_snoc0, enc_snoc0] at h₀
  have h₁ := s_b_two 0 (2 * q + 2) 0 [0] (1 :: twos (i + 1))
  rw [show 3 * (2 * q + 2) + 5 = 6 * q + 11 by omega, tw_two] at h₁
  have h₂ := s_e_two (0 + 3) [0] (twos (2 * q + 2) ++ 1 :: twos (i + 1))
  have h₃ := s_f_tok 2 0 [0 + 3 + 3, 0] (twos (2 * q + 1) ++ 1 :: twos (i + 1))
  have h₄ := tail_iter [0] (2 :: 1 :: twos (i + 1)) q (0 + 2 + 1) (0 + 3 + 3)
  rw [← twos_odd] at h₄
  have h₅ := two_one (0 + 2 + 1 + 4 * q) (0 + 3 + 3 + 2 * q) [0] (twos (i + 1))
  have h₆ := tail_end (0 + 2 + 1 + 4 * q + 3) (0 + 3 + 3 + 2 * q + 2) [0] (i + 1) (by omega)
  rw [show 0 + 2 + 1 + 4 * q + 3 = 4 * q + 6 by omega, show 0 + 3 + 3 + 2 * q + 2 = 2 * q + 8 by omega,
    show i + 1 + 1 = i + 2 from rfl, K_one0] at h₆
  rw [show 0 + 2 + 1 + 4 * q + 3 = 4 * q + 6 by omega, show 0 + 3 + 3 + 2 * q + 2 = 2 * q + 8 by omega] at h₅
  have e : twos (2 * q + 2 + 1) ++ 1 :: twos (i + 1) = 2 :: (twos (2 * q + 2) ++ 1 :: twos (i + 1)) := rfl
  rw [e] at h₁
  have e' : twos (2 * q + 2) ++ 1 :: twos (i + 1) = 2 :: (twos (2 * q + 1) ++ 1 :: twos (i + 1)) := rfl
  rw [e'] at h₂
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆)))))

/-! ## `x ≡ 2 (mod 6)`: a second sweep -/

/-- The first sweep after a single block `6q + 8`: A before the block `4q + 3` and the word 1 (kernel only). -/
theorem one_two6_sweep (q : Nat) (R : List Nat) :
    Reaches (enc ⟨.B, 0, [6 * q + 8, 0, 0], 0 :: 1 :: R⟩) (enc ⟨.A, 0, [4 * q + 3, 2 * q + 6, 0], 1 :: R⟩) := by
  have h₁ := s_b_two 0 (2 * q + 1) 0 [0] (1 :: R)
  rw [show 3 * (2 * q + 1) + 5 = 6 * q + 8 by omega, tw_two] at h₁
  have h₂ := s_e_two (0 + 3) [0] (twos (2 * q + 1) ++ 1 :: R)
  have h₃ := s_f_tok 2 0 [0 + 3 + 3, 0] (twos (2 * q) ++ 1 :: R)
  have h₄ := tail_iter [0] (1 :: R) q (0 + 2 + 1) (0 + 3 + 3)
  rw [show 0 + 2 + 1 + 4 * q = 4 * q + 3 by omega, show 0 + 3 + 3 + 2 * q = 2 * q + 6 by omega] at h₄
  exact h₁.trans (h₂.trans (h₃.trans h₄))

theorem K_start1 (x i : Nat) : Reaches (K [x] (3 * i + 2)) (enc ⟨.B, 0, [x, 0, 0], 0 :: 1 :: twos (i + 1)⟩) := by
  have h₀ := s_k_start x i []
  rw [tw_two, enc_snoc0, enc_snoc0] at h₀
  exact h₀

/-- **`x ≡ 2 (mod 18)`, x ≥ 20**: one supply word; a last block `3j` becomes `(4x - 26)/9 + 2j`, the block left of it
`(5x + 62)/9 + 2⌈(j - 1)/2⌉` (kernel only). -/
theorem one_two18 (r i : Nat) :
    Reaches (K [18 * r + 20] (3 * i + 2)) (K [10 * r + 18 + 2 * ((i + 1) / 2)] (8 * r + 8 + 2 * i - 1)) := by
  have h₀ := K_start1 (18 * r + 20) i
  have h₁ := one_two6_sweep (3 * r + 2) (twos (i + 1))
  rw [show 6 * (3 * r + 2) + 8 = 18 * r + 20 by omega, show 4 * (3 * r + 2) + 3 = 3 * (4 * r + 2) + 5 by omega,
    show 2 * (3 * r + 2) + 6 = 6 * r + 10 by omega] at h₁
  have h₂ := a_one_two (3 * (4 * r + 2) + 5) [6 * r + 10, 0] (twos i)
  have h₃ := s_b_two (6 * r + 10) (4 * r + 2) 0 [0] (3 :: twos i)
  rw [tw_two] at h₃
  have h₄ := s_e_two (6 * r + 10 + 3) [0] (twos (4 * r + 2) ++ 3 :: twos i)
  have h₅ := s_f_tok 2 0 [6 * r + 10 + 3 + 3, 0] (twos (4 * r + 1) ++ 3 :: twos i)
  have h₆ := tail_iter [0] (2 :: 3 :: twos i) (2 * r) (0 + 2 + 1) (6 * r + 10 + 3 + 3)
  rw [← twos_odd, show 2 * (2 * r) = 4 * r by omega] at h₆
  have h₇ := two_three (0 + 2 + 1 + 4 * (2 * r)) (6 * r + 10 + 3 + 3 + 4 * r) [0] (twos i)
  rw [show 0 + 2 + 1 + 4 * (2 * r) + 5 = 8 * r + 8 by omega,
    show 6 * r + 10 + 3 + 3 + 4 * r + 2 = 10 * r + 18 by omega] at h₇
  have h₈ := tail_end (8 * r + 8) (10 * r + 18) [0] i (by omega)
  rw [K_one0] at h₈
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans (h₇.trans h₈)))))))

/-- **`x ≡ 8 (mod 18)`**: offset 0 with two supply words; a last block `3j`, `j ≥ 2`, becomes `2j`, with the blocks
`(2x + 2)/9` and `(7x + 43)/9 + 2⌈(j - 2)/2⌉` to its left (kernel only). -/
theorem one_eight18 (r i : Nat) :
    Reaches (K [18 * r + 8] (3 * (i + 1) + 2))
      (K [14 * r + 11 + 2 * ((i + 1) / 2), 4 * r + 2] (4 + 2 * i - 1)) := by
  have h₀ := K_start1 (18 * r + 8) (i + 1)
  have h₁ := one_two6_sweep (3 * r) (twos (i + 2))
  rw [show 6 * (3 * r) + 8 = 18 * r + 8 by omega, show 4 * (3 * r) + 3 = 3 * (4 * r + 1) by omega,
    show 2 * (3 * r) + 6 = 6 * r + 6 by omega] at h₁
  have h₂ := a_one_two (3 * (4 * r + 1)) [6 * r + 6, 0] (twos (i + 1))
  have h₃ := s_b_zero (6 * r + 6) (4 * r + 1) [0] (3 :: twos (i + 1))
  rw [tw_one_succ] at h₃
  have h₄ := s_c_move 2 [0] (twos (4 * r) ++ 3 :: twos (i + 1)) (6 * r + 6)
  have h₅ := s_c_one 0 [] ((2 + (6 * r + 6)) :: (twos (4 * r) ++ 3 :: twos (i + 1)))
  have h₆ := s_f_tok (2 + (6 * r + 6)) 0 [0 + 2] (twos (4 * r) ++ 3 :: twos (i + 1))
  have h₇ := tail_iter [] (3 :: twos (i + 1)) (2 * r) (0 + (2 + (6 * r + 6)) + 1) (0 + 2)
  rw [show 2 * (2 * r) = 4 * r by omega, show 0 + 2 + 4 * r = 4 * r + 2 by omega] at h₇
  have h₈ := three_two (0 + (2 + (6 * r + 6)) + 1 + 4 * (2 * r)) [0 + 2 + 4 * r] (twos i)
  rw [show 0 + (2 + (6 * r + 6)) + 1 + 4 * (2 * r) + 2 = 14 * r + 11 by omega,
    show 0 + 2 + 4 * r = 4 * r + 2 by omega] at h₈
  have h₉ := tail_end 4 (14 * r + 11) [4 * r + 2] i (by omega)
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans (h₇.trans (h₈.trans h₉))))))))

/-! ## `x ≡ 14 (mod 18)`: a carry down the powers of 3 -/

theorem twos_split (n q : Nat) (h : n = 2 * q + 1) (R : List Nat) : twos n ++ R = twos (2 * q) ++ 2 :: R := by
  subst h; exact twos_odd q R

theorem twos_even (n q : Nat) (h : n = 2 * q) (R : List Nat) : twos n ++ R = twos (2 * q) ++ R := by subst h; rfl

/-- The result of a level of the carry for a block `6r + 8` before the words `0, 1, 2^(4r+2), 3`: whether a word 3 is
left in front (`true`, the blocks grow by one each level) or not, and the blocks `a :: b :: M` left of A.  A level
with `r ≡ 1 (mod 3)` hands on to a block `6(r/3) + 8`. -/
def g14 (r : Nat) : Bool × Nat × Nat × List Nat :=
  if r % 3 = 2 then (false, 32 * (r / 3) + 29, 22 * (r / 3) + 28, [0])
  else if r % 3 = 0 then (true, 24 * (r / 3) + 4, 26 * (r / 3) + 11, [4 * (r / 3) + 2])
  else
    match g14 (r / 3) with
    | (false, a, b, M) => (false, a + 24 * (r / 3) + 13, b + 12 * (r / 3) + 6, M)
    | (true, a, b, M) => (true, 24 * (r / 3) + 12, a + 12 * (r / 3) + 6, b :: M)
termination_by r
decreasing_by omega

theorem g14_two (m : Nat) : g14 (3 * m + 2) = (false, 32 * m + 29, 22 * m + 28, [0]) := by
  rw [g14]; simp only [show (3 * m + 2) % 3 = 2 by omega, show (3 * m + 2) / 3 = m by omega, ite_true]

theorem g14_zero (m : Nat) : g14 (3 * m) = (true, 24 * m + 4, 26 * m + 11, [4 * m + 2]) := by
  rw [g14]; simp only [show (3 * m) % 3 = 0 by omega, show (3 * m) / 3 = m by omega]; simp

theorem g14_one (m : Nat) : g14 (3 * m + 1) =
    match g14 m with
    | (false, a, b, M) => (false, a + 24 * m + 13, b + 12 * m + 6, M)
    | (true, a, b, M) => (true, 24 * m + 12, a + 12 * m + 6, b :: M) := by
  rw [g14]; simp only [show (3 * m + 1) % 3 = 1 by omega, show (3 * m + 1) / 3 = m by omega]; simp

/-- The start of a level: B at a block `6r + 8`, then A at `4r + 3` before `1, 2, …`, then B before `0, 3`. -/
theorem lvl_start (r : Nat) (Rest : List Nat) :
    Reaches (enc ⟨.B, 0, [6 * r + 8, 0, 0], 0 :: 1 :: (twos (4 * r + 2) ++ 3 :: Rest)⟩)
      (enc ⟨.B, 0, [4 * r + 3, 2 * r + 6, 0], 0 :: 3 :: (twos (4 * r + 1) ++ 3 :: Rest)⟩) := by
  have h₁ := one_two6_sweep r (twos (4 * r + 2) ++ 3 :: Rest)
  have h₂ := a_one_two (4 * r + 3) [2 * r + 6, 0] (twos (4 * r + 1) ++ 3 :: Rest)
  exact h₁.trans h₂

/-- **One level of the carry** (kernel only), by strong induction on `r`. -/
theorem lvl : ∀ (r : Nat) (Rest : List Nat),
    Reaches (enc ⟨.B, 0, [6 * r + 8, 0, 0], 0 :: 1 :: (twos (4 * r + 2) ++ 3 :: Rest)⟩)
      (enc ⟨.A, 0, (g14 r).2.1 :: (g14 r).2.2.1 :: (g14 r).2.2.2, if (g14 r).1 then 3 :: Rest else Rest⟩) := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
  intro Rest
  obtain ⟨m, rfl | rfl | rfl⟩ : ∃ m, r = 3 * m ∨ r = 3 * m + 1 ∨ r = 3 * m + 2 := ⟨r / 3, by omega⟩
  · -- r = 3m: a block 3(4m + 1), as for x ≡ 8 (mod 18)
    rw [g14_zero]
    have h₀ := lvl_start (3 * m) Rest
    rw [show 4 * (3 * m) + 3 = 3 * (4 * m + 1) by omega, show 2 * (3 * m) + 6 = 6 * m + 6 by omega,
      show 4 * (3 * m) + 1 = 12 * m + 1 by omega] at h₀
    have h₁ := s_b_zero (6 * m + 6) (4 * m + 1) [0] (3 :: (twos (12 * m + 1) ++ 3 :: Rest))
    rw [tw_one_succ] at h₁
    have h₂ := s_c_move 2 [0] (twos (4 * m) ++ 3 :: (twos (12 * m + 1) ++ 3 :: Rest)) (6 * m + 6)
    have h₃ := s_c_one 0 [] ((2 + (6 * m + 6)) :: (twos (4 * m) ++ 3 :: (twos (12 * m + 1) ++ 3 :: Rest)))
    have h₄ := s_f_tok (2 + (6 * m + 6)) 0 [0 + 2] (twos (4 * m) ++ 3 :: (twos (12 * m + 1) ++ 3 :: Rest))
    have h₅ := tail_iter [] (3 :: (twos (12 * m + 1) ++ 3 :: Rest)) (2 * m) (0 + (2 + (6 * m + 6)) + 1) (0 + 2)
    rw [← twos_even (4 * m) (2 * m) (by omega)] at h₅
    have h₆ := three_two (0 + (2 + (6 * m + 6)) + 1 + 4 * (2 * m)) [0 + 2 + 2 * (2 * m)] (twos (12 * m) ++ 3 :: Rest)
    have h₇ := tail_iter [0 + 2 + 2 * (2 * m)] (3 :: Rest) (6 * m) 4 (0 + (2 + (6 * m + 6)) + 1 + 4 * (2 * m) + 2)
    rw [← twos_even (12 * m) (6 * m) (by omega)] at h₇
    rw [show 4 + 4 * (6 * m) = 24 * m + 4 by omega,
      show 0 + (2 + (6 * m + 6)) + 1 + 4 * (2 * m) + 2 + 2 * (6 * m) = 26 * m + 11 by omega,
      show 0 + 2 + 2 * (2 * m) = 4 * m + 2 by omega] at h₇
    rw [show 0 + 2 + 2 * (2 * m) = 4 * m + 2 by omega] at h₅ h₆
    have e2 : twos (12 * m + 1) ++ 3 :: Rest = 2 :: (twos (12 * m) ++ 3 :: Rest) := rfl
    rw [e2] at h₄ h₅
    simp only [ite_true]
    exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans h₇))))))
  · -- r = 3m + 1: a block 3(4m + 2) + 1 carries on to the block 6m + 8
    have h₀ := lvl_start (3 * m + 1) Rest
    rw [show 4 * (3 * m + 1) + 3 = 3 * (4 * m + 2) + 1 by omega, show 2 * (3 * m + 1) + 6 = 6 * m + 8 by omega,
      show 4 * (3 * m + 1) + 1 = 12 * m + 5 by omega] at h₀
    have h₁ := s_b_one (6 * m + 8) (4 * m + 2) 0 [0] (3 :: (twos (12 * m + 5) ++ 3 :: Rest))
    rw [enc_snoc0 .B 0 [6 * m + 8, 0]] at h₁
    have e : tw 1 (4 * m + 2) 0 ++ 3 :: (twos (12 * m + 5) ++ 3 :: Rest) =
        1 :: (twos (4 * m + 2) ++ 3 :: (twos (12 * m + 5) ++ 3 :: Rest)) := by
      rw [show tw 1 (4 * m + 2) 0 = cw (4 * m + 2) from rfl, cw_eq]; rfl
    rw [e] at h₁
    have h₂ := ih m (by omega) (twos (12 * m + 5) ++ 3 :: Rest)
    rw [g14_one]
    rcases hg : g14 m with ⟨_ | _, a, b, M⟩
    · rw [hg] at h₂
      simp only [Bool.false_eq_true, ite_false] at h₂ ⊢
      have h₃ := tail_iter M (2 :: 3 :: Rest) (6 * m + 2) a b
      rw [← twos_split (12 * m + 5) (6 * m + 2) (by omega)] at h₃
      have h₄ := two_three (a + 4 * (6 * m + 2)) (b + 2 * (6 * m + 2)) M Rest
      rw [show a + 4 * (6 * m + 2) + 5 = a + 24 * m + 13 by omega,
        show b + 2 * (6 * m + 2) + 2 = b + 12 * m + 6 by omega] at h₄
      exact h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄)))
    · rw [hg] at h₂
      simp only [ite_true] at h₂ ⊢
      have h₃ := three_two a (b :: M) (twos (12 * m + 4) ++ 3 :: Rest)
      have h₄ := tail_iter (b :: M) (3 :: Rest) (6 * m + 2) 4 (a + 2)
      rw [← twos_even (12 * m + 4) (6 * m + 2) (by omega),
        show 4 + 4 * (6 * m + 2) = 24 * m + 12 by omega, show a + 2 + 2 * (6 * m + 2) = a + 12 * m + 6 by omega] at h₄
      exact h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄)))
  · -- r = 3m + 2: a block 3(4m + 2) + 5, as for x ≡ 2 (mod 18)
    rw [g14_two]
    have h₀ := lvl_start (3 * m + 2) Rest
    rw [show 4 * (3 * m + 2) + 3 = 3 * (4 * m + 2) + 5 by omega, show 2 * (3 * m + 2) + 6 = 6 * m + 10 by omega,
      show 4 * (3 * m + 2) + 1 = 12 * m + 9 by omega] at h₀
    have h₁ := s_b_two (6 * m + 10) (4 * m + 2) 0 [0] (3 :: (twos (12 * m + 9) ++ 3 :: Rest))
    rw [tw_two] at h₁
    have h₂ := s_e_two (6 * m + 10 + 3) [0] (twos (4 * m + 2) ++ 3 :: (twos (12 * m + 9) ++ 3 :: Rest))
    have h₃ := s_f_tok 2 0 [6 * m + 10 + 3 + 3, 0] (twos (4 * m + 1) ++ 3 :: (twos (12 * m + 9) ++ 3 :: Rest))
    have h₄ := tail_iter [0] (2 :: 3 :: (twos (12 * m + 9) ++ 3 :: Rest)) (2 * m) (0 + 2 + 1) (6 * m + 10 + 3 + 3)
    rw [← twos_split (4 * m + 1) (2 * m) (by omega)] at h₄
    have h₅ := two_three (0 + 2 + 1 + 4 * (2 * m)) (6 * m + 10 + 3 + 3 + 2 * (2 * m)) [0]
      (twos (12 * m + 9) ++ 3 :: Rest)
    have h₆ := tail_iter [0] (2 :: 3 :: Rest) (6 * m + 4) (0 + 2 + 1 + 4 * (2 * m) + 5)
      (6 * m + 10 + 3 + 3 + 2 * (2 * m) + 2)
    rw [← twos_split (12 * m + 9) (6 * m + 4) (by omega)] at h₆
    have h₇ := two_three (0 + 2 + 1 + 4 * (2 * m) + 5 + 4 * (6 * m + 4))
      (6 * m + 10 + 3 + 3 + 2 * (2 * m) + 2 + 2 * (6 * m + 4)) [0] Rest
    rw [show 0 + 2 + 1 + 4 * (2 * m) + 5 + 4 * (6 * m + 4) + 5 = 32 * m + 29 by omega,
      show 6 * m + 10 + 3 + 3 + 2 * (2 * m) + 2 + 2 * (6 * m + 4) + 2 = 22 * m + 28 by omega] at h₇
    simp only [Bool.false_eq_true, ite_false]
    exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans h₇))))))

theorem g14_pos : ∀ r : Nat, 4 ≤ (g14 r).2.1 := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
  obtain ⟨m, rfl | rfl | rfl⟩ : ∃ m, r = 3 * m ∨ r = 3 * m + 1 ∨ r = 3 * m + 2 := ⟨r / 3, by omega⟩
  · rw [g14_zero]; simp only; omega
  · have h := ih m (by omega)
    rw [g14_one]
    rcases hg : g14 m with ⟨_ | _, a, b, M⟩ <;> rw [hg] at h <;> simp only at h ⊢ <;> omega
  · rw [g14_two]; simp only; omega

/-- The start of `x ≡ 14 (mod 18)`: the first sweep, then a carry over the block `12r + 7` to the level `6r + 8`. -/
theorem one_fourteen_start (r i : Nat) :
    Reaches (K [18 * r + 14] (3 * i + 2))
      (enc ⟨.A, 0, (g14 r).2.1 :: (g14 r).2.2.1 :: (g14 r).2.2.2, if (g14 r).1 then 3 :: twos i else twos i⟩) := by
  have h₀ := K_start1 (18 * r + 14) i
  have h₁ := one_two6_sweep (3 * r + 1) (twos (i + 1))
  rw [show 6 * (3 * r + 1) + 8 = 18 * r + 14 by omega, show 4 * (3 * r + 1) + 3 = 3 * (4 * r + 2) + 1 by omega,
    show 2 * (3 * r + 1) + 6 = 6 * r + 8 by omega] at h₁
  have h₂ := a_one_two (3 * (4 * r + 2) + 1) [6 * r + 8, 0] (twos i)
  have h₃ := s_b_one (6 * r + 8) (4 * r + 2) 0 [0] (3 :: twos i)
  rw [enc_snoc0 .B 0 [6 * r + 8, 0]] at h₃
  have e : tw 1 (4 * r + 2) 0 ++ 3 :: twos i = 1 :: (twos (4 * r + 2) ++ 3 :: twos i) := by
    rw [show tw 1 (4 * r + 2) 0 = cw (4 * r + 2) from rfl, cw_eq]; rfl
  rw [e] at h₃
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (lvl r (twos i)))))

/-- **`x ≡ 14 (mod 18)`, no word 3 left** (`(x - 5)/9` without its factors 3 is 5 mod 6): one supply word; a last
block `3j` becomes `a + 2(j - 1)`, the block left of it `b + 2⌈(j - 1)/2⌉`, with `(false, a, b, M) = g14 ((x - 14)/18)`
(kernel only). -/
theorem one_fourteen_two (r i a b : Nat) (M : List Nat) (hg : g14 r = (false, a, b, M)) :
    Reaches (K [18 * r + 14] (3 * i + 2)) (K ((b + 2 * ((i + 1) / 2)) :: M) (a + 2 * i - 1)) := by
  have h₀ := one_fourteen_start r i
  have hp := g14_pos r
  rw [hg] at h₀ hp
  simp only [Bool.false_eq_true, ite_false] at h₀ hp
  exact h₀.trans (tail_end a b M i (by omega))

/-- **`x ≡ 14 (mod 18)`, a word 3 left** (`(x - 5)/9` without its factors 3 is 1 mod 6): offset 0, two supply words;
a last block `3j`, `j ≥ 2`, becomes `2j`, the blocks left of it `a + 2 + 2⌈(j - 2)/2⌉, b, M`, with
`(true, a, b, M) = g14 ((x - 14)/18)` (kernel only). -/
theorem one_fourteen_three (r i a b : Nat) (M : List Nat) (hg : g14 r = (true, a, b, M)) :
    Reaches (K [18 * r + 14] (3 * (i + 1) + 2)) (K ((a + 2 + 2 * ((i + 1) / 2)) :: b :: M) (4 + 2 * i - 1)) := by
  have h₀ := one_fourteen_start r (i + 1)
  rw [hg] at h₀
  simp only [ite_true] at h₀
  have h₁ := three_two a (b :: M) (twos i)
  exact h₀.trans (h₁.trans (tail_end 4 (a + 2) (b :: M) i (by omega)))

/-- **`x = 5`**: a last block `3j` becomes `2j + 2`, the block left of it `6 + 2⌈j/2⌉` (kernel only). -/
theorem one_five (i : Nat) : Reaches (K [5] (3 * i + 2)) (K [6 + 2 * ((i + 2) / 2)] (2 + 2 * (i + 1) - 1)) := by
  have h₀ := K_start1 5 i
  have h₁ := s_b_two 0 0 0 [0] (1 :: twos (i + 1))
  have h₂ := s_e_two (0 + 3) [0] (1 :: twos (i + 1))
  have h₃ := s_f_tok 1 0 [0 + 3 + 3, 0] (twos (i + 1))
  have h₄ := tail_end (0 + 1 + 1) (0 + 3 + 3) [0] (i + 1) (by omega)
  rw [K_one0] at h₄
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄)))

/-! ## Odd blocks -/

/-- The first sweep after a single block `6q + 1`: A before the block `4q + 2` and the word 1 (kernel only). -/
theorem one_one6_sweep (q : Nat) (R : List Nat) :
    Reaches (enc ⟨.B, 0, [6 * q + 1, 0, 0], 0 :: 1 :: R⟩) (enc ⟨.A, 0, [4 * q + 2, 2 * q + 2, 0], 1 :: R⟩) := by
  have h₁ := s_b_one 0 (2 * q) 0 [0] (1 :: R)
  rw [show 3 * (2 * q) + 1 = 6 * q + 1 by omega] at h₁
  have h₂ := s_b_zero 0 0 [] (tw 1 (2 * q) 0 ++ 1 :: R)
  rw [show 3 * 0 = 0 from rfl, enc_snoc0 .C, show tw 1 0 0 = [1] from rfl] at h₂
  simp only [List.cons_append, List.nil_append] at h₂
  have e : tw 1 (2 * q) 0 ++ 1 :: R = 1 :: (twos (2 * q) ++ 1 :: R) := by
    rw [show tw 1 (2 * q) 0 = cw (2 * q) from rfl, cw_eq]; rfl
  rw [e] at h₁ h₂
  have h₃ := s_c_one 0 [] (1 :: (twos (2 * q) ++ 1 :: R))
  have h₄ := s_f_tok 1 0 [0 + 2] (twos (2 * q) ++ 1 :: R)
  rw [enc_snoc0 .A] at h₄
  have h₅ := tail_iter [0] (1 :: R) q (0 + 1 + 1) (0 + 2)
  rw [show 0 + 1 + 1 + 4 * q = 4 * q + 2 by omega, show 0 + 2 + 2 * q = 2 * q + 2 by omega] at h₅
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- The first sweep after a single block `6q + 3`: A before the block `4q + 3` and the word 1 (kernel only). -/
theorem one_three6_sweep (q : Nat) (R : List Nat) :
    Reaches (enc ⟨.B, 0, [6 * q + 3, 0, 0], 0 :: 1 :: R⟩) (enc ⟨.A, 0, [4 * q + 3, 2 * q + 2, 0], 1 :: R⟩) := by
  have h₁ := s_b_zero 0 (2 * q + 1) [0] (1 :: R)
  rw [show 3 * (2 * q + 1) = 6 * q + 3 by omega] at h₁
  have e : tw 1 (2 * q + 1) 0 ++ 1 :: R = 1 :: 2 :: (twos (2 * q) ++ 1 :: R) := by
    rw [tw_one_succ]; rfl
  rw [e] at h₁
  have h₂ := s_c_one 0 [] (2 :: (twos (2 * q) ++ 1 :: R))
  have h₃ := s_f_tok 2 0 [0 + 2] (twos (2 * q) ++ 1 :: R)
  rw [enc_snoc0 .A] at h₃
  have h₄ := tail_iter [0] (1 :: R) q (0 + 2 + 1) (0 + 2)
  rw [show 0 + 2 + 1 + 4 * q = 4 * q + 3 by omega, show 0 + 2 + 2 * q = 2 * q + 2 by omega] at h₄
  exact h₁.trans (h₂.trans (h₃.trans h₄))

theorem a_one_two' (a b i : Nat) :
    Reaches (enc ⟨.A, 0, [a, b, 0], 1 :: twos (i + 1)⟩) (enc ⟨.B, 0, [a, b, 0], 0 :: 3 :: twos i⟩) :=
  a_one_two a [b, 0] (twos i)

/-- **`x ≡ 1 (mod 18)`, x ≥ 19**: offset 0; a last block `3j`, `j ≥ 2`, becomes `2j`, the blocks left of it
`(4x + 5)/9 + 2⌈(j - 2)/2⌉` and `(5x + 49)/9` (kernel only). -/
theorem one_one18 (r i : Nat) :
    Reaches (K [18 * r + 19] (3 * (i + 1) + 2)) (K [8 * r + 9 + 2 * ((i + 1) / 2), 10 * r + 16] (4 + 2 * i - 1)) := by
  have h₀ := K_start1 (18 * r + 19) (i + 1)
  have h₁ := one_one6_sweep (3 * r + 3) (twos (i + 2))
  rw [show 6 * (3 * r + 3) + 1 = 18 * r + 19 by omega, show 4 * (3 * r + 3) + 2 = 3 * (4 * r + 3) + 5 by omega,
    show 2 * (3 * r + 3) + 2 = 6 * r + 8 by omega] at h₁
  have h₂ := a_one_two' (3 * (4 * r + 3) + 5) (6 * r + 8) (i + 1)
  have h₃ := s_b_two (6 * r + 8) (4 * r + 3) 0 [0] (3 :: twos (i + 1))
  rw [tw_two] at h₃
  have h₄ := s_e_two (6 * r + 8 + 3) [0] (twos (4 * r + 3) ++ 3 :: twos (i + 1))
  have h₅ := s_f_tok 2 0 [6 * r + 8 + 3 + 3, 0] (twos (4 * r + 2) ++ 3 :: twos (i + 1))
  have h₆ := tail_iter [0] (3 :: twos (i + 1)) (2 * r + 1) (0 + 2 + 1) (6 * r + 8 + 3 + 3)
  rw [← twos_even (4 * r + 2) (2 * r + 1) (by omega)] at h₆
  have h₇ := three_two (0 + 2 + 1 + 4 * (2 * r + 1)) [6 * r + 8 + 3 + 3 + 2 * (2 * r + 1), 0] (twos i)
  rw [show 0 + 2 + 1 + 4 * (2 * r + 1) + 2 = 8 * r + 9 by omega,
    show 6 * r + 8 + 3 + 3 + 2 * (2 * r + 1) = 10 * r + 16 by omega] at h₇
  rw [show 6 * r + 8 + 3 + 3 + 2 * (2 * r + 1) = 10 * r + 16 by omega] at h₆
  have h₈ := tail_end 4 (8 * r + 9) [10 * r + 16, 0] i (by omega)
  rw [show [8 * r + 9 + 2 * ((i + 1) / 2), 10 * r + 16, 0] = [8 * r + 9 + 2 * ((i + 1) / 2), 10 * r + 16] ++ [0]
    from rfl, ← K_snoc0] at h₈
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans (h₇.trans h₈)))))))

/-- **`x ≡ 7 (mod 18)`**: one supply word; a last block `3j` becomes `(7x + 41)/9 + 2j`, the block left of it
`(2x + 22)/9 + 2⌈(j - 1)/2⌉` (kernel only). -/
theorem one_seven18 (r i : Nat) :
    Reaches (K [18 * r + 7] (3 * i + 2)) (K [4 * r + 4 + 2 * ((i + 1) / 2)] (14 * r + 12 + 2 * i - 1)) := by
  have h₀ := K_start1 (18 * r + 7) i
  have h₁ := one_one6_sweep (3 * r + 1) (twos (i + 1))
  rw [show 6 * (3 * r + 1) + 1 = 18 * r + 7 by omega, show 4 * (3 * r + 1) + 2 = 3 * (4 * r + 2) by omega,
    show 2 * (3 * r + 1) + 2 = 6 * r + 4 by omega] at h₁
  have h₂ := a_one_two' (3 * (4 * r + 2)) (6 * r + 4) i
  have h₃ := s_b_zero (6 * r + 4) (4 * r + 2) [0] (3 :: twos i)
  rw [tw_one_succ] at h₃
  have h₄ := s_c_move 2 [0] (twos (4 * r + 1) ++ 3 :: twos i) (6 * r + 4)
  have h₅ := s_c_one 0 [] ((2 + (6 * r + 4)) :: (twos (4 * r + 1) ++ 3 :: twos i))
  have h₆ := s_f_tok (2 + (6 * r + 4)) 0 [0 + 2] (twos (4 * r + 1) ++ 3 :: twos i)
  have h₇ := tail_iter [] (2 :: 3 :: twos i) (2 * r) (0 + (2 + (6 * r + 4)) + 1) (0 + 2)
  rw [← twos_split (4 * r + 1) (2 * r) (by omega)] at h₇
  have h₈ := two_three (0 + (2 + (6 * r + 4)) + 1 + 4 * (2 * r)) (0 + 2 + 2 * (2 * r)) [] (twos i)
  rw [show 0 + (2 + (6 * r + 4)) + 1 + 4 * (2 * r) + 5 = 14 * r + 12 by omega,
    show 0 + 2 + 2 * (2 * r) + 2 = 4 * r + 4 by omega] at h₈
  have h₉ := tail_end (14 * r + 12) (4 * r + 4) [] i (by omega)
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans (h₇.trans (h₈.trans h₉))))))))

/-- **`x ≡ 13 (mod 18)`**: one supply word; a last block `3j` becomes `(2x + 13)/3 + 2j`, the block left of it
`(x + 11)/3 + 2⌈(j - 1)/2⌉` (kernel only). -/
theorem one_thirteen18 (r i : Nat) :
    Reaches (K [18 * r + 13] (3 * i + 2)) (K [6 * r + 8 + 2 * ((i + 1) / 2)] (12 * r + 15 + 2 * i - 1)) := by
  have h₀ := K_start1 (18 * r + 13) i
  have h₁ := one_one6_sweep (3 * r + 2) (twos (i + 1))
  rw [show 6 * (3 * r + 2) + 1 = 18 * r + 13 by omega, show 4 * (3 * r + 2) + 2 = 3 * (4 * r + 3) + 1 by omega,
    show 2 * (3 * r + 2) + 2 = 3 * (2 * r + 2) by omega] at h₁
  have h₂ := a_one_two' (3 * (4 * r + 3) + 1) (3 * (2 * r + 2)) i
  have h₃ := s_b_one (3 * (2 * r + 2)) (4 * r + 3) 0 [0] (3 :: twos i)
  have e : tw 1 (4 * r + 3) 0 ++ 3 :: twos i = 1 :: (twos (4 * r + 3) ++ 3 :: twos i) := by
    rw [show tw 1 (4 * r + 3) 0 = cw (4 * r + 3) from rfl, cw_eq]; rfl
  rw [e, enc_snoc0 .B 0 [3 * (2 * r + 2), 0]] at h₃
  have h₄ := s_b_zero 0 (2 * r + 2) [0] (1 :: (twos (4 * r + 3) ++ 3 :: twos i))
  rw [tw_one_succ] at h₄
  have h₅ := s_c_one 0 [] (2 :: (twos (2 * r + 1) ++ 1 :: (twos (4 * r + 3) ++ 3 :: twos i)))
  have h₆ := s_f_tok 2 0 [0 + 2] (twos (2 * r + 1) ++ 1 :: (twos (4 * r + 3) ++ 3 :: twos i))
  have h₇ := tail_iter [] (2 :: 1 :: (twos (4 * r + 3) ++ 3 :: twos i)) r (0 + 2 + 1) (0 + 2)
  rw [← twos_odd] at h₇
  have h₈ := two_one (0 + 2 + 1 + 4 * r) (0 + 2 + 2 * r) [] (twos (4 * r + 3) ++ 3 :: twos i)
  have h₉ := tail_iter [] (2 :: 3 :: twos i) (2 * r + 1) (0 + 2 + 1 + 4 * r + 3) (0 + 2 + 2 * r + 2)
  rw [← twos_split (4 * r + 3) (2 * r + 1) (by omega)] at h₉
  have h₁₀ := two_three (0 + 2 + 1 + 4 * r + 3 + 4 * (2 * r + 1)) (0 + 2 + 2 * r + 2 + 2 * (2 * r + 1)) [] (twos i)
  rw [show 0 + 2 + 1 + 4 * r + 3 + 4 * (2 * r + 1) + 5 = 12 * r + 15 by omega,
    show 0 + 2 + 2 * r + 2 + 2 * (2 * r + 1) + 2 = 6 * r + 8 by omega] at h₁₀
  have h₁₁ := tail_end (12 * r + 15) (6 * r + 8) [] i (by omega)
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans (h₇.trans (h₈.trans
    (h₉.trans (h₁₀.trans h₁₁))))))))))

/-- **`x ≡ 3 (mod 18)`**: offset 0; a last block `3j`, `j ≥ 2`, becomes `2j`, the blocks left of it
`(7x + 42)/9 + 2⌈(j - 2)/2⌉` and `(2x + 12)/9` (kernel only). -/
theorem one_three18 (r i : Nat) :
    Reaches (K [18 * r + 3] (3 * (i + 1) + 2)) (K [14 * r + 7 + 2 * ((i + 1) / 2), 4 * r + 2] (4 + 2 * i - 1)) := by
  have h₀ := K_start1 (18 * r + 3) (i + 1)
  have h₁ := one_three6_sweep (3 * r) (twos (i + 2))
  rw [show 6 * (3 * r) + 3 = 18 * r + 3 by omega, show 4 * (3 * r) + 3 = 3 * (4 * r + 1) by omega,
    show 2 * (3 * r) + 2 = 6 * r + 2 by omega] at h₁
  have h₂ := a_one_two' (3 * (4 * r + 1)) (6 * r + 2) (i + 1)
  have h₃ := s_b_zero (6 * r + 2) (4 * r + 1) [0] (3 :: twos (i + 1))
  rw [tw_one_succ] at h₃
  have h₄ := s_c_move 2 [0] (twos (4 * r) ++ 3 :: twos (i + 1)) (6 * r + 2)
  have h₅ := s_c_one 0 [] ((2 + (6 * r + 2)) :: (twos (4 * r) ++ 3 :: twos (i + 1)))
  have h₆ := s_f_tok (2 + (6 * r + 2)) 0 [0 + 2] (twos (4 * r) ++ 3 :: twos (i + 1))
  have h₇ := tail_iter [] (3 :: twos (i + 1)) (2 * r) (0 + (2 + (6 * r + 2)) + 1) (0 + 2)
  rw [← twos_even (4 * r) (2 * r) (by omega), show 0 + 2 + 2 * (2 * r) = 4 * r + 2 by omega] at h₇
  have h₈ := three_two (0 + (2 + (6 * r + 2)) + 1 + 4 * (2 * r)) [4 * r + 2] (twos i)
  rw [show 0 + (2 + (6 * r + 2)) + 1 + 4 * (2 * r) + 2 = 14 * r + 7 by omega] at h₈
  have h₉ := tail_end 4 (14 * r + 7) [4 * r + 2] i (by omega)
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans (h₇.trans (h₈.trans h₉))))))))

/-- **`x ≡ 9 (mod 18)`**: offset 0; a last block `3j`, `j ≥ 2`, becomes `2j`, the blocks left of it
`(2x + 15)/3 + 2⌈(j - 2)/2⌉` and `(x + 9)/3` (kernel only). -/
theorem one_nine18 (r i : Nat) :
    Reaches (K [18 * r + 9] (3 * (i + 1) + 2)) (K [12 * r + 11 + 2 * ((i + 1) / 2), 6 * r + 6] (4 + 2 * i - 1)) := by
  have h₀ := K_start1 (18 * r + 9) (i + 1)
  have h₁ := one_three6_sweep (3 * r + 1) (twos (i + 2))
  rw [show 6 * (3 * r + 1) + 3 = 18 * r + 9 by omega, show 4 * (3 * r + 1) + 3 = 3 * (4 * r + 2) + 1 by omega,
    show 2 * (3 * r + 1) + 2 = 3 * (2 * r + 1) + 1 by omega] at h₁
  have h₂ := a_one_two' (3 * (4 * r + 2) + 1) (3 * (2 * r + 1) + 1) (i + 1)
  have h₃ := s_b_one (3 * (2 * r + 1) + 1) (4 * r + 2) 0 [0] (3 :: twos (i + 1))
  have e : tw 1 (4 * r + 2) 0 ++ 3 :: twos (i + 1) = 1 :: (twos (4 * r + 2) ++ 3 :: twos (i + 1)) := by
    rw [show tw 1 (4 * r + 2) 0 = cw (4 * r + 2) from rfl, cw_eq]; rfl
  rw [e, enc_snoc0 .B 0 [3 * (2 * r + 1) + 1, 0]] at h₃
  have h₄ := s_b_one 0 (2 * r + 1) 0 [0] (1 :: (twos (4 * r + 2) ++ 3 :: twos (i + 1)))
  have e' : tw 1 (2 * r + 1) 0 ++ 1 :: (twos (4 * r + 2) ++ 3 :: twos (i + 1)) =
      1 :: (twos (2 * r + 1) ++ 1 :: (twos (4 * r + 2) ++ 3 :: twos (i + 1))) := by
    rw [show tw 1 (2 * r + 1) 0 = cw (2 * r + 1) from rfl, cw_eq]; rfl
  rw [e'] at h₄
  have h₅ := s_b_zero 0 0 [] (1 :: (twos (2 * r + 1) ++ 1 :: (twos (4 * r + 2) ++ 3 :: twos (i + 1))))
  rw [show 3 * 0 = 0 from rfl, enc_snoc0 .C, show tw 1 0 0 = [1] from rfl] at h₅
  simp only [List.cons_append, List.nil_append] at h₅
  have h₆ := s_c_one 0 [] (1 :: (twos (2 * r + 1) ++ 1 :: (twos (4 * r + 2) ++ 3 :: twos (i + 1))))
  have h₇ := s_f_tok 1 0 [0 + 2] (twos (2 * r + 1) ++ 1 :: (twos (4 * r + 2) ++ 3 :: twos (i + 1)))
  have h₈ := tail_iter [] (2 :: 1 :: (twos (4 * r + 2) ++ 3 :: twos (i + 1))) r (0 + 1 + 1) (0 + 2)
  rw [← twos_odd] at h₈
  have h₉ := two_one (0 + 1 + 1 + 4 * r) (0 + 2 + 2 * r) [] (twos (4 * r + 2) ++ 3 :: twos (i + 1))
  have h₁₀ := tail_iter [] (3 :: twos (i + 1)) (2 * r + 1) (0 + 1 + 1 + 4 * r + 3) (0 + 2 + 2 * r + 2)
  rw [← twos_even (4 * r + 2) (2 * r + 1) (by omega),
    show 0 + 2 + 2 * r + 2 + 2 * (2 * r + 1) = 6 * r + 6 by omega] at h₁₀
  have h₁₁ := three_two (0 + 1 + 1 + 4 * r + 3 + 4 * (2 * r + 1)) [6 * r + 6] (twos i)
  rw [show 0 + 1 + 1 + 4 * r + 3 + 4 * (2 * r + 1) + 2 = 12 * r + 11 by omega] at h₁₁
  have h₁₂ := tail_end 4 (12 * r + 11) [6 * r + 6] i (by omega)
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans (h₇.trans (h₈.trans
    (h₉.trans (h₁₀.trans (h₁₁.trans h₁₂)))))))))))

/-- **`x ≡ 15 (mod 18)`**: one supply word; a last block `3j` becomes `(4x - 6)/9 + 2j`, the block left of it
`(5x + 51)/9 + 2⌈(j - 1)/2⌉` (kernel only). -/
theorem one_fifteen18 (r i : Nat) :
    Reaches (K [18 * r + 15] (3 * i + 2)) (K [10 * r + 14 + 2 * ((i + 1) / 2)] (8 * r + 8 + 2 * i - 1)) := by
  have h₀ := K_start1 (18 * r + 15) i
  have h₁ := one_three6_sweep (3 * r + 2) (twos (i + 1))
  rw [show 6 * (3 * r + 2) + 3 = 18 * r + 15 by omega, show 4 * (3 * r + 2) + 3 = 3 * (4 * r + 2) + 5 by omega,
    show 2 * (3 * r + 2) + 2 = 6 * r + 6 by omega] at h₁
  have h₂ := a_one_two' (3 * (4 * r + 2) + 5) (6 * r + 6) i
  have h₃ := s_b_two (6 * r + 6) (4 * r + 2) 0 [0] (3 :: twos i)
  rw [tw_two] at h₃
  have h₄ := s_e_two (6 * r + 6 + 3) [0] (twos (4 * r + 2) ++ 3 :: twos i)
  have h₅ := s_f_tok 2 0 [6 * r + 6 + 3 + 3, 0] (twos (4 * r + 1) ++ 3 :: twos i)
  have h₆ := tail_iter [0] (2 :: 3 :: twos i) (2 * r) (0 + 2 + 1) (6 * r + 6 + 3 + 3)
  rw [← twos_split (4 * r + 1) (2 * r) (by omega)] at h₆
  have h₇ := two_three (0 + 2 + 1 + 4 * (2 * r)) (6 * r + 6 + 3 + 3 + 2 * (2 * r)) [0] (twos i)
  rw [show 0 + 2 + 1 + 4 * (2 * r) + 5 = 8 * r + 8 by omega,
    show 6 * r + 6 + 3 + 3 + 2 * (2 * r) + 2 = 10 * r + 14 by omega] at h₇
  have h₈ := tail_end (8 * r + 8) (10 * r + 14) [0] i (by omega)
  rw [K_one0] at h₈
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans (h₇.trans h₈)))))))

end BB6c
