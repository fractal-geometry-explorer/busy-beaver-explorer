import Model

/-! # A halt of the counter needs a charged pair

Two neighbouring groups `(d, n), (d', n')` are **neutral** when `n ≡ d' + 2 (mod 3)`, and **charged** otherwise.
A plain decrement keeps every pair's residue `n - d' (mod 3)`, so a neutral pair stays neutral, and in a neutral
pair an empty group is followed by a digit 1: the two merge.  The halting patterns of the model all start with an
empty group followed by a digit 0, so they need a charged pair.

`good G` says that every pair of `G` is neutral, except the pairs at the very end of the list, where the model's
end-of-round events put empty groups: a last group `(0,0)` or `(1,0)`, or two last groups `(0,0), (0,0)`, may sit
behind anything.  `good_not_halt`: from a good list the next bounce is not a halt (for every `n0`). -/

namespace H40361

/-- The pair `a, b` is neutral: `a`'s block length is `b`'s digit plus 2, mod 3. -/
def pairOK (a b : Nat × Nat) : Bool := a.2 % 3 == (b.1 + 2) % 3

/-- The lists `[X]`, `[X, (0,0)]`, `[X, (1,0)]`, `[X, (0,0), (0,0)]` (and the empty list): the tails that the
end-of-round events leave, in which the pairs are not constrained. -/
def tailFree : List (Nat × Nat) → Bool
  | [] => true
  | [_] => true
  | _ :: (d, n) :: rest =>
    n == 0 && (match rest with
      | [] => decide (d ≤ 1)
      | [(d', n')] => d == 0 && d' == 0 && n' == 0
      | _ => false)

/-- Every pair is neutral, up to a free tail. -/
def good : List (Nat × Nat) → Bool
  | [] => true
  | a :: l => tailFree (a :: l) || ((match l with | [] => true | b :: _ => pairOK a b) && good l)

theorem good_tail {a : Nat × Nat} {l : List (Nat × Nat)} (h : good (a :: l) = true) : good l = true := by
  unfold good at h
  rcases Bool.or_eq_true _ _ |>.mp h with h1 | h1
  · rcases l with _ | ⟨⟨d, n⟩, rest⟩
    · rfl
    · rcases rest with _ | ⟨⟨d', n'⟩, rest'⟩
      · simp [good, tailFree]
      · rcases rest' with _ | ⟨c, rest''⟩
        · simp [tailFree] at h1
          obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := h1
          decide
        · simp [tailFree] at h1
  · exact (Bool.and_eq_true _ _ |>.mp h1).2

theorem good_suffix : ∀ (pre : List (Nat × Nat)) {r : List (Nat × Nat)}, good (pre ++ r) = true → good r = true
  | [], _, h => h
  | _ :: pre, _, h => good_suffix pre (good_tail h)

/-- What `norm` leaves is the end of the list it was given. -/
theorem norm_suffix (n0 : Nat) (racc : List Nat) (G : List (Nat × Nat)) :
    ∃ pre, pre ++ (norm n0 racc G).2.2 = G := by
  fun_induction norm n0 racc G with
  | case1 n0 racc m G ih => obtain ⟨pre, h⟩ := ih; exact ⟨(0, m + 1) :: pre, by rw [List.cons_append, h]⟩
  | case2 n0 n G ih => obtain ⟨pre, h⟩ := ih; exact ⟨(0, 0) :: (1, n) :: pre, by simp [h]⟩
  | case3 n0 m racc n G ih => obtain ⟨pre, h⟩ := ih; exact ⟨(0, 0) :: (1, n) :: pre, by simp [h]⟩
  | case4 n0 racc n G ih => obtain ⟨pre, h⟩ := ih; exact ⟨(0, 0) :: (0, 0) :: (1, n) :: pre, by simp [h]⟩
  | case5 n0 racc G _ _ _ _ => exact ⟨[], rfl⟩

/-- The halting patterns are not good. -/
theorem term_halt_not_good {n0 : Nat} {ms : List Nat} {r : List (Nat × Nat)} (h : term n0 ms r = .halt) :
    good r = false := by
  unfold term at h
  rcases r with _ | ⟨⟨d, n⟩, rest⟩
  · simp only at h; split at h <;> cases h
  · rcases d with _ | e
    · rcases n with _ | n
      · simp only at h
        split at h <;> (try cases h) <;>
          first
            | (simp [good, tailFree, pairOK]; done)
            | (rename_i tl; rcases tl with _ | ⟨c, tl⟩ <;> simp [good, tailFree, pairOK]; done)
            | (rename_i tl; rcases tl with _ | ⟨c, tl⟩ <;> (try rcases tl with _ | ⟨c', tl⟩) <;>
                simp [good, tailFree, pairOK]; done)
      · simp only at h; cases h
    · simp only at h; cases h

/-- **No halt without a charge.**  If every pair of the list is neutral (up to a free tail), the next bounce of
the counter is not a halt. -/
theorem good_not_halt (n0 : Nat) {G : List (Nat × Nat)} (hg : good G = true) : bounceM n0 G ≠ .halt := by
  intro h
  obtain ⟨pre, hp⟩ := norm_suffix n0 [] G
  have h1 : good (norm n0 [] G).2.2 = true := good_suffix pre (by rw [hp]; exact hg)
  have h2 := term_halt_not_good h
  rw [h1] at h2; cases h2

end H40361
