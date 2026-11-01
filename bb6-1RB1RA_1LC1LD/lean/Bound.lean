import CaseB

/-!
# No lower bound on the last block in terms of the tape is kept by every pass

`lean/CaseB.lean` shows that a halt by case B needs the last block to come down to 9.  The natural way to rule that
out would be a lower bound on the last block in terms of the size of the tape that every pass keeps.  There is none
of that kind: a covered pass from a last block `1 mod 3` (`n % 3 = 0`, `n ≥ 6`) shrinks the last block, to exactly
two thirds of it plus 5, less 5 (`next_shrink`), while every other block stays or grows and the total number of ones
grows by at least 2 (`descent_step`).  So for any nondecreasing `f`, a pass start whose last block is `f` of its
total and `1 mod 3` passes to one whose last block is below `f` of its total (`no_total_bound`); the same holds for any
bound that is nondecreasing in the blocks to the left, since none of them shrinks.

What does constrain the descents is arithmetic: `k` covered descents in a row from a last block `b` need `3^k`
dividing `b + 5` (`next_shrink`, iterated), and the recursive passes on the way have last block `3j` and offset `c`
depending on the blocks to the left.  How often the run meets long descents is a question about residues, measured
in `py/blocks.py descents`.
-/

namespace BB6c

theorem sum_head_tail (ls : List Nat) : ls.sum = ls.headD 0 + ls.tail.sum := by
  cases ls with
  | nil => rfl
  | cons a l => simp only [List.sum_cons, List.headD, List.tail]

/-- **A descent step**: from a last block `n + 1` with `n % 3 = 0`, `n ≥ 6`, for every list of blocks to the left,
the covered pass gives a smaller last block, changes only the block next to it, which grows, and adds at least 2 ones
in total. -/
theorem descent_step (ls : List Nat) {n : Nat} (h3 : n % 3 = 0) (h6 : 6 ≤ n) :
    ∃ x' n', next ls n = some (x' :: ls.tail, n') ∧ n' < n ∧ ls.headD 0 ≤ x' ∧
      ls.sum + n + 2 ≤ (x' :: ls.tail).sum + n' := by
  have hs := sum_head_tail ls
  by_cases h : n % 6 = 3
  · refine ⟨ls.headD 0 + 2 * ((n - 9) / 6) + 8, 4 * ((n - 9) / 6) + 4, ?_, by omega, by omega, ?_⟩
    · have h' : n ≠ 3 := by omega
      simp only [next, h', h, ↓reduceIte]
    · simp only [List.sum_cons]; omega
  · refine ⟨ls.headD 0 + 2 * ((n - 6) / 6) + 6, 4 * ((n - 6) / 6) + 2, ?_, by omega, by omega, ?_⟩
    · have h' : n ≠ 3 := by omega
      have h0 : n % 6 = 0 := by omega
      simp only [next, h', h0, show 0 < n by omega, and_self, ↓reduceIte]
      rfl
    · simp only [List.sum_cons]; omega

/-- **No bound `last ≥ f(total)` is kept by every pass**, for any nondecreasing `f`: a good pass start whose last
block is `1 mod 3`, at least 7, and exactly `f` of its total, passes to a good one whose last block is below `f` of its
total.  (`n + 1` is the last block; the total counts every one on the tape.) -/
theorem no_total_bound (f : Nat → Nat) (hf : ∀ a b, a ≤ b → f a ≤ f b) {ls : List Nat} {n : Nat}
    (hg : Good ls n) (h3 : n % 3 = 0) (h6 : 6 ≤ n) (ht : n + 1 = f (ls.sum + n + 1)) :
    ∃ ls' n', Reaches (K ls n) (K ls' n') ∧ Good ls' n' ∧ n' + 1 < f (ls'.sum + n' + 1) := by
  obtain ⟨x', n', e, hlt, -, hsum⟩ := descent_step ls h3 h6
  refine ⟨_, _, next_sound e, next_good hg e, ?_⟩
  have := hf (ls.sum + n + 1) ((x' :: ls.tail).sum + n' + 1) (by omega)
  omega

end BB6c
