import Chain

/-!
# Case B of `Chain.lean`: a last block 6 with offset 0

Case B is a pass start `…, x, 6` with `x ≠ 2` whose recursive pass has offset `c = 0` (`six_pass`): it passes to a
last block 4 and halts on the pass after.  What this file settles:

* `sixteen_halts`, `chain_54_halts`: **no condition on the pass start alone that `Safe` and the parity of the blocks
  can express rules case B out.**  `16 16` is safe, every block is even (as the leftmost block always is on the run,
  computed), and it halts: `16 16 → 26 9 → 6 27 6 → 14 27 4 → 14 33 1`, then the halt.  `314 54` is safe and even
  too, and comes down to case B by three recursive passes with offset 0 (last blocks `54 → 36 → 24 → 16`), the
  covered `16 → 9` and `9 → 6`, again with offset 0.  So excluding case B needs the history of the run.
* `safe_pass_shrink`: what that history must contain.  From a safe start with last block other than 3 and 6, if `pre`
  stops, the next pass start is safe, its last block is at least two thirds of the old one less 5/3
  (`2 n ≤ 3 n' + 6` in terms of `n = last - 1`), and it is 6 only if the old last block was 9, or 2 after a block 3.
  So a halt by case B needs the last block to come down to 9 (or to `3 2`) first, at most by a factor 3/2 a pass.

The computed side is `py/blocks.py caseb`: the offset is 0 exactly when `pre` takes two supply words, the halting
starts found are all at the end of such a descent, and the run's last blocks stay far above it.
-/

namespace BB6c

/-- **A safe pass start with even blocks that halts by case B**, evaluated by the kernel:
`16 16 → 26 9 → 6 27 6 → 14 27 4 → 14 33 1`, then the halt. -/
theorem sixteen_halts : Safe [16] 15 ∧ TM.Halts trans (K [16] 15) := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, List.cons_ne_nil _ _, fun h => absurd h (by decide)⟩, ?_⟩
  exact passes_sound 1000 10 (ls := [16]) (n := 15) (o := .halt) (by decide +kernel)

/-- **A longer descent to case B**: `314 54` is safe with even blocks; the recursive passes `54 → 36 → 24 → 16` (offset
0 each), the covered `16 → 9` and the recursive `9 → 6` (offset 0) bring it to case B, which halts. -/
theorem chain_54_halts : Safe [314] 53 ∧ TM.Halts trans (K [314] 53) := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, List.cons_ne_nil _ _, fun h => absurd h (by decide)⟩, ?_⟩
  exact passes_sound 100000 20 (ls := [314]) (n := 53) (o := .halt) (by decide +kernel)

/-- **The last block comes down by at most a factor 3/2 a pass, and reaches 6 only from 9 or from `3 2`** (kernel
only), if `pre` stops: from a safe pass start with last block `n + 1` other than 3 and 6, the next pass start
`K ls' n'` is safe, `2 n ≤ 3 n' + 6`, and `n' = 5` only if `n = 8`, or `n = 1` with a block 3 left of the last.
Recursive passes by `recur_next` (last block at least `2j - 1` from `3j`), covered ones from `next`. -/
theorem safe_pass_shrink {ls : List Nat} {n : Nat} (hs : Safe ls n) (h3 : n ≠ 2) (h6 : n ≠ 5)
    (hp : PreStops ls) :
    ∃ ls' n', Safe ls' n' ∧ Reaches (K ls n) (K ls' n') ∧ 2 * n ≤ 3 * n' + 6 ∧
      (n' = 5 → n = 8 ∨ (n = 1 ∧ ls.headD 0 = 3)) := by
  by_cases hr : n % 3 = 2
  · obtain ⟨f, L, p, u, e⟩ := hp
    obtain ⟨j, rfl⟩ : ∃ j, 3 * j - 1 = n := ⟨(n + 1) / 3, by omega⟩
    obtain ⟨ls', n', hb, hne, hR, hle⟩ := recur_next_cons hs.1.1 e j (by omega)
    refine ⟨ls', n', ⟨⟨hb, ?_, ?_⟩, hne, ?_⟩, hR, ?_, ?_⟩ <;> split at hle <;> omega
  · obtain ⟨⟨ls', n'⟩, e⟩ := Option.isSome_iff_exists.1 (next_isSome ls hs.1.2.1 hr)
    refine ⟨ls', n', next_safe hs e, next_sound e, ?_⟩
    have hx : 2 ≤ ls.headD 0 := by
      cases ls with
      | nil => exact absurd rfl hs.2.1
      | cons a _ => exact hs.1.1 a (List.mem_cons_self ..)
    have hn3 := hs.1.2.2
    dsimp only [next] at e
    split at e; · cases e; omega
    split at e; · cases e; omega
    split at e; · cases e; omega
    split at e; · cases e; omega
    split at e; · cases e; omega
    cases e

end BB6c
