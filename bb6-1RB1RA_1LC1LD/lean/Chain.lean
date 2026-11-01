import Blocks
import Formula
import OffsetData

/-!
# The shrinking chain: what the results so far settle, and what they leave open

`Good ls n` (`Blocks.lean`: every block at least 2, last block `n + 1` neither 1 nor 4) is **not** kept by every
pass: `2 2 3` is good and halts (`recur_two_three_halts`), and so does `3 6` (`three_six_halts`, `3 6 → 2 7 4 → 2 13 1`).
So `Good` alone cannot prove that the machine never halts, whether or not `pre` always stops.  What the results do
give, with `pre` stopping as the only assumption:

* `safe_pass`: from a pass start with at least two blocks, all of them at least 2, and last block other than 1, 3, 4
  and 6, or 3 after a block of at least 6, the next pass start is of the same kind, unless the last block is 3 or 6.
  So a halt needs a last block 3 after a block of at least 6, or a last block 6.  A covered pass makes a last block 3
  only from 7, and then the block to its left has gained 6; a recursive pass makes one only from 6 after a 2.
* `six_after_two`: a last block 6 after a block 2 gives a last block 3 after a block of at least 10, which is safe.
* `six_pass`: a last block 6 after any other block gives last block `4 + c`, `c ≥ 0`: the machine halts if `c = 0`
  (last block 4, then 1), and the next pass start is safe if `c ≥ 1`.

Two cases are left open.  **A**: a last block 3 after a block `x ≥ 6`.  Here `j = 1`, and `pre` may take two supply
words (`u = 2 > j`), which `recur_sound` does not cover; where it does, the last block is `2 + c` with `c ≥ 0`, so a
halt needs `c = 2` (last block 4).  Computed: `c` is 0 (with `u = 2`) or at least 3, never 1, 2 or 4, and the next pass
start always safe (`py/blocks.py chain`).  **B**: a last block 6 with `c = 0`.  That one does occur on good lists (for
example `8 6 → 2 11 4`, `2 7 6 → 2 13 4`, `4 3 6 → 8 5 4`), so ruling it out needs the history: which pass starts with last block 6 the run can
reach, which comes back to 9 with `c = 0`, 2 after a 3, and 6 with `c = 2`, and so on down the chain.
-/

namespace BB6c

/-- `pre` stops on the blocks `ls` (the assumption of `recur_next`). -/
def PreStops (ls : List Nat) : Prop := ∃ f L p u, pre f ⟨.B, 0, pad 1 ls, [0, 1]⟩ 0 = some (L, p, u)

/-- A pass start that the results so far keep: good, with at least two blocks, and a last block 3 only after a block
of at least 6. -/
def Safe (ls : List Nat) (n : Nat) : Prop := Good ls n ∧ ls ≠ [] ∧ (n = 2 → 6 ≤ ls.headD 0)

/-- **Good starts do not stay good**: `3 6` is good, and halts two passes later (`3 6 → 2 7 4 → 2 13 1`), evaluated by
the kernel. -/
theorem three_six_halts : Good [3] 5 ∧ TM.Halts trans (K [3] 5) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  exact passes_sound 1000 3 (ls := [3]) (n := 5) (o := .halt) (by decide +kernel)

/-- `2 2 3` is good and halts on the next pass (`recur_two_three_halts`). -/
theorem two_two_three_halts : Good [2, 2] 2 ∧ TM.Halts trans (K [2, 2] 2) :=
  ⟨⟨by decide, by decide, by decide⟩, recur_two_three_halts 2 []⟩

/-- `recur_next` with the shape of the result kept: the next pass start has at least two blocks. -/
theorem recur_next_cons {ls : List Nat} (hg : ∀ b ∈ ls, 2 ≤ b) {f : Nat} {L : List Nat} {p u : Nat}
    (e : pre f ⟨.B, 0, pad 1 ls, [0, 1]⟩ 0 = some (L, p, u)) (j : Nat) (hj : 2 ≤ j) :
    ∃ ls' n, (∀ b ∈ ls', 2 ≤ b) ∧ ls' ≠ [] ∧ Reaches (K ls (3 * j - 1)) (K ls' n) ∧
      2 * j ≤ n + 1 + (if ls.headD 0 = 2 then 1 else 0) := by
  obtain ⟨a, b, M, rfl, hc, hb, ⟨g, z, rfl, hgg, hz⟩, hu⟩ := offset_bound hg e
  have hle : 2 * j ≤ a + 2 * (p + (j - u)) + (if ls.headD 0 = 2 then 1 else 0) := by
    split at hc <;> split <;> omega
  have hpos : 1 ≤ a + 2 * (p + (j - u)) := by split at hle <;> omega
  have r := recur_sound e j (by omega) (by omega) hpos
  refine ⟨(b + 2 * ((p + (j - u) + 1) / 2)) :: g, a + 2 * (p + (j - u)) - 1, ?_, List.cons_ne_nil _ _, ?_,
    by omega⟩
  · exact List.forall_mem_cons.2 ⟨by omega, hgg⟩
  · have hK : K ((b + 2 * ((p + (j - u) + 1) / 2)) :: (g ++ z)) (a + 2 * (p + (j - u)) - 1) =
        K ((b + 2 * ((p + (j - u) + 1) / 2)) :: g) (a + 2 * (p + (j - u)) - 1) := by
      unfold K
      rw [show (b + 2 * ((p + (j - u) + 1) / 2)) :: (g ++ z) = ((b + 2 * ((p + (j - u) + 1) / 2)) :: g) ++ z from rfl,
        lt_app_allZ hz]
    exact reaches_eq r hK

/-- A covered pass keeps `Safe`: it keeps `Good` (`next_good`), always leaves at least two blocks, and makes a last
block 3 only from a last block 7, the block to its left gaining 6. -/
theorem next_safe {ls ls' : List Nat} {n n' : Nat} (hs : Safe ls n) (h : next ls n = some (ls', n')) :
    Safe ls' n' := by
  obtain ⟨hg, hne, -⟩ := hs
  refine ⟨next_good hg h, ?_, ?_⟩
  · dsimp only [next] at h
    split at h; · cases h; exact List.cons_ne_nil _ _
    split at h; · cases h; exact List.cons_ne_nil _ _
    split at h; · cases h; exact List.cons_ne_nil _ _
    split at h; · cases h; exact List.cons_ne_nil _ _
    split at h; · cases h; exact List.cons_ne_nil _ _
    cases h
  · have hx : 2 ≤ ls.headD 0 := by
      cases ls with
      | nil => exact absurd rfl hne
      | cons a _ => exact hg.1 a (List.mem_cons_self ..)
    intro h2
    dsimp only [next] at h
    split at h; · cases h; simp only [List.headD]; omega
    split at h; · cases h; omega
    split at h; · cases h; simp only [List.headD]; omega
    split at h; · cases h; omega
    split at h; · cases h; omega
    cases h

/-- **From a safe pass start whose last block is neither 3 nor 6, the next pass start is safe**, if `pre` stops
(kernel only).  Covered passes by `next_safe`; a recursive pass has last block `3j` with `j ≥ 3`, so by `recur_next`
the next last block is at least `2j - 1 ≥ 5`. -/
theorem safe_pass {ls : List Nat} {n : Nat} (hs : Safe ls n) (h3 : n ≠ 2) (h6 : n ≠ 5) (hp : PreStops ls) :
    ∃ ls' n', Safe ls' n' ∧ Reaches (K ls n) (K ls' n') := by
  by_cases hr : n % 3 = 2
  · obtain ⟨f, L, p, u, e⟩ := hp
    obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j - 1 := ⟨(n + 1) / 3, by omega⟩
    obtain ⟨ls', n', hb, hne, hR, hle⟩ := recur_next_cons hs.1.1 e j (by omega)
    refine ⟨ls', n', ⟨⟨hb, ?_, ?_⟩, hne, ?_⟩, hR⟩ <;> split at hle <;> omega
  · obtain ⟨⟨ls', n'⟩, e⟩ := Option.isSome_iff_exists.1 (next_isSome ls hs.1.2.1 hr)
    exact ⟨ls', n', next_safe hs e, next_sound e⟩

/-- **A last block 6 after a block 2** gives a last block 3 after a block of at least 10 (`recur_two`), which is safe,
for every list further left. -/
theorem six_after_two {d : Nat} {M : List Nat} (hg : Good (2 :: d :: M) 5) :
    Safe ((d + 8) :: M) 2 ∧ Reaches (K (2 :: d :: M) 5) (K ((d + 8) :: M) 2) := by
  have hb := hg.1
  have hd : 2 ≤ d := hb d (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  refine ⟨⟨⟨cons_good (by omega) (tail_good (tail_good hb)), by omega, by omega⟩, List.cons_ne_nil _ _,
    fun _ => by simp only [List.headD]; omega⟩, ?_⟩
  simpa using recur_two d 0 M

/-- **A last block 6 after a block other than 2** (kernel only), if `pre` stops: the next pass start has blocks of at
least 2 and last block `4 + c` with `c ≥ 0`.  If `c = 0` (last block 4) the machine halts on the pass after; otherwise
the next pass start is safe. -/
theorem six_pass {ls : List Nat} (hg : Good ls 5) (hx : ls.headD 0 ≠ 2) (hp : PreStops ls) :
    ∃ ls' c, Reaches (K ls 5) (K ls' (3 + c)) ∧ (c = 0 → TM.Halts trans (K ls 5)) ∧ (c ≠ 0 → Safe ls' (3 + c)) := by
  obtain ⟨f, L, p, u, e⟩ := hp
  obtain ⟨ls', n', hb, hne, hR, hle⟩ := recur_next_cons hg.1 e 2 (by omega)
  simp only [hx, ↓reduceIte] at hle
  refine ⟨ls', n' - 3, ?_, fun h0 => ?_, fun h0 => ⟨⟨hb, by omega, by omega⟩, hne, by omega⟩⟩
  · rw [show 3 + (n' - 3) = n' by omega]; exact hR
  · rw [show n' = 3 by omega] at hR
    rw [K_pad1 ls' 3] at hR
    exact halts_of_reaches (hR.trans (kA0 _ _))

/-- The run from blank tape reaches a safe pass start: `10 3` (`blank_passes`). -/
theorem blank_safe : Safe [10] 2 ∧ Reaches init (K [10] 2) :=
  ⟨⟨⟨by decide, by decide, by decide⟩, List.cons_ne_nil _ _, fun _ => by decide⟩, blank_passes⟩

end BB6c
