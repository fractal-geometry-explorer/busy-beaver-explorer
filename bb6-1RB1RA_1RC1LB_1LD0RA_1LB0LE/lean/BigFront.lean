import Large

/-!
# A large first block does not bound the halvings

The first block changes only at a few kinds of pass (a stop at the second block, a stop at the third block of a
longer list, an even last block on two or three blocks). Between two changes it is only halved, by front stops, so a
stop at a first block of 1 needs a change to leave it at 2^R − 1 and then R − 1 halvings (the Mersenne lemma). The
lists of `Run7.lean` and `Large.lean` that do this have a tiny first block (`wL`: 1.4·10⁻⁵ of the ones), while the
orbit keeps its first block at least 7.6% of the ones at every change after pass 50 (10⁸ passes, computed,
`py/bigfront.py orbit`). The idea tested here (`notes/LAB_NOTES.md`, 1 November, "Bound the halvings by the first
block at a change") was that a large first block bounds the number of halvings.

It does not, at least not at these sizes. Both lists below have 4 | ones, `Good`, |ψ| within the range the orbit
shows (−21..24 for `wH`, −23 for `wF`), a first block 255 = 2^8 − 1 that is at least 1/5 of the ones, and a run of
passes that only halve it, 255 → 1, ending with a stop at a first block of 1 (`wF_one`, `wH_one`), the only way the
machine halts (`halts_only_by_one`):

    wF = [255, 512, 32, 60, 32, 64, 9]               ψ = −23, ones 964   (first block 26% of the ones)
    wH = [255, 528, 48, 24, 8, 32, 64, 128, 129]     ψ = 1,   ones 1216  (first block 21% of the ones)

(first block first; Lean's lists are nearest first). They were found by an exact search (`py/bigfront.py search`);
for every R from 4 to 8 such lists exist with the first block at least 1/5 of the ones and |ψ| ≤ 21. Kernel only.
-/

namespace BB6d

/-- The first block and the block count at each of the first `n` pass starts from `zs`. -/
def firsts (n : Nat) (zs : List Nat) : List (Nat × Nat) :=
  (List.range n).map fun i =>
    match run i zs with
    | .ok ys => (ys.getLast?.getD 0, ys.length)
    | _ => (0, 0)

/-- `[255, 512, 32, 60, 32, 64, 9]` (first block first). -/
def wF : List Nat := [9, 64, 32, 60, 32, 512, 255]

theorem wF_psi : psi wF = -23 := by decide
theorem wF_sum : wF.sum % 4 = 0 := by decide
theorem wF_good : Good wF := by
  simp only [wF, Good]; decide
theorem wF_first : wF.getLast? = some (2 ^ 8 - 1) := by decide
/-- The first block is at least a quarter of the ones. -/
theorem wF_large : wF.sum ≤ 4 * (2 ^ 8 - 1) := by decide

/-- Nineteen pass starts: the first block 255 is only halved. -/
theorem wF_firsts : firsts 19 wF =
    [(255, 7), (127, 8), (127, 7), (127, 6), (63, 7), (63, 6), (63, 5), (31, 6), (31, 5), (15, 6), (15, 5),
     (7, 6), (7, 5), (3, 6), (3, 5), (1, 6), (1, 5), (1, 4), (1, 3)] := by decide

/-- The nineteenth pass stops at a first block of 1. -/
theorem wF_one : run 19 wF = .one := by decide

/-- `[255, 528, 48, 24, 8, 32, 64, 128, 129]` (first block first). -/
def wH : List Nat := [129, 128, 64, 32, 8, 24, 48, 528, 255]

theorem wH_psi : psi wH = 1 := by decide
theorem wH_sum : wH.sum % 4 = 0 := by decide
theorem wH_good : Good wH := by
  simp only [wH, Good]; decide
theorem wH_first : wH.getLast? = some (2 ^ 8 - 1) := by decide
/-- The first block is at least a fifth of the ones. -/
theorem wH_large : wH.sum ≤ 5 * (2 ^ 8 - 1) := by decide

/-- Twenty-one pass starts: the first block 255 is only halved. -/
theorem wH_firsts : firsts 21 wH =
    [(255, 9), (127, 10), (127, 9), (127, 8), (127, 7), (63, 8), (63, 7), (31, 8), (31, 7), (31, 6), (15, 7),
     (15, 6), (15, 5), (15, 4), (7, 5), (7, 4), (3, 5), (3, 4), (1, 5), (1, 4), (1, 3)] := by decide

/-- The twenty-first pass stops at a first block of 1. -/
theorem wH_one : run 21 wH = .one := by decide

end BB6d
