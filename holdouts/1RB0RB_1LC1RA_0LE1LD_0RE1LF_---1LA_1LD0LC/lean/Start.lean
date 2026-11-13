import Machine

/-!
# The counter after the last left record

The leftmost cell visited by the first 10^16 steps is reached at step 234,511.  At step 235,323 the head is in state
A on the last written cell and the tape is `Q (01)^333 1`, a fixed 84-cell prefix `Q` followed by 333 pairs `0 1`.
Checked by `native_decide` on the list simulator of `tools/lean/TM/Fin.lean`.
-/

namespace H157319

open TM

/-- Cells written as a string of `0`/`1`, left to right. -/
def bits (s : String) : List Bool := s.toList.map (· == '1')

/-- The 84 cells left of the counter. -/
def Q : List Bool :=
  bits "110111110101010101110101111101111101010111010101011111010101110101010111011111011111"

/-- 235,323 steps from blank tape reach `Q (01)^333 A> 1` (left list nearest the head first). -/
theorem counter_start :
    steps 235323 init =
      some (FCfg.toCfg ⟨(Q ++ (List.replicate 333 [false, true]).flatten).reverse, [true], .A⟩) :=
  blank_reaches trans (by native_decide)

end H157319
