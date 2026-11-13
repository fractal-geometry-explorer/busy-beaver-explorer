import Machine

/-!
# The counter after the last left record

The leftmost cell visited by the first 10^9 steps is reached at step 29,281.  At step 29,479 the head is in state A
on the last written cell and the tape is `Q (110101)^26 1 1 1`, a fixed 40-cell prefix `Q` followed by a counter of
26 copies of `110101`.  Checked by `native_decide` on the list simulator of `tools/lean/TM/Fin.lean`.
-/

namespace H157503

open TM

/-- Cells written as a string of `0`/`1`, left to right. -/
def bits (s : String) : List Bool := s.toList.map (· == '1')

/-- The 40 cells left of the counter. -/
def Q : List Bool := bits "1111010101011101110111011101010111010101"

/-- 29,479 steps from blank tape reach `Q (110101)^26 1 1 A> 1` (left list nearest the head first). -/
theorem counter_start :
    steps 29479 init =
      some (FCfg.toCfg ⟨(Q ++ (List.replicate 26 (bits "110101")).flatten ++ bits "11").reverse, [true], .A⟩) :=
  blank_reaches trans (by native_decide)

end H157503
