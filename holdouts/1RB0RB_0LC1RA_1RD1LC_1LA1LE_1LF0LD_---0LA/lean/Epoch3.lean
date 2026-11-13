import Machine

/-!
# The start of the third epoch

After 589,506 steps from blank tape the tape is `P (01)^520` with the head in state A on the blank cell right of it,
where `P` is the 106-cell word below.  This is where the base-4 countdown of the third epoch starts (see the
README); the claims about how long that countdown lasts are not proved here.  Checked by `native_decide` on the
list simulator of `tools/lean/TM/Fin.lean`.
-/

namespace H77294

open TM

/-- Cells written as a string of `0`/`1`, left to right. -/
def bits (s : String) : List Bool := s.toList.map (· == '1')

/-- The 106 cells left of the counter at the start of the third epoch. -/
def P : List Bool :=
  bits "1111010101110101011101010111010101110101011101010101110101011101011101010111010101110101110101011101010111"

theorem P_length : P.length = 106 := by decide

/-- 589,506 steps from blank tape reach `P (01)^520 A>` (left list nearest the head first). -/
theorem epoch3_start :
    steps 589506 init =
      some (FCfg.toCfg ⟨(P ++ (List.replicate 520 [false, true]).flatten).reverse, [false], .A⟩) :=
  blank_reaches trans (by native_decide)

end H77294
