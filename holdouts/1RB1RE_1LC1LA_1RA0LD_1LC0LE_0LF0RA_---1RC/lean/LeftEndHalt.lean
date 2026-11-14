import Machine
import LeftEnd

/-!
# 1RB1RE_1LC1LA_1RA0LD_1LC0LE_0LF0RA_---1RC: the halting criterion at the left end

A carry that reaches the left end arrives in state C on the last cell of the leftmost run of 1s and crosses it three
cells at a time. If the run has 3m+2 cells the machine halts, whatever the rest of the tape is:

* `halts_left2`: `0^inf 1^(3m+1) C> 1 R` halts, for every m and every tape R.

(With 3m or 3m+1 cells the head bounces off the blank tape in state C or D and the run goes on.) Whether the run
from blank tape ever reaches such a configuration is open; `py/overflow.py` finds configurations of the same family
as the ones it visits that do.
-/

namespace H132695

open TM

theorem halts_left2 (m : Nat) (R : Tape) :
    TM.Halts trans ⟨cons true (rep m [true, true, true] blank), cons true R, .C⟩ :=
  ⟨_, _, left2 m R, rfl⟩

end H132695
