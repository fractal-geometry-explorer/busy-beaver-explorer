import Machine
import TM.RSim

/-!
# The long run of the checked accelerated simulator, as a compiled definition

Compiled with the machine (`check_long.sh`), so that `RSimLong.lean` evaluates it with specialized native code.
-/

namespace H83242

open TM TM.RS

deriving instance Hashable for St

/-- The target of the long run. -/
def longN : Nat := 8000000000000000

/-- The steps the checked simulator accounts for, run towards `longN` from blank tape. -/
def longRun : Nat := (runTo trans longN 1000000000000000 (TM.RS.init trans .A)).n

end H83242
