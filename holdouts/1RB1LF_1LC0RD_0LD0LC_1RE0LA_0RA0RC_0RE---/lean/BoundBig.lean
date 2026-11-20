import Bound

/-!
# 1RB1LF_1LC0RD_0LD0LC_1RE0LA_0RA0RC_0RE---: no halt in the first 10^100 steps

The run of `Bound.lean` taken further; checked by `check_big.sh`, which loads compiled code for the evaluation.
-/

namespace H69016

theorem bound_big : ∃ c, steps (10 ^ 100) init = some c :=
  bound_of_run (fuel := 10 ^ 15) (by native_decide)

end H69016
