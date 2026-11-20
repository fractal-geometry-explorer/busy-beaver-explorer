import Bound

/-!
# 1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---: no halt in the first 10^100 steps

The run of `Bound.lean` taken further; checked by `check_big.sh`, which loads compiled code for the evaluation.
-/

namespace H72107

theorem bound_big : ∃ c, steps (10 ^ 100) init = some c :=
  bound_of_run (fuel := 10 ^ 15) (by native_decide)

end H72107
