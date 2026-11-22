import RSimRun

/-!
# 1RB0RF_0LC---_1LD1LC_1RE0LA_1RA1RD_0RD1RF: no halt in the first `longN` steps

By the checked accelerated simulator of `TM/RSim.lean` (every move proved, every jump checked by a symbolic period),
evaluated by `native_decide` with compiled code loaded: `check_long.sh`.
-/

namespace H83242

open TM TM.RS

theorem rsim_long : ∃ c, TM.steps trans longN (TM.blankCfg .A) = some c :=
  run_ok trans .A longN 1000000000000000 (by native_decide : longN ≤ longRun)

end H83242
