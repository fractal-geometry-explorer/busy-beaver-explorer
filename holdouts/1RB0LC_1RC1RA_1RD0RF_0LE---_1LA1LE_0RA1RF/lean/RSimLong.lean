import RSimRun

/-!
# 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF: no halt in the first `longN` steps

By the checked accelerated simulator of `TM/RSim.lean` (every move proved, every jump checked by a symbolic period),
evaluated by `native_decide` with compiled code loaded: `check_long.sh`.
-/

namespace H63327

open TM TM.RS

theorem rsim_long : ∃ c, TM.steps trans longN (TM.blankCfg .A) = some c :=
  run_ok trans .A longN 1000000000000000 (by native_decide : longN ≤ longRun)

end H63327
