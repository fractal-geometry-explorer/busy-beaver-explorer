import Machine
import TM.RSim

/-!
# 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1RF: no halt in the first 10^8 steps, by the checked accelerated simulator

`TM/RSim.lean` is rsim (the accelerated simulator of `c/rsim_fast.cpp`) rebuilt so that every move is proved,
including its trip-level jumps: each jump is checked by running one period symbolically, with the counts of the runs
as linear forms. This file runs it from blank tape far enough for continuous integration; `RSimLong.lean` (checked
by `check_long.sh`, with compiled code loaded) runs it much further.
-/

namespace H63327

open TM TM.RS

deriving instance Hashable for St

/-- No halt in the first 10^8 steps (`native_decide` on the checked simulator). -/
theorem rsim_1e8 : ∃ c, TM.steps trans 100000000 (TM.blankCfg .A) = some c :=
  run_ok trans .A 100000000 1000000000 (by native_decide)

end H63327
