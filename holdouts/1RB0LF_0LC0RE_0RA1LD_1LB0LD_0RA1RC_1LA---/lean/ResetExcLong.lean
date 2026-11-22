import ResetExc

/-!
# The reset map without hypotheses for the first 36 phases of both runs (checked by hand)

`cOrbit` (`ResetExc.lean`) checks every tail excursion of `k` phases in a row; `native_decide` evaluates it on the
two runs' first resets.

* `goodN_own36`, `goodN_twin36`: the hypotheses `GoodN 36` of `ResetMap.lean` hold for both runs.
* `reach_own_phases36`: this machine's run from blank tape reaches `Reset 93454756 T` (phase 36: 40, 61, 94, 142,
  ..., 93,454,756), so it makes no halt before.
* `reach_twin_phases36`: the same for this table started in state D (the twin
  1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---, `twin_halts_iff`): `Reset 121081390 T` (52, 79, 121, ..., 121,081,390).

This file is not in `check.sh` (CI checks `ResetExcRuns.lean`, 26 phases); it takes about an hour per machine with
the native checker: `./check.sh` once, then `./check_native.sh ResetExcLong.lean`.
-/

namespace H129771

open TM TM.EX

theorem check_own36 : cOrbit 36 40 (ofList ws L0own) = true := by native_decide
theorem check_twin36 : cOrbit 36 52 (ofList ws L0twin) = true := by native_decide

theorem goodN_own36 : GoodN 36 40 T0own := by rw [T0own_eq]; exact cOrbit_spec _ _ _ check_own36
theorem goodN_twin36 : GoodN 36 52 T0twin := by rw [T0twin_eq]; exact cOrbit_spec _ _ _ check_twin36

theorem fit_own36 : fit 36 40 = 93454756 := by decide
theorem fit_twin36 : fit 36 52 = 121081390 := by decide

/-- This machine's run from blank tape reaches the reset of phase 36, `X = 93,454,756`. -/
theorem reach_own_phases36 : ∃ n T', 36 ≤ n ∧ steps n init = some (Reset 93454756 T') := by
  obtain ⟨n, T', hn, h⟩ := reach_of_check (by omega) (T0own_eq ▸ reach_own) 36 check_own36
  exact ⟨n, T', by omega, fit_own36 ▸ h⟩

/-- The twin (this table from blank tape, started in D) reaches the reset of phase 36, `X = 121,081,390`. -/
theorem reach_twin_phases36 : ∃ n T', 36 ≤ n ∧ steps n (blankCfg .D) = some (Reset 121081390 T') := by
  obtain ⟨n, T', hn, h⟩ := reach_of_check (by omega) (T0twin_eq ▸ reach_twin) 36 check_twin36
  exact ⟨n, T', by omega, fit_twin36 ▸ h⟩

end H129771
