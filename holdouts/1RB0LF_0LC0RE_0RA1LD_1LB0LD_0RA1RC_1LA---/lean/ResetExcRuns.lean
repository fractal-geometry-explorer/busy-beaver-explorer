import ResetExc

/-!
# The reset map without hypotheses for the first 26 phases of both runs

`cOrbit` (`ResetExc.lean`) checks every tail excursion of `k` phases in a row; `native_decide` evaluates it on the
two runs' first resets.  `check_native.sh` runs this file with the checker compiled to native code.

* `goodN_own`, `goodN_twin`: the hypotheses `GoodN 26` of `ResetMap.lean` hold for both runs.
* `reach_own_phases`: this machine's run from blank tape reaches `Reset 1620646 T` (phase 26: 40, 61, 94, 142,
  ..., 1,620,646), so it makes no halt before.
* `reach_twin_phases`: the same for this table started in state D (the twin
  1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---, `twin_halts_iff`): `Reset 2099734 T` (52, 79, 121, ..., 2,099,734).

`ResetExcLong.lean` (by hand, not in CI) does the same for more phases.
-/

namespace H129771

open TM TM.EX

theorem check_own : cOrbit 26 40 (ofList ws L0own) = true := by native_decide
theorem check_twin : cOrbit 26 52 (ofList ws L0twin) = true := by native_decide

theorem goodN_own : GoodN 26 40 T0own := by rw [T0own_eq]; exact cOrbit_spec _ _ _ check_own
theorem goodN_twin : GoodN 26 52 T0twin := by rw [T0twin_eq]; exact cOrbit_spec _ _ _ check_twin

theorem fit_own : fit 26 40 = 1620646 := by decide
theorem fit_twin : fit 26 52 = 2099734 := by decide

/-- This machine's run from blank tape reaches the reset of phase 26, `X = 1,620,646`. -/
theorem reach_own_phases : ∃ n T', 26 ≤ n ∧ steps n init = some (Reset 1620646 T') := by
  obtain ⟨n, T', hn, h⟩ := reach_of_check (by omega) (T0own_eq ▸ reach_own) 26 check_own
  exact ⟨n, T', by omega, fit_own ▸ h⟩

/-- The twin (this table from blank tape, started in D) reaches the reset of phase 26, `X = 2,099,734`. -/
theorem reach_twin_phases : ∃ n T', 26 ≤ n ∧ steps n (blankCfg .D) = some (Reset 2099734 T') := by
  obtain ⟨n, T', hn, h⟩ := reach_of_check (by omega) (T0twin_eq ▸ reach_twin) 26 check_twin
  exact ⟨n, T', by omega, fit_twin ▸ h⟩

end H129771
