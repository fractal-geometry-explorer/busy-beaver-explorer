import TailHash

/-!
# The reset map without hypotheses for the first 40 phases of both runs, the carries by Hashlife

`cOrbitF` (`TailHash.lean`) checks every tail excursion of `k` phases in a row, the carries of a phase `2^j` at a
time by symbolic transforms that are proved for every tail of their family; `native_decide` evaluates it on the two
runs' first resets.  `check_native.sh` runs this file (in CI, about two minutes); `TailHashLong.lean` does more phases by hand.

* `goodNF_own40`, `goodNF_twin40`: the hypotheses `GoodN 40` of `ResetMap.lean` hold for both runs.
* `reachF_own40`: this machine's run from blank tape reaches `Reset 473114716 T` (phase 40), so it makes no halt before.
* `reachF_twin40`: the same for this table started in state D (the twin
  1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---, `twin_halts_iff`): `Reset 612974545 T`.
-/

namespace H129771

open TM

theorem checkF_own40 : cOrbitF 40 40 (toS (EX.ofList ws L0own)) {} = true := by native_decide
theorem checkF_twin40 : cOrbitF 40 52 (toS (EX.ofList ws L0twin)) {} = true := by native_decide

theorem goodNF_own40 : GoodN 40 40 T0own := by rw [T0own_tp]; exact cOrbitF_spec _ _ _ _ checkF_own40
theorem goodNF_twin40 : GoodN 40 52 T0twin := by rw [T0twin_tp]; exact cOrbitF_spec _ _ _ _ checkF_twin40

theorem fitF_own40 : fit 40 40 = 473114716 := by decide +kernel
theorem fitF_twin40 : fit 40 52 = 612974545 := by decide +kernel

/-- This machine's run from blank tape reaches the reset of phase 40, `X = 473,114,716`. -/
theorem reachF_own40 : ∃ n T', 40 ≤ n ∧ steps n init = some (Reset 473114716 T') := by
  obtain ⟨n, T', hn, h⟩ := reach_of_checkF (by omega) (T0own_tp ▸ reach_own) 40 checkF_own40
  exact ⟨n, T', by omega, fitF_own40 ▸ h⟩

/-- The twin (this table from blank tape, started in D) reaches the reset of phase 40, `X = 612,974,545`. -/
theorem reachF_twin40 : ∃ n T', 40 ≤ n ∧ steps n (blankCfg .D) = some (Reset 612974545 T') := by
  obtain ⟨n, T', hn, h⟩ := reach_of_checkF (by omega) (T0twin_tp ▸ reach_twin) 40 checkF_twin40
  exact ⟨n, T', by omega, fitF_twin40 ▸ h⟩

end H129771
