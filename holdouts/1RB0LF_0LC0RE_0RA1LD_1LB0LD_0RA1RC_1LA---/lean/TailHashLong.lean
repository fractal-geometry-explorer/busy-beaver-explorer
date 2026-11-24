import TailHash

/-!
# The reset map without hypotheses for the first 130 phases of both runs, the carries by Hashlife

`cOrbitF` (`TailHash.lean`) checks every tail excursion of `k` phases in a row, the carries of a phase `2^j` at a
time by symbolic transforms that are proved for every tail of their family; `native_decide` evaluates it on the two
runs' first resets.  Not in `check.sh` (CI checks `TailHashRuns.lean`, 40 phases): run `./check.sh` once, then `./check_native.sh TailHashLong.lean` (about 25 minutes, 4 GB).

* `goodNF_own130`, `goodNF_twin130`: the hypotheses `GoodN 130` of `ResetMap.lean` hold for both runs.
* `reachF_own130`: this machine's run from blank tape reaches `Reset 3335644625007427579461373 T` (phase 130), so it makes no halt before.
* `reachF_twin130`: the same for this table started in state D (the twin
  1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---, `twin_halts_iff`): `Reset 4321711362379564880782897 T`.
-/

namespace H129771

open TM

theorem checkF_own130 : cOrbitF 130 40 (toS (EX.ofList ws L0own)) {} = true := by native_decide
theorem checkF_twin130 : cOrbitF 130 52 (toS (EX.ofList ws L0twin)) {} = true := by native_decide

theorem goodNF_own130 : GoodN 130 40 T0own := by rw [T0own_tp]; exact cOrbitF_spec _ _ _ _ checkF_own130
theorem goodNF_twin130 : GoodN 130 52 T0twin := by rw [T0twin_tp]; exact cOrbitF_spec _ _ _ _ checkF_twin130

theorem fitF_own130 : fit 130 40 = 3335644625007427579461373 := by decide +kernel
theorem fitF_twin130 : fit 130 52 = 4321711362379564880782897 := by decide +kernel

/-- This machine's run from blank tape reaches the reset of phase 130, `X = 3,335,644,625,007,427,579,461,373`. -/
theorem reachF_own130 : ∃ n T', 130 ≤ n ∧ steps n init = some (Reset 3335644625007427579461373 T') := by
  obtain ⟨n, T', hn, h⟩ := reach_of_checkF (by omega) (T0own_tp ▸ reach_own) 130 checkF_own130
  exact ⟨n, T', by omega, fitF_own130 ▸ h⟩

/-- The twin (this table from blank tape, started in D) reaches the reset of phase 130, `X = 4,321,711,362,379,564,880,782,897`. -/
theorem reachF_twin130 : ∃ n T', 130 ≤ n ∧ steps n (blankCfg .D) = some (Reset 4321711362379564880782897 T') := by
  obtain ⟨n, T', hn, h⟩ := reach_of_checkF (by omega) (T0twin_tp ▸ reach_twin) 130 checkF_twin130
  exact ⟨n, T', by omega, fitF_twin130 ▸ h⟩

end H129771
