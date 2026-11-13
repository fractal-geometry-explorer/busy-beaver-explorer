import Nested

/-!
# A long run, from blank tape, through the first nested run

From the first sweep configuration (`reach_D0`, step 2,340) the run-length sweep program `runR` (`Rle.lean`) goes
5,373 sweeps to the first nested run (step 115,650,647); `nested_run` (`Nested.lean`) crosses it, to step
231,327,122; from there `runR` goes on for 10,000,000 sweeps, to step 400,000,471,326,994, with no sweep left
uncovered (in this stretch no carry reaches the left end).  Both runs are evaluated by compiled code
(`native_decide`).  So the machine does not halt in its first 4·10¹⁴ steps (`no_halt_long`).
-/

namespace H115779

open TM

/-- The first sweep configuration, on runs (`D0 = [0, 2, 2, 1, 1, 1, 1, 1, 2, 0]`). -/
def s0R : MR := ⟨3, [(0, 1), (2, 1), (1, 5), (2, 2), (0, 1)], false⟩

theorem s0R_cfg : s0R.cfg = P (raw 3) D0 := rfl

/-- Where the first nested run starts and where it ends, on runs. -/
def sA : MR := ⟨12, [(1, 2686), (3, 1), (1, 5), (3, 1), (1, 1)], false⟩
def sB : MR := ⟨15, [(1, 2686), (2, 1), (0, 1), (1, 6), (0, 2), (2, 1)], true⟩

theorem sA_ev : ev sA.rs = dsA := by simp only [sA, dsA, ev]; rfl
theorem sB_ev : ev sB.rs = dsB := by simp only [sB, dsB, ev]; rfl

theorem run1_value : runR 5373 s0R 2340 = some (sA, 115650647) := by native_decide

theorem reach_A : steps 115650647 init = some sA.cfg :=
  runR_sound 5373 s0R 2340 sA 115650647 run1_value (by rw [s0R_cfg]; exact reach_D0)

theorem reach_B : steps 231327122 init = some sB.cfg := by
  have h : sA.cfg = P (raw 12) dsA := by unfold MR.cfg; rw [sA_ev]; rfl
  have h' : sB.cfg = Q (raw 15) dsB := by unfold MR.cfg; rw [sB_ev]; rfl
  have hA : steps 115650647 init = some (P (raw 12) dsA) := by rw [← h]; exact reach_A
  rw [h']
  exact steps_congr trans (by decide) (steps_seq trans hA nested_run)

theorem run2_value : ((runR 10000000 sB 231327122).map (·.2)) = some 400000471326994 := by native_decide

/-- **No halt in the first 400,000,471,326,994 steps** (about 4·10¹⁴). -/
theorem no_halt_long : ∃ c, steps 400000471326994 init = some c := by
  have h := run2_value
  cases e : runR 10000000 sB 231327122 with
  | none => rw [e] at h; cases h
  | some x =>
    rw [e] at h
    obtain ⟨s', t'⟩ := x
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨_, runR_sound 10000000 sB 231327122 s' _ e reach_B⟩

end H115779
