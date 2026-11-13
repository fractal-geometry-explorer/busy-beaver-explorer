import Machine
import Blank
import Phase
import Levels

/-! From blank tape to the first three main phases, and each of them to its turn by `main_to_turn`.
Written by `py/gen_reach.py`. -/

namespace H154944

open TM

/-- The rest of the tape at step 173: `10000110011` then blank. -/
def R0 : Tape := cons true (cons false (cons false (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true blank))))))))))

set_option maxRecDepth 100000 in
/-- After 173 steps the tape is `A>0 (10)^1 00 (10)^4 110 0 1^2 0` and `R0`, that is `P 1 4 2 R0`. -/
theorem reach_173 : steps 173 init = some (P 1 4 2 R0) := by
  have h := blank_reaches trans (q := St.A) (n := 173) (c := ⟨[], [false, true, false, false, false, true, false, true, false, true, false, true, false, true, true, false, false, true, true, false, true, false, false, false, false, true, true, false, false, true, true], .A⟩) (by native_decide)
  refine h.trans (congrArg some ?_)
  simp only [FCfg.toCfg, P, R0, rep_succ, rep_zero, app]

/-- That main phase ends at step 735 as a wall of 36 ones (the head on the last of them), followed by
`1 0 1^14 0` and `R0`. -/
theorem turn_173 : steps 735 init = some ⟨rep 35 [true] blank,
    cons true (cons true (cons false (rep 14 [true] (cons false R0)))), .A⟩ := by
  have h := steps_seq trans reach_173 (main_to_turn 4 2 R0)
  exact steps_congr trans (by simp [pcost]) h

/-- The rest of the tape at step 1225: `01010101011001110101010001100111111` then blank. -/
def R1 : Tape := cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons true (cons true (cons true (cons true blank))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
/-- After 1225 steps the tape is `A>0 (10)^1 00 (10)^14 110 0 1^2 0` and `R1`, that is `P 1 14 2 R1`. -/
theorem reach_1225 : steps 1225 init = some (P 1 14 2 R1) := by
  have h := blank_reaches trans (q := St.A) (n := 1225) (c := ⟨[], [false, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, false, false, true, true, false, false, true, false, true, false, true, false, true, false, true, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, true, true, true, true, true], .A⟩) (by native_decide)
  refine h.trans (congrArg some ?_)
  simp only [FCfg.toCfg, P, R1, rep_succ, rep_zero, app]

/-- That main phase ends at step 4967 as a wall of 96 ones (the head on the last of them), followed by
`1 0 1^34 0` and `R1`. -/
theorem turn_1225 : steps 4967 init = some ⟨rep 95 [true] blank,
    cons true (cons true (cons false (rep 34 [true] (cons false R1)))), .A⟩ := by
  have h := steps_seq trans reach_1225 (main_to_turn 14 2 R1)
  exact steps_congr trans (by simp [pcost]) h

/-- The rest of the tape at step 5625: `10010101010101000101011001111110010110000110011111110101010001100111111` then blank. -/
def R2 : Tape := cons true (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (cons false (cons true (cons false (cons true (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons true (cons false (cons false (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons false (cons true (cons false (cons true (cons false (cons true (cons false (cons false (cons false (cons true (cons true (cons false (cons false (cons true (cons true (cons true (cons true (cons true (cons true blank))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
/-- After 5625 steps the tape is `A>0 (10)^1 00 (10)^46 110 0 1^2 0` and `R2`, that is `P 1 46 2 R2`. -/
theorem reach_5625 : steps 5625 init = some (P 1 46 2 R2) := by
  have h := blank_reaches trans (q := St.A) (n := 5625) (c := ⟨[], [false, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, true, false, true, false, true, true, false, false, true, true, true, true, true, true, false, false, true, false, true, true, false, false, false, false, true, true, false, false, true, true, true, true, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, true, true, true, true, true], .A⟩) (by native_decide)
  refine h.trans (congrArg some ?_)
  simp only [FCfg.toCfg, P, R2, rep_succ, rep_zero, app]

/-- That main phase ends at step 38359 as a wall of 288 ones (the head on the last of them), followed by
`1 0 1^98 0` and `R2`. -/
theorem turn_5625 : steps 38359 init = some ⟨rep 287 [true] blank,
    cons true (cons true (cons false (rep 98 [true] (cons false R2)))), .A⟩ := by
  have h := steps_seq trans reach_5625 (main_to_turn 46 2 R2)
  exact steps_congr trans (by simp [pcost]) h

/-- The first phase: after 173 + 320 = 493 steps the tape is `P 13 0 10 R0`. -/
theorem phase_493 : steps 493 init = some (P 13 0 10 R0) := by
  have h := steps_seq trans reach_173 (phase 4 1 2 R0)
  exact steps_congr trans (by simp [pcost]) h

end H154944
