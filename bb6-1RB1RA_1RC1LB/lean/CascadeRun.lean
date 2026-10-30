import Cascade

/-!
# No halt in the first 4.4·10³⁷ steps, by the periodic tables

The plan below (from `python3 py/superrun.py plan 35 6`) builds the tables of the last 1, 2, …, 35 blocks one level at a
time, each after the given number of passes of the table before, and then makes 6 passes of the table for 35 levels
(8.8·10¹⁶ super steps each).  `drive` checks every table as it builds it (the level must come back to its block), and
`runs_of_drive` turns the run into a statement about the machine.  The evaluation is `native_decide`, so the bound
also trusts Lean's compiler; it ends after 675059516082932571 super steps, at machine step 44405698359075157430295693458238990120 (about 4 minutes).
-/

namespace BB6b

open TM

/-- Passes of the current table, and the passes over which the next level comes back (0 at the end). -/
def plan35 : List (Nat × Nat) := [(7, 4), (3, 2), (5, 4), (5, 4), (3, 2), (5, 4), (5, 4), (2, 1), (5, 4), (5, 4), (6, 5), (2, 1), (5, 4), (5, 4), (3, 2), (6, 5), (5, 4), (6, 5), (5, 4), (5, 4), (5, 4), (5, 4), (6, 5), (2, 1), (2, 1), (5, 4), (5, 4), (5, 4), (3, 2), (2, 1), (3, 2), (5, 4), (5, 4), (5, 4), (5, 4), (6, 0)]

theorem drive_plan35 : (drive plan35 T₀ (0, 0) [6, 1] 136).map Prod.snd = some 44405698359075157430295693458238990120 := by
  native_decide

/-- **No halt in the first 44405698359075157430295693458238990120 steps** (4.4·10³⁷). -/
theorem blank_runs_4e37 : ∃ c, steps 44405698359075157430295693458238990120 init = some c := by
  have h := drive_plan35
  cases e : drive plan35 T₀ (0, 0) [6, 1] 136 with
  | none => rw [e] at h; cases h
  | some x =>
    obtain ⟨U, t⟩ := x
    rw [e] at h
    cases h
    exact runs_of_drive plan35 U _ e

end BB6b

#print axioms BB6b.drive_sound
#print axioms BB6b.build_rep
#print axioms BB6b.runs_of_drive
#print axioms BB6b.blank_runs_4e37
