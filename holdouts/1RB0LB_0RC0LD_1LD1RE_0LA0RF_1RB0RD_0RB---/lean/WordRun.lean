import Word

/-! The first 2,000 rounds of the run, computed on words by `run` (`lean/Word.lean`) and checked by evaluation
(`native_decide`): none of them halts. -/

namespace H28035

open TM

/-- `true` when the computation ends with a word. -/
def Res.isOk : Res → Bool
  | .ok _ => true
  | _ => false

theorem run_2000_ok : (run 100000 2000).isOk = true := by native_decide

/-- The machine runs through 2,000 rounds from blank tape: after some `n ≥ 2000` steps it is at `0^∞ A> 1 0 w 0^∞`. -/
theorem rounds_2000 : ∃ n w, 2000 ≤ n ∧ steps n init = some (LE (app w blank)) := by
  have h := run_2000_ok
  cases e : run 100000 2000 with
  | ok w =>
    obtain ⟨n, hn, hs⟩ := (run_sound 100000 2000).1 w e
    exact ⟨n, w, hn, hs⟩
  | halt => rw [e] at h; cases h
  | stuck => rw [e] at h; cases h

end H28035
