import Phase

/-! # The run from blank tape enters the main regime -/

namespace H100726

open TM

/-- The cells of `P a b`, as a list. -/
def Plist (a b : Nat) : List Bool :=
  List.replicate 6 false ++ (List.replicate a w1).flatten ++ [true, false, true, true, true] ++
    (List.replicate b w2).flatten ++ tail1

/-- After 30,224 steps from blank tape the machine is in the main regime, at `P 13 27` (kernel). -/
theorem reach_P : steps 30224 init = some (P 13 27) := by
  have h : TM.fsteps trans 30224 (FCfg.blank .A) = some ⟨[], Plist 13 27, .F⟩ := by decide +kernel
  have e : (⟨[], Plist 13 27, .F⟩ : FCfg St).toCfg = P 13 27 := rfl
  rw [← e]
  exact blank_reaches trans h

/-- So the run passes through `P (13 + 6k) (27 - 2k)` for k up to 13, ending at `P 91 1` (kernel). -/
theorem reach_P_end : ∃ t, steps t init = some (P 91 1) := by
  obtain ⟨t, ht⟩ := P_iter 13 13 0
  exact ⟨30224 + t, steps_seq trans reach_P ht⟩

end H100726
