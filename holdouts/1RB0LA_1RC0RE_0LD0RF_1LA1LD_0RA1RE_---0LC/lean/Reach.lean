import Phase

/-! # The run from blank tape enters the first regime with a long reservoir -/

namespace H91503

open TM

set_option maxRecDepth 100000

/-- The right end of the tape during the first regime of 853,764 steps. -/
def tail0 : List Bool :=
  [false, false, true, true, true, true, false, true, true, true, true, true, false, true, true, true]

def Qlist (a b : Nat) : List Bool :=
  (List.replicate a w5).flatten ++ wB ++ (List.replicate a w3).flatten ++ (List.replicate b wB).flatten ++ tail0

/-- After 853,764 steps from blank tape the configuration is `Q 5 ((01111)^287 tail0)` (`native_decide`). -/
theorem reach_Q : steps 853764 init = some (Q 5 (rep 287 wB (app tail0 blank))) := by
  have h : TM.fsteps trans 853764 (FCfg.blank .A) = some ⟨[], Qlist 5 287 ++ [false], .A⟩ := by native_decide
  have e : (⟨[], Qlist 5 287 ++ [false], .A⟩ : FCfg St).toCfg = Q 5 (rep 287 wB (app tail0 blank)) := by
    show (⟨blank, app (Qlist 5 287 ++ [false]) blank, .A⟩ : Config) = _
    rw [← app_app]
    show (⟨blank, app (Qlist 5 287) (cons false blank), .A⟩ : Config) = _
    rw [cons_false_blank]
    rfl
  rw [← e]
  exact blank_reaches trans h

/-- Then 286 round trips of the first regime, to `Q 291 ((01111)^1 tail0)`. -/
theorem reach_Q_end : ∃ t, steps t init = some (Q 291 (rep 1 wB (app tail0 blank))) := by
  obtain ⟨t, ht⟩ := Q_iter 286 4 0 (app tail0 blank)
  exact ⟨853764 + t, steps_seq trans reach_Q ht⟩

def Zlist (a c d : Nat) : List Bool :=
  (List.replicate a w5).flatten ++ wB ++ (List.replicate c w3).flatten ++
    [true, true, false, false, true, false, false, true, true, true, true] ++ (List.replicate d w3).flatten ++
    [true, true, false, false, true]

/-- After 4,090,752 steps from blank tape the configuration is `Z 359 293 278`, in the right-end eater regime
(`native_decide`). -/
theorem reach_Z : steps 4090752 init = some (Z 359 293 278) := by
  have h : TM.fsteps trans 4090752 (FCfg.blank .A) = some ⟨[], Zlist 359 293 278 ++ [false, false, false], .A⟩ := by
    native_decide
  have e : (⟨[], Zlist 359 293 278 ++ [false, false, false], .A⟩ : FCfg St).toCfg = Z 359 293 278 := by
    show (⟨blank, app (Zlist 359 293 278 ++ [false, false, false]) blank, .A⟩ : Config) = _
    rw [← app_app]
    show (⟨blank, app (Zlist 359 293 278) (cons false (cons false (cons false blank))), .A⟩ : Config) = _
    rw [blank3]
    rfl
  rw [← e]
  exact blank_reaches trans h

/-- Then 68 periods of 14 round trips, to `Z 1311 293 6`. -/
theorem reach_Z_end : ∃ t, steps t init = some (Z 1311 293 6) := by
  obtain ⟨t, ht⟩ := Z_iter 68 358 292 1
  exact ⟨4090752 + t, steps_seq trans reach_Z ht⟩

end H91503
