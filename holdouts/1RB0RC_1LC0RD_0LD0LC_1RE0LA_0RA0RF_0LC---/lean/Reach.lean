import Machine
import Counter

/-!
# From blank tape to a sample configuration

After 1,001,057 steps from blank tape the machine is at the sample configuration

    0 0 W^364 e W^68 a W^71 b W^40 b W^8 0 0 1

with blank tape after it, made of standard digits only.  The run is evaluated by compiled code (`native_decide`) on
the list simulator of `TM/Fin.lean`, proved to agree with `steps`; the list it ends with is then identified with
`sample` by the kernel (`encList_app`).
-/

namespace H19849

open TM

/-- The cells of `enc`, as a list. -/
def encList : List (Dg × Nat) → List Bool → List Bool
  | [], t => t
  | (x, g) :: xs, t => x.word ++ (List.replicate g W).flatten ++ encList xs t

theorem app_flatten_rep (g : Nat) (s : Tape) : app (List.replicate g W).flatten s = rep g W s := by
  induction g with
  | zero => rfl
  | succ g ih => simp only [List.replicate_succ, List.flatten_cons, ← app_app, ih]; rfl

theorem encList_app (xs : List (Dg × Nat)) (t : List Bool) : app (encList xs t) blank = enc xs (app t blank) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨x, g⟩ := p
    simp only [encList, enc, ← app_app, app_flatten_rep, ih]

theorem app_falses (k : Nat) : app (List.replicate k false) blank = blank := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, app_cons, ih, cons_false_blank]

/-- The sample configuration reached. -/
def firstDigits : List (Dg × Nat) := [(.e, 68), (.a, 71), (.b, 40), (.b, 8)]

theorem reach_list : fsteps 1001057 (FCfg.blank .A) =
    some ⟨[], [false, false] ++ (List.replicate 364 W).flatten ++ encList firstDigits [false, false, true] ++ List.replicate 0 false, .A⟩ := by
  native_decide

/-- **The run from blank tape reaches a sample configuration** after 1,001,057 steps. -/
theorem reach : steps 1001057 init = some (sample 364 firstDigits (app [false, false, true] blank)) := by
  have h := blank_reaches trans reach_list
  show TM.steps trans 1001057 (blankCfg St.A) = _
  rw [h]
  unfold sample FCfg.toCfg
  simp only [← app_app, app_falses, app_flatten_rep, encList_app]
  rfl

set_option maxRecDepth 100000 in
/-- The counter rule alone then carries the run through the next 186 visits, to the first collision
(`bump` undefined: a digit with an empty gap after it). -/
theorem counted : ∃ k, steps k init = some (sample 588 [(.a, 0), (.c, 57), (.d, 38), (.c, 8)] (app [false, false, true] blank)) := by
  obtain ⟨k, hk⟩ := run_sound 186 364 firstDigits 588 [(.a, 0), (.c, 57), (.d, 38), (.c, 8)] (app [false, false, true] blank) (by decide)
  exact ⟨_, steps_seq trans reach hk⟩

end H19849
