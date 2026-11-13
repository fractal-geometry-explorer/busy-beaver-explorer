import Machine
import Counter

/-!
# From blank tape to a sample configuration

After 1,010,696 steps from blank tape the machine is at the sample configuration

    0 0 W^148 e W^102 e W^319 e W^33 a W^12 0 0 1

with blank tape after it, made of standard digits only.  The run is evaluated by compiled code (`native_decide`) on
the list simulator of `TM/Fin.lean`, proved to agree with `steps`; the list it ends with is then identified with
`sample` by the kernel (`encList_app`).
-/

namespace H54516

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
def firstDigits : List (Dg × Nat) := [(.e, 102), (.e, 319), (.e, 33), (.a, 12)]

theorem reach_list : fsteps 1010696 (FCfg.blank .A) =
    some ⟨[], [false, false] ++ (List.replicate 148 W).flatten ++ encList firstDigits [false, false, true] ++ List.replicate 0 false, .D⟩ := by
  native_decide

/-- **The run from blank tape reaches a sample configuration** after 1,010,696 steps. -/
theorem reach : steps 1010696 init = some (sample 148 firstDigits (app [false, false, true] blank)) := by
  have h := blank_reaches trans reach_list
  show TM.steps trans 1010696 (blankCfg St.A) = _
  rw [h]
  unfold sample FCfg.toCfg
  simp only [← app_app, app_falses, app_flatten_rep, encList_app]
  rfl

set_option maxRecDepth 100000 in
/-- The counter rule alone then carries the run through the next 282 visits, to the first collision
(`bump` undefined: a digit with an empty gap after it). -/
theorem counted : ∃ k, steps k init = some (sample 487 [(.b, 0), (.a, 299), (.a, 28), (.c, 11)] (app [false, false, true] blank)) := by
  obtain ⟨k, hk⟩ := run_sound 282 148 firstDigits 487 [(.b, 0), (.a, 299), (.a, 28), (.c, 11)] (app [false, false, true] blank) (by decide)
  exact ⟨_, steps_seq trans reach hk⟩

end H54516
