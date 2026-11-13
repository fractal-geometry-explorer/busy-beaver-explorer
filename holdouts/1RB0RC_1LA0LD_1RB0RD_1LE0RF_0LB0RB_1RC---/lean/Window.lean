import Machine

/-!
# Runs on a finite window with an unknown tape on the left

`wsteps n ⟨l, r, s⟩` runs the machine on the cells `l` (left of the head, nearest first) and `r` (the head on its
first cell, blank beyond its end), and fails (`none`) if the head would move left of `l` or the machine halts.
When it succeeds, the same run happens with any tape `L` further left (`wsteps_over`): the run never looks at `L`.
Evaluating `wsteps` is how a long run over a fixed stretch of tape is checked (by `native_decide`) while the tape
on its left is still a parameter.
-/

namespace H32641

open TM

/-- One step on the window; `none` if the machine halts or the head would leave the window on the left. -/
def wstep (c : FCfg St) : Option (FCfg St) :=
  match trans c.st (c.r.headD false) with
  | none => none
  | some (w, .R, s) => some ⟨w :: c.l, c.r.tail, s⟩
  | some (w, .L, s) =>
    match c.l with
    | [] => none
    | a :: l => some ⟨l, a :: w :: c.r.tail, s⟩

/-- `n` steps on the window (tail recursive). -/
def wsteps : Nat → FCfg St → Option (FCfg St)
  | 0, c => some c
  | n + 1, c =>
    match wstep c with
    | none => none
    | some c' => wsteps n c'

/-- The window with the tape `L` on its left. -/
def over (c : FCfg St) (L : Tape) : Config := ⟨app c.l L, app c.r blank, c.st⟩

theorem wstep_over {c c' : FCfg St} (h : wstep c = some c') (L : Tape) :
    step (over c L) = some (over c' L) := by
  obtain ⟨l, r, s⟩ := c
  simp only [wstep] at h
  simp only [step, TM.step, over, app_head]
  cases e : trans s (r.headD false) with
  | none => rw [e] at h; cases h
  | some t =>
    obtain ⟨w, d, s'⟩ := t
    rw [e] at h
    cases d with
    | R =>
      cases h
      simp only [app_cons, app_tail]
    | L =>
      cases l with
      | nil => cases h
      | cons a l =>
        cases h
        simp only [app_cons, app_tail, cons_zero, tail_cons]

theorem wsteps_over' {n : Nat} {c c' : FCfg St} (h : wsteps n c = some c') (L : Tape) :
    steps n (over c L) = some (over c' L) := by
  induction n generalizing c with
  | zero => cases h; rfl
  | succ n ih =>
    simp only [wsteps] at h
    cases e : wstep c with
    | none => rw [e] at h; cases h
    | some d =>
      rw [e] at h
      rw [show steps (n + 1) (over c L) = steps n (over d L) from
        steps_succ_of_step trans n (wstep_over e L)]
      exact ih h

/-- **The window run**: a run on the window is a run on any tape that has the window's cells there. -/
theorem wsteps_over {n : Nat} {l r l' r' : List Bool} {s s' : St} (h : wsteps n ⟨l, r, s⟩ = some ⟨l', r', s'⟩)
    (L : Tape) : steps n ⟨app l L, app r blank, s⟩ = some ⟨app l' L, app r' blank, s'⟩ :=
  wsteps_over' h L

/-- The same, for a window that starts with one cell left of the head and ends with none, on a cell `b`. -/
theorem wsteps_over1 {n : Nat} {a b : Bool} {r r' : List Bool} {s s' : St}
    (h : wsteps n ⟨[a], r, s⟩ = some ⟨[], b :: r', s'⟩) (L : Tape) :
    steps n ⟨cons a L, app r blank, s⟩ = some ⟨L, cons b (app r' blank), s'⟩ :=
  wsteps_over' h L

/-- The same with three cells left of the head (nearest first). -/
theorem wsteps_over3 {n : Nat} {a₁ a₂ a₃ b : Bool} {r r' : List Bool} {s s' : St}
    (h : wsteps n ⟨[a₁, a₂, a₃], r, s⟩ = some ⟨[], b :: r', s'⟩) (L : Tape) :
    steps n ⟨cons a₁ (cons a₂ (cons a₃ L)), app r blank, s⟩ = some ⟨L, cons b (app r' blank), s'⟩ :=
  wsteps_over' h L

end H32641
