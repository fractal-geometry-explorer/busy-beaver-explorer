import ModelWords

/-! # The stack model as a function, and the machine follows it

`mstep` is the model of `py/model.py` as a Lean function on its states (a list of frames and a mode), `den` the tape
a state stands for.  `mstep_next`: whenever `mstep` gives a next state and a step count, the machine goes from the
tape of the state to the tape of the next state in that many steps.  `mstep_halt`: when `mstep` says halt, the
machine halts.  So a run of the model is a run of the machine (`mrun_sound`), and since the run from blank tape
starts in a state of the model (`blank_to_model`), the model can be run in place of the machine. -/

namespace H129887

open TM

/-- The active part.  `ret p x w` is `RET(p + 1, x :: w)` (the head in C on a 1 with `p` ones between it and the
top frame), `z x w` is `Z(x :: w)` with the head on a zero and the frames on its left (the head's zero is not
counted in the top frame), `call m X` is `CALL(m, X)`. -/
inductive Mode where
  | ret (p : Nat) (x : Bool) (w : List Bool)
  | z (x : Bool) (w : List Bool)
  | call (m : Nat) (X : List Bool)

structure MS where
  fs : List (Nat × Nat)
  mode : Mode

/-- The configuration of the machine a state stands for. -/
def den : MS → Config
  | ⟨fs, .ret p x w⟩ => ⟨ones p (frames fs), cons true (wV x w), .C⟩
  | ⟨fs, .z x w⟩ => ⟨frames fs, cons false (wV x w), .C⟩
  | ⟨fs, .call m X⟩ => ⟨ones m (frames fs), wX X, .B⟩

inductive Res where
  | next (s : MS) (k : Nat)
  | halt
  | stuck

/-- Push a frame; a frame with no ones adds its zeros to the frame below (at the bottom they vanish in the blank
tape). -/
def push (n z : Nat) (fs : List (Nat × Nat)) : List (Nat × Nat) :=
  match n, fs with
  | 0, [] => []
  | 0, (n', z') :: r => (n', z + z') :: r
  | n + 1, fs => (n + 1, z) :: fs

/-- The number of leading c's of a word, and what follows them. -/
def lead : List Bool → Nat × List Bool
  | true :: w => ((lead w).1 + 1, (lead w).2)
  | w => (0, w)

/-- After `Z`: the call with `m` ones; a top frame with no zeros left gives its ones to the call. -/
def zcall (fs : List (Nat × Nat)) (m : Nat) (X : List Bool) : MS :=
  match fs with
  | (n, 0) :: r => ⟨r, .call (m + n) X⟩
  | fs => ⟨fs, .call m X⟩

/-- One transition of the model. -/
def mstep : MS → Res
  | ⟨fs, .ret (p + 3) x w⟩ => .next ⟨fs, .ret p false (x :: w)⟩ 5
  | ⟨[], .ret 2 x w⟩ => .next ⟨[], .z false (x :: w)⟩ 5
  | ⟨(n, z + 1) :: r, .ret 2 x w⟩ => .next ⟨(n, z) :: r, .z false (x :: w)⟩ 5
  | ⟨[], .ret 1 x w⟩ => .next ⟨[], .z false (x :: w)⟩ 3
  | ⟨(n, z + 2) :: r, .ret 1 x w⟩ => .next ⟨(n, z) :: r, .z false (x :: w)⟩ 3
  | ⟨(n + 1, 1) :: r, .ret 1 x w⟩ => .next ⟨r, .ret n false (x :: w)⟩ 3
  | ⟨[], .ret 0 x w⟩ => .next ⟨[], .z true (x :: w)⟩ 3
  | ⟨(n, z + 3) :: r, .ret 0 x w⟩ => .next ⟨(n, z) :: r, .z true (x :: w)⟩ 3
  | ⟨(n + 1, 2) :: r, .ret 0 x w⟩ => .next ⟨r, .ret n true (x :: w)⟩ 3
  | ⟨(n + 2, 1) :: r, .ret 0 x w⟩ => .next ⟨push n 1 r, .call 1 (x :: w)⟩ 5
  | ⟨[(1, 1)], .ret 0 _ _⟩ => .halt
  | ⟨(1, 1) :: (_, _ + 1) :: _, .ret 0 _ _⟩ => .halt
  | ⟨fs, .z x w⟩ =>
    match lead (x :: w) with
    | (a, false :: X) => .next (zcall fs (3 * a + 2) X) (3 * a + 2)
    | (a + 1, []) => .next (zcall fs (3 * a + 3) []) (3 * a + 3)
    | _ => .stuck
  | ⟨fs, .call (m + 1) X⟩ =>
    match lead X with
    | (j, false :: Y) => .next ⟨push m (3 * j + 2) fs, .ret 0 true Y⟩ (9 * j + 7)
    | (0, []) => .next ⟨fs, .ret m true []⟩ 1
    | (j + 1, []) => .next ⟨push m (3 * (j + 1)) fs, .ret 0 true []⟩ (9 * (j + 1) + 1)
    | _ => .stuck
  | _ => .stuck

theorem zeros_blank (z : Nat) : zeros z blank = blank := by
  induction z with
  | zero => rfl
  | succ z ih => show cons false (zeros z blank) = blank; rw [ih, cons_false_blank]

theorem frames_push (n z : Nat) (fs : List (Nat × Nat)) :
    frames (push n z fs) = zeros z (ones n (frames fs)) := by
  cases n with
  | zero =>
    cases fs with
    | nil => exact (zeros_blank z).symm
    | cons f r => obtain ⟨n', z'⟩ := f; exact zeros_add z z' _
  | succ n => rfl

theorem lead_spec (w : List Bool) : w = cpow (lead w).1 (lead w).2 := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    cases x with
    | false => rfl
    | true =>
      show true :: w = true :: cpow (lead w).1 (lead w).2
      rw [← ih]

theorem den_zcall (fs : List (Nat × Nat)) (m : Nat) (X : List Bool) :
    den (zcall fs m X) = ⟨ones m (frames fs), wX X, .B⟩ := by
  unfold zcall
  split
  · rename_i n r
    show (⟨ones (m + n) (frames r), wX X, .B⟩ : Config) = ⟨ones m (zeros 0 (ones n (frames r))), wX X, .B⟩
    rw [ones_add]; rfl
  · rfl

/-- The machine follows the model: a transition of the model is a run of the machine. -/
theorem mstep_next (s s' : MS) (k : Nat) (h : mstep s = .next s' k) : steps k (den s) = some (den s') := by
  unfold mstep at h
  split at h
  all_goals first
    | (injection h with h1 h2; subst h1; subst h2)
    | skip
  · exact ret_stride _ _ _ _
  · exact ret3_bottom _ _
  · exact ret3 _ _ _ _
  · exact ret2_bottom _ _
  · exact ret2 _ _ _ _
  · exact ret2_pop _ _ _ _
  · exact ret1_bottom _ _
  · exact ret1 _ _ _ _
  · exact ret1_pop _ _ _ _
  · rename_i n r x w
    show steps 5 ⟨zeros 1 (ones (n + 2) (frames r)), cons true (wV x w), .C⟩
      = some ⟨ones 1 (frames (push n 1 r)), wX (x :: w), .B⟩
    rw [frames_push]
    exact ret1_one _ _ _ _
  · cases h
  · cases h
  · rename_i fs x w
    split at h
    · rename_i a X hl
      injection h with h1 h2; subst h1; subst h2
      rw [den_zcall]
      have e := lead_spec (x :: w)
      rw [hl] at e
      have e2 := wV_cpow_b a X
      rw [← e] at e2
      show steps (3 * a + 2) ⟨frames fs, cons false (wV x w), .C⟩ = _
      have e3 : wV x w = ones (3 * a) (cons false (wX X)) := e2
      rw [e3]
      exact z_call _ _ _
    · rename_i a hl
      injection h with h1 h2; subst h1; subst h2
      rw [den_zcall]
      have e := lead_spec (x :: w)
      rw [hl] at e
      have e3 : wV x w = wV true (cpow a []) := by
        have : x :: w = true :: cpow a [] := e
        injection this with hx hw
        rw [hx, hw]
      show steps (3 * a + 3) ⟨frames fs, cons false (wV x w), .C⟩ = _
      rw [e3]
      exact z_call_end _ _
    · cases h
  · rename_i fs m X
    split at h
    · rename_i j Y hl
      injection h with h1 h2; subst h1; subst h2
      have e := lead_spec X
      rw [hl] at e
      show steps (9 * j + 7) ⟨ones (m + 1) (frames fs), wX X, .B⟩
        = some ⟨ones 0 (frames (push m (3 * j + 2) fs)), cons true (wV true Y), .C⟩
      rw [frames_push, e]
      exact call_word _ _ _ _
    · rename_i hl
      injection h with h1 h2; subst h1; subst h2
      have e := lead_spec X
      rw [hl] at e
      show steps 1 ⟨ones (m + 1) (frames fs), wX X, .B⟩ = some ⟨ones m (frames fs), cons true (wV true []), .C⟩
      rw [e]
      exact call_end m 0 _
    · rename_i j hl
      injection h with h1 h2; subst h1; subst h2
      have e := lead_spec X
      rw [hl] at e
      show steps (9 * (j + 1) + 1) ⟨ones (m + 1) (frames fs), wX X, .B⟩
        = some ⟨ones 0 (frames (push m (3 * (j + 1)) fs)), cons true (wV true []), .C⟩
      rw [frames_push, e]
      exact call_end _ _ _
    · cases h
  · cases h

/-- When the model says halt, the machine halts (on its fourth step from the state's tape). -/
theorem mstep_halt (s : MS) (h : mstep s = .halt) : ∃ c, steps 3 (den s) = some c ∧ step c = none := by
  unfold mstep at h
  split at h
  all_goals first
    | cases h
    | skip
  · rename_i x w
    have e := ret1_halt blank x w
    rw [cons_false_blank] at e
    exact e
  · rename_i n' z' r x w
    exact ret1_halt _ x w
  · split at h <;> cases h
  · split at h <;> cases h

/-- `n` transitions of the model from `s`, counting machine steps from `k`: the state reached and the step count,
or `none` if the model halts or is stuck on the way. -/
def mrun : Nat → MS → Nat → Option (MS × Nat)
  | 0, s, k => some (s, k)
  | n + 1, s, k =>
    match mstep s with
    | .next s' d => mrun n s' (k + d)
    | _ => none

theorem mrun_sound (n : Nat) (s : MS) (k : Nat) (s' : MS) (K : Nat) (h : mrun n s k = some (s', K)) :
    ∃ d, K = k + d ∧ steps d (den s) = some (den s') := by
  induction n generalizing s k with
  | zero =>
    simp only [mrun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    exact ⟨0, rfl, rfl⟩
  | succ n ih =>
    unfold mrun at h
    split at h
    · rename_i s1 d hs
      obtain ⟨d', hK, hd'⟩ := ih s1 (k + d) h
      exact ⟨d + d', by omega, steps_seq trans (mstep_next s s1 d hs) hd'⟩
    · cases h

/-- The state of the model two steps after the start from blank tape: `RET(1, c)` on the empty stack. -/
def start : MS := ⟨[], .ret 0 true []⟩

/-- If the model runs `n` transitions from `start` and counts `K` steps, the machine runs `K` steps from blank tape
without halting. -/
theorem blank_runs_of_mrun (n K : Nat) (h : ((mrun n start 2).map fun r => r.2) = some K) :
    ∃ c, steps K init = some c := by
  cases e : mrun n start 2 with
  | none => rw [e] at h; cases h
  | some r =>
    obtain ⟨s', K'⟩ := r
    rw [e] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨d, hK, hd⟩ := mrun_sound n start 2 s' K' e
    refine ⟨den s', ?_⟩
    rw [hK]
    exact steps_seq trans blank_to_model hd

/-- 20,000 transitions of the model from blank tape are 130,661 steps of the machine without a halt (the model run
by Lean's kernel). -/
theorem blank_runs_model_kernel : ∃ c, steps 130661 init = some c :=
  blank_runs_of_mrun 20000 130661 (by decide +kernel)

/-- 5,000,000 transitions of the model are 33,257,365 steps without a halt (the model run by `native_decide`). -/
theorem blank_runs_model_native : ∃ c, steps 33257365 init = some c :=
  blank_runs_of_mrun 5000000 33257365 (by native_decide)

end H129887
