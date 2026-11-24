import Sim

/-! # A faster run of the model, proved to be the same run

Almost all transitions of the run from blank tape go to the periodic block `a^k` (`a = c b b`) at the left end of the
word: a call eats it copy by copy and leaves a frame `1^7 0^2` for each copy (three transitions, 27 steps, per copy),
and later a return turns the frames back into the word, prepending `b b c` for each (three transitions, 13 steps).
`qstep` does each of these loops, and runs of returns past three ones (`RET(p + 3)`, 5 steps each), in one go, as
tight loops on the lists, and otherwise is `mstep`.  `qstep_next`: a transition of `qstep` is a run of the machine.
`fvrun` runs `qstep` to a given visit (a state `RET(1, v)` on the empty stack). -/

namespace H129887

open TM

theorem steps_of_mrun {n : Nat} {s s' : MS} {K : Nat} (h : mrun n s 0 = some (s', K)) :
    steps K (den s) = some (den s') := by
  obtain ⟨d, hK, hd⟩ := mrun_sound n s 0 s' K h
  rw [hK, Nat.zero_add]; exact hd

/-- One copy of `a` eaten by a call: `CALL(m + 2, c b b X)` leaves the frame `1^(m+1) 0^2` and is `CALL(8, X)`. -/
theorem copy_call (m : Nat) (fs : List (Nat × Nat)) (X : List Bool) :
    steps 27 (den ⟨fs, .call (m + 2) (true :: false :: false :: X)⟩) = some (den ⟨(m + 1, 2) :: fs, .call 8 X⟩) :=
  steps_of_mrun (n := 3) (by cases fs <;> rfl)

/-- One frame `1^7 0^2` given back by a return: `RET(1, v)` on it is `RET(1, b b c v)` below it. -/
theorem copy_ret (r : List (Nat × Nat)) (x : Bool) (w : List Bool) :
    steps 13 (den ⟨(7, 2) :: r, .ret 0 x w⟩) = some (den ⟨r, .ret 0 false (false :: true :: x :: w)⟩) :=
  steps_of_mrun (n := 3) (by cases r <;> rfl)

theorem copy_stride (fs : List (Nat × Nat)) (p : Nat) (x : Bool) (w : List Bool) :
    steps 5 (den ⟨fs, .ret (p + 3) x w⟩) = some (den ⟨fs, .ret p false (x :: w)⟩) :=
  mstep_next _ _ _ (by cases fs <;> rfl)

/-- The call loop: frames pushed, the rest of the word, and the step count (accumulated). -/
def eatA : List (Nat × Nat) → List Bool → Nat → List (Nat × Nat) × List Bool × Nat
  | fs, true :: false :: false :: X, d => eatA ((7, 2) :: fs) X (d + 27)
  | fs, X, d => (fs, X, d)

/-- The return loop over frames `1^7 0^2`. -/
def popA : List (Nat × Nat) → Bool → List Bool → Nat → List (Nat × Nat) × Bool × List Bool × Nat
  | (7, 2) :: r, x, w, d => popA r false (false :: true :: x :: w) (d + 13)
  | fs, x, w, d => (fs, x, w, d)

/-- Returns past three ones at a time. -/
def strideR : Nat → Bool → List Bool → Nat → Nat × Bool × List Bool × Nat
  | p + 3, x, w, d => strideR p false (x :: w) (d + 5)
  | p, x, w, d => (p, x, w, d)

theorem eatA_spec (c0 : Config) (fs : List (Nat × Nat)) (X : List Bool) (d : Nat)
    (h : steps d c0 = some (den ⟨fs, .call 8 X⟩)) :
    steps (eatA fs X d).2.2 c0 = some (den ⟨(eatA fs X d).1, .call 8 (eatA fs X d).2.1⟩) := by
  revert h
  fun_induction eatA fs X d with
  | case1 fs X d ih => intro h; exact ih (steps_seq trans h (copy_call 6 fs X))
  | case2 fs X d _ => intro h; exact h

theorem popA_spec (c0 : Config) (fs : List (Nat × Nat)) (x : Bool) (w : List Bool) (d : Nat)
    (h : steps d c0 = some (den ⟨fs, .ret 0 x w⟩)) :
    steps (popA fs x w d).2.2.2 c0 =
      some (den ⟨(popA fs x w d).1, .ret 0 (popA fs x w d).2.1 (popA fs x w d).2.2.1⟩) := by
  revert h
  fun_induction popA fs x w d with
  | case1 r x w d ih => intro h; exact ih (steps_seq trans h (copy_ret r x w))
  | case2 fs x w d _ => intro h; exact h

theorem strideR_spec (c0 : Config) (fs : List (Nat × Nat)) (p : Nat) (x : Bool) (w : List Bool) (d : Nat)
    (h : steps d c0 = some (den ⟨fs, .ret p x w⟩)) :
    steps (strideR p x w d).2.2.2 c0 =
      some (den ⟨fs, .ret (strideR p x w d).1 (strideR p x w d).2.1 (strideR p x w d).2.2.1⟩) := by
  revert h
  fun_induction strideR p x w d with
  | case1 p x w d ih => intro h; exact ih (steps_seq trans h (copy_stride fs p x w))
  | case2 p x w d _ => intro h; exact h

/-- One transition of the faster model. -/
def qstep : MS → Res
  | ⟨fs, .call (m + 2) (true :: false :: false :: X)⟩ =>
    match eatA ((m + 1, 2) :: fs) X 27 with
    | (fs', X', d) => .next ⟨fs', .call 8 X'⟩ d
  | ⟨(7, 2) :: r, .ret 0 x w⟩ =>
    match popA r false (false :: true :: x :: w) 13 with
    | (fs', x', w', d) => .next ⟨fs', .ret 0 x' w'⟩ d
  | ⟨fs, .ret (p + 3) x w⟩ =>
    match strideR p false (x :: w) 5 with
    | (p', x', w', d) => .next ⟨fs, .ret p' x' w'⟩ d
  | s => mstep s

/-- The faster model is the machine too. -/
theorem qstep_next (s s' : MS) (k : Nat) (h : qstep s = .next s' k) : steps k (den s) = some (den s') := by
  unfold qstep at h
  split at h
  · rename_i fs m X
    injection h with h1 h2; subst h1; subst h2
    exact eatA_spec _ _ _ _ (copy_call m fs X)
  · rename_i r x w
    injection h with h1 h2; subst h1; subst h2
    exact popA_spec _ _ _ _ _ (copy_ret r x w)
  · rename_i fs p x w
    injection h with h1 h2; subst h1; subst h2
    exact strideR_spec _ _ _ _ _ _ (copy_stride fs p x w)
  · exact mstep_next _ _ _ h

/-- A visit: `RET(1, v)` on the empty stack. -/
def isVisit : MS → Bool
  | ⟨[], .ret 0 _ _⟩ => true
  | _ => false

/-- `fvrun f v s k`: run the faster model from `s` (with the machine's step count `k`) to its `v`-th visit,
counting `s` itself; at most `f` transitions.  `none` if the model halts, gets stuck or runs out of fuel. -/
def fvrun : Nat → Nat → MS → Nat → Option (MS × Nat)
  | 0, _, _, _ => none
  | f + 1, v, s, k =>
    if (if isVisit s then v - 1 else v) = 0 then some (s, k) else
    match qstep s with
    | .next s' d => fvrun f (if isVisit s then v - 1 else v) s' (k + d)
    | _ => none

theorem fvrun_sound (f v : Nat) (s : MS) (k : Nat) (s' : MS) (K : Nat) (h : fvrun f v s k = some (s', K)) :
    ∃ d, K = k + d ∧ steps d (den s) = some (den s') := by
  induction f generalizing v s k with
  | zero => cases h
  | succ f ih =>
    unfold fvrun at h
    generalize (if isVisit s then v - 1 else v) = v' at h
    by_cases hv : v' = 0
    · simp only [hv, ↓reduceIte] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2; exact ⟨0, by omega, rfl⟩
    · simp only [hv, ↓reduceIte] at h
      split at h
      · rename_i s1 d hs
        obtain ⟨d', hK, hd'⟩ := ih _ s1 (k + d) h
        exact ⟨d + d', by omega, steps_seq trans (qstep_next s s1 d hs) hd'⟩
      · cases h

/-- The number of tokens of the word of a state `RET(1, v)`. -/
def wlen : MS → Nat
  | ⟨_, .ret _ _ w⟩ => w.length + 1
  | _ => 0

/-- If the faster model reaches a state from `start` with step count `K`, the machine runs `K` steps from blank
tape without halting. -/
theorem blank_runs_of_fvrun (f v K : Nat) (h : ((fvrun f v start 2).map fun r => r.2) = some K) :
    ∃ c, steps K init = some c := by
  cases e : fvrun f v start 2 with
  | none => rw [e] at h; cases h
  | some r =>
    obtain ⟨s', K'⟩ := r
    rw [e] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨d, hK, hd⟩ := fvrun_sound f v start 2 s' K' e
    refine ⟨den s', ?_⟩
    rw [hK]
    exact steps_seq trans blank_to_model hd

/-- A short check of the chain: visit 1,024 at step count 8,617,537 (`c/wrun.c` prints 8,617,539, two steps on),
with a word of 1,619 tokens, as in `c/wrun.c run 1024`. -/
theorem fvrun_1024 : ((fvrun 100000000 1024 start 2).map fun r => (r.2, wlen r.1)) = some (8617537, 1619) := by
  native_decide

theorem blank_runs_1024_visits : ∃ c, steps 8617537 init = some c :=
  blank_runs_of_fvrun 100000000 1024 8617537 (by native_decide)

end H129887
