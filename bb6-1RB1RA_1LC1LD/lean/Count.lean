import Recur

/-!
# The pass map with step counts

`pass_sound` (`Recur.lean`) says the machine gets from one pass configuration to the next, but not in how many
steps, so iterating it bounds the run in passes only.  This file is the same pass map with the number of machine steps
carried along: every rule of `Rules.lean` already states its exact step count, and here they are added up.

* `nextC`, `astepC`, `arunC`, `passC`, `passesC` are `next`, `astep`, `arun`, `pass`, `passes` returning, beside the
  outcome, the exact number of steps; `passesC_sound` says the machine takes exactly that many (kernel only).
* `blank_passesC`: blank tape to `K [10] 2` (the fourth pass start `1^10 0 1^3 A>0`, plus three steps) in 186 steps.
* `blank_reaches_1e12`: from there 8,257 passes of `passC`, evaluated by `native_decide` (so it trusts Lean's compiler
  as well as its kernel), reach a pass configuration past step 10¹²; hence `blank_runs_1e12` (and `blank_runs_1e10`,
  `blank_runs_1e11`): the run from blank tape does not halt in its first 10¹² steps.

The counted map is a copy of the uncounted one, case for case; nothing here depends on the two agreeing, since
`passesC_sound` is proved directly from the rules.
-/

namespace BB6c

open TM

/-! ## Counted steps -/

/-- What `Out` promises about the real machine from `x`, in exactly `s` steps (for `.halt`: the run is defined for `s`
steps and then halts). -/
def LeadsIn (x : Config) (s : Nat) : Out → Prop
  | .go c' => steps s x = some (enc c')
  | .pass ls n => steps s x = some (K ls n)
  | .halt => ∃ c, steps s x = some c ∧ step c = none

theorem LeadsIn.seq {x y : Config} {a b : Nat} {o : Out} (h₁ : steps a x = some y) (h₂ : LeadsIn y b o) :
    LeadsIn x (a + b) o := by
  cases o with
  | go _ => exact steps_seq trans h₁ h₂
  | pass _ _ => exact steps_seq trans h₁ h₂
  | halt => obtain ⟨c, h₂, h₃⟩ := h₂; exact ⟨c, steps_seq trans h₁ h₂, h₃⟩

theorem LeadsIn.congr {x : Config} {a b : Nat} {o : Out} (e : a = b) (h : LeadsIn x a o) : LeadsIn x b o := e ▸ h

/-! ## The passes of `Macro.lean`, counted -/

/-- Steps of `aphase` and `yphase` over `t` double words, the second block starting at `y`. -/
def aph : Nat → Nat → Nat
  | 0, _ => 0
  | t + 1, y => 10 * y + 18 + aph t (y + 4)

theorem aphaseC (L : Tape) (t : Nat) : ∀ (x y : Nat) (R : Tape),
    steps (aph t y) (PA L x y (rep t W R)) = some (PA L (x + 2 * t) (y + 4 * t) R) := by
  induction t with
  | zero => intro x y R; rfl
  | succ t ih =>
    intro x y R
    have h₁ := a_two x y L (cons false (cons true (cons true (rep t W R))))
    have h₂ := y_two x y L (rep t W R)
    rw [bump] at h₂
    have h := steps_seq trans (steps_seq trans h₁ h₂) (ih (x + 2) (y + 4) R)
    rw [show x + 2 + 2 * t = x + 2 * (t + 1) by omega, show y + 4 + 4 * t = y + 4 * (t + 1) by omega] at h
    exact steps_congr trans (by simp only [aph]; try omega) h

theorem yphaseC (L : Tape) (t : Nat) : ∀ (x y : Nat) (R : Tape),
    steps (aph t y) (PY L x y (rep t W R)) = some (PY L (x + 2 * t) (y + 4 * t) R) := by
  induction t with
  | zero => intro x y R; rfl
  | succ t ih =>
    intro x y R
    have h₁ := y_two x y L (cons false (cons true (cons true (rep t W R))))
    rw [bump] at h₁
    have h₂ := a_two (x + 2) (y + 4) L (rep t W R)
    have h := steps_seq trans (steps_seq trans h₁ h₂) (ih (x + 2) (y + 4) R)
    rw [show x + 2 + 2 * t = x + 2 * (t + 1) by omega, show y + 4 + 4 * t = y + 4 * (t + 1) by omega] at h
    exact steps_congr trans (by simp only [aph]; try omega) h

theorem kAC (t x : Nat) (ls : List Nat) :
    steps (14 * t + 32 + aph t 3 + (7 + (10 * (3 + 4 * t) + 12))) (K (x :: ls) (6 * (t + 1) + 3)) =
      some (K ((x + 2 * t + 8) :: ls) (4 * t + 4)) := by
  have h₁ : steps (14 * t + 32) (K (x :: ls) (6 * (t + 1) + 3)) =
      some (PA (lt ls) (x + 6) 3 (rep t W (cons false (cons true (cons true blank))))) := by
    have e : K (x :: ls) (6 * (t + 1) + 3) = ⟨rep (t + 1) [true, true, true, true, true, true] (cons true (cons true
        (cons true (cons false (rep x [true] (cons false (lt ls))))))), cons true (cons false (cons true blank)), .B⟩ := by
      simp only [K, lt]; rw [ones_add, ones_six]; rfl
    rw [e, conv6t9, rot2]; rfl
  have h₂ := aphaseC (lt ls) t (x + 6) 3 (cons false (cons true (cons true blank)))
  have h₃ : steps (7 + (10 * (3 + 4 * t) + 12)) (PA (lt ls) (x + 6 + 2 * t) (3 + 4 * t)
      (cons false (cons true (cons true blank)))) = some (K ((x + 2 * t + 8) :: ls) (4 * t + 4)) := by
    have h := steps_seq trans (a_two (x + 6 + 2 * t) (3 + 4 * t) (lt ls) blank) (y_end (x + 6 + 2 * t) (3 + 4 * t) (lt ls))
    rw [blk2, show 3 + 4 * t + 1 = 4 * t + 4 by omega, show x + 6 + 2 * t + 2 = x + 2 * t + 8 by omega] at h
    exact h
  exact steps_seq trans (steps_seq trans h₁ h₂) h₃

theorem kBC (t x : Nat) (ls : List Nat) :
    steps (14 * t + 24 + 1 + aph t 3 + 3) (K (x :: ls) (6 * (t + 1))) = some (K ((x + 2 * t + 6) :: ls) (4 * t + 2)) := by
  have h₁ : steps (14 * t + 24 + 1) (K (x :: ls) (6 * (t + 1))) = some (PA (lt ls) (x + 6) 3 (rep t W blank)) := by
    have e : K (x :: ls) (6 * (t + 1)) = ⟨rep (t + 1) [true, true, true, true, true, true]
        (cons false (rep x [true] (cons false (lt ls)))), cons true (cons false (cons true blank)), .B⟩ := by
      simp only [K, lt]; rw [ones_six]
    have h : steps (14 * t + 24) (K (x :: ls) (6 * (t + 1))) =
        some (PA (lt ls) (x + 6) 2 (cons true (rep t W blank))) := by
      rw [e, conv6t6, rot1]; rfl
    exact steps_seq trans h rfl
  have h₂ := aphaseC (lt ls) t (x + 6) 3 blank
  have h₃ : steps 3 (PA (lt ls) (x + 6 + 2 * t) (3 + 4 * t) blank) = some (K ((x + 2 * t + 6) :: ls) (4 * t + 2)) := by
    rw [show 3 + 4 * t = 4 * t + 2 + 1 by omega, show x + 2 * t + 6 = x + 6 + 2 * t by omega]; exact pa_end _ _ _
  exact steps_seq trans (steps_seq trans h₁ h₂) h₃

theorem kCC (t c d : Nat) (ls : List Nat) :
    steps (10 * c + 14 * t + 12 + 1 + aph t (c + 3) + 3) (K (c :: d :: ls) (6 * t + 1)) =
      some (K ((d + 2 * t + 2) :: ls) (c + 4 * t + 2)) := by
  have h₁ : steps (10 * c + 14 * t + 12 + 1) (K (c :: d :: ls) (6 * t + 1)) =
      some (PA (lt ls) (d + 2) (c + 3) (rep t W blank)) := by
    have e : K (c :: d :: ls) (6 * t + 1) = ⟨rep t [true, true, true, true, true, true] (cons true (cons false
        (rep c [true] (cons false (rep d [true] (cons false (lt ls))))))), cons true (cons false (cons true blank)), .B⟩ := by
      simp only [K, lt]; rw [ones_add, ones_six]; rfl
    have h : steps (10 * c + 14 * t + 12) (K (c :: d :: ls) (6 * t + 1)) =
        some (PA (lt ls) (d + 2) (c + 2) (cons true (rep t W blank))) := by
      rw [e, conv6t1, rot1, blk2]; rfl
    exact steps_seq trans h rfl
  have h₂ := aphaseC (lt ls) t (d + 2) (c + 3) blank
  have h₃ : steps 3 (PA (lt ls) (d + 2 + 2 * t) (c + 3 + 4 * t) blank) =
      some (K ((d + 2 * t + 2) :: ls) (c + 4 * t + 2)) := by
    rw [show c + 3 + 4 * t = c + 4 * t + 2 + 1 by omega, show d + 2 * t + 2 = d + 2 + 2 * t by omega]
    exact pa_end _ _ _
  exact steps_seq trans (steps_seq trans h₁ h₂) h₃

/-- Steps of the pass `kD` (last block `6t + 5`, block `c` to its left). -/
def kdCost (c : Nat) : Nat → Nat
  | 0 => 10 * c + 24 + (10 * (c + 3) + 15)
  | s + 1 => 10 * c + 14 * (s + 1) + 24 + (10 * (c + 3) + 21) + aph s (c + 7) + (10 * (c + 7 + 4 * s) + 12)

theorem kDC (t c d : Nat) (ls : List Nat) :
    steps (kdCost c t) (K (c :: d :: ls) (6 * t + 4)) = some (K ((d + 2 * t + 4) :: ls) (c + 4 * t + 4)) := by
  have e : K (c :: d :: ls) (6 * t + 4) = ⟨rep t [true, true, true, true, true, true]
      (cons true (cons true (cons true (cons true (cons false (rep c [true] (cons false (rep d [true]
        (cons false (lt ls)))))))))), cons true (cons false (cons true blank)), .B⟩ := by
    simp only [K, lt]; rw [ones_add, ones_six]; rfl
  have h₁ := conv6t4 c d t (lt ls)
  rw [← e] at h₁
  rw [blk2] at h₁
  cases t with
  | zero =>
    have h₂ := left_end (c + 3) (d + 2) (lt ls)
    rw [blk2] at h₂
    exact steps_seq trans h₁ h₂
  | succ s =>
    rw [rot1] at h₁
    have h₂ := left_two (c + 3) (d + 2) (lt ls) (rep s W blank)
    rw [blk2] at h₂
    have h₃ := yphaseC (lt ls) s (d + 4) (c + 7) blank
    have h₄ := y_end (d + 4 + 2 * s) (c + 7 + 4 * s) (lt ls)
    rw [blk2] at h₄
    have h := steps_seq trans (steps_seq trans (steps_seq trans h₁ h₂) h₃) h₄
    rw [show c + 7 + 4 * s + 1 = c + 4 * (s + 1) + 4 by omega,
      show d + 4 + 2 * s + 2 = d + 2 * (s + 1) + 4 by omega] at h
    exact h

/-- `next` with its step count. -/
def nextC (ls : List Nat) (n : Nat) : Option (List Nat × Nat × Nat) :=
  let x := ls.headD 0
  let d := ls.tail.headD 0
  if n = 3 then some ((x + 6) :: ls.tail, 0, 19)
  else if n % 6 = 3 then
    let t := (n - 9) / 6
    some ((x + 2 * t + 8) :: ls.tail, 4 * t + 4, 14 * t + 32 + aph t 3 + (7 + (10 * (3 + 4 * t) + 12)))
  else if n % 6 = 0 ∧ 0 < n then
    let t := (n - 6) / 6
    some ((x + 2 * t + 6) :: ls.tail, 4 * t + 2, 14 * t + 24 + 1 + aph t 3 + 3)
  else if n % 6 = 1 then
    let t := n / 6
    some ((d + 2 * t + 2) :: ls.tail.tail, x + 4 * t + 2, 10 * x + 14 * t + 12 + 1 + aph t (x + 3) + 3)
  else if n % 6 = 4 then
    let t := n / 6
    some ((d + 2 * t + 4) :: ls.tail.tail, x + 4 * t + 4, kdCost x t)
  else none

theorem nextC_sound {ls ls' : List Nat} {n n' s : Nat} (h : nextC ls n = some (ls', n', s)) :
    steps s (K ls n) = some (K ls' n') := by
  dsimp only [nextC] at h
  split at h
  · rename_i h3; cases h; subst h3; rw [K_pad1]; exact conv3 _ _
  split at h
  · rename_i _ h63; cases h
    obtain ⟨t, rfl⟩ : ∃ t, n = 6 * (t + 1) + 3 := ⟨(n - 9) / 6, by omega⟩
    rw [show (6 * (t + 1) + 3 - 9) / 6 = t by omega, K_pad1]; exact kAC _ _ _
  split at h
  · rename_i _ _ h60; cases h
    obtain ⟨t, rfl⟩ : ∃ t, n = 6 * (t + 1) := ⟨(n - 6) / 6, by omega⟩
    rw [show (6 * (t + 1) - 6) / 6 = t by omega, K_pad1]; exact kBC _ _ _
  split at h
  · rename_i _ _ _ h61; cases h
    obtain ⟨t, rfl⟩ : ∃ t, n = 6 * t + 1 := ⟨n / 6, by omega⟩
    rw [show (6 * t + 1) / 6 = t by omega, K_pad2]; exact kCC _ _ _ _
  split at h
  · rename_i _ _ _ _ h64; cases h
    obtain ⟨t, rfl⟩ : ∃ t, n = 6 * t + 4 := ⟨n / 6, by omega⟩
    rw [show (6 * t + 4) / 6 = t by omega, K_pad2]; exact kDC _ _ _ _
  cases h

/-! ## The block machine, counted -/

theorem c_a_run (h a : Nat) (M W : List Nat) :
    steps h (enc ⟨.A, h, a :: M, W⟩) = some (enc ⟨.A, 0, (a + h) :: M, W⟩) := by
  have e := ra_run h (lt (a :: M)) (rt W)
  rw [show lt (a :: M) = rep a [true] (cons false (lt M)) from rfl, ← ones_add, Nat.add_comm] at e
  exact e

theorem c_a_tok (k : Nat) (L W : List Nat) :
    steps (3 * k + 4) (enc ⟨.A, 0, L, (k + 1) :: W⟩) = some (enc ⟨.B, 0, 1 :: zs k L, W⟩) := by
  have e := ra_tok k (lt L) (rt W)
  unfold enc; rw [lt_one_zs]; exact e

theorem c_d_tok (k a : Nat) (M W : List Nat) :
    steps (3 * k + 4) (enc ⟨.D, 0, a :: M, (k + 3) :: W⟩) = some (enc ⟨.B, 0, 1 :: zs k ((a + 2) :: M), W⟩) := by
  have e := rd_tok k a (lt M) (rt W)
  unfold enc; rw [lt_one_zs]; exact e

theorem c_e_tok (k a : Nat) (M W : List Nat) :
    steps (3 * k + 5) (enc ⟨.E, 1, a :: M, (k + 3) :: W⟩) = some (enc ⟨.B, 0, 1 :: zs k ((a + 3) :: M), W⟩) := by
  have e := re_tok k a (lt M) (rt W)
  unfold enc; rw [lt_one_zs]; exact e

theorem c_f_tok (k a : Nat) (M W : List Nat) :
    steps (k + 1) (enc ⟨.F, 0, a :: M, k :: W⟩) = some (enc ⟨.A, 0, (a + k + 1) :: M, W⟩) := by
  have e := rf_tok k a (lt M) (rt W)
  rw [ones_cons, ← ones_add, show k + 1 + a = a + k + 1 by omega] at e
  exact e

theorem c_f_end (a : Nat) (M : List Nat) : steps (1 + 3) (enc ⟨.F, 0, a :: M, []⟩) = some (K M a) :=
  steps_seq trans (b := 3) (a := 1) rfl (start a (lt M))

theorem c_c_tok (c k : Nat) (M W : List Nat) :
    steps (3 * k + 3) (enc ⟨.C, 0, (c + 1) :: M, k :: W⟩) = some (enc ⟨.B, 0, 1 :: zs k (c :: M), W⟩) := by
  have e := rc_tok c k (lt M) (rt W)
  unfold enc; rw [lt_one_zs]; exact e

theorem c_c_more (d k : Nat) (M W : List Nat) :
    steps (3 * k + 5) (enc ⟨.C, 0, 0 :: d :: M, (k + 2) :: W⟩) = some (enc ⟨.B, 0, 1 :: zs k ((d + 2) :: M), W⟩) := by
  have e := rc_more d k (lt M) (rt W)
  unfold enc; rw [lt_one_zs]; exact e

theorem c_b_end (x y : Nat) (M : List Nat) :
    steps (10 * y + 12) (enc ⟨.B, 0, 1 :: 0 :: y :: x :: M, []⟩) = some (K ((x + 2) :: M) (y + 1)) := by
  have e := y_end x y (lt M)
  rw [blk2] at e
  exact e

theorem c_b_one (c j k : Nat) (M W : List Nat) :
    steps (7 * j + 2) (enc ⟨.B, 0, (3 * j + 1) :: c :: M, k :: W⟩) =
      some (enc ⟨.B, 0, c :: M, 0 :: (tw 1 j k ++ W)⟩) := by
  have e := rb_one c j k (lt M) (rt W)
  unfold enc lt; simp only [rt, rep_zero]; rw [ones_three, rt_tw]; exact e

theorem c_b_two (c j k : Nat) (M W : List Nat) :
    steps (7 * j + 13) (enc ⟨.B, 0, (3 * j + 5) :: c :: M, k :: W⟩) =
      some (enc ⟨.E, 1, (c + 3) :: M, tw 2 j k ++ W⟩) := by
  have e := rb_two c j k (lt M) (rt W)
  unfold enc lt; simp only [rt, rep_zero]; rw [ones_three, rt_tw]; exact e

theorem c_b_zero (c j : Nat) (M W : List Nat) :
    steps (7 * j + 1) (enc ⟨.B, 0, (3 * j) :: c :: M, 0 :: W⟩) = some (enc ⟨.C, 0, c :: M, tw 1 j 0 ++ W⟩) := by
  have e := rb_zero c j (lt M) (rt W)
  unfold enc lt; simp only [rt, rep_zero]; rw [show 3 * j = 3 * j + 0 from rfl, ones_three, rt_tw]
  exact e

theorem c_b_three0 (c d k : Nat) (M W : List Nat) :
    steps (10 * c + 7 * 0 + 14) (enc ⟨.B, 0, 3 :: c :: d :: M, (k + 1) :: W⟩) =
      some (enc ⟨.A, k + 2, (c + 2) :: (d + 2) :: M, W⟩) := by
  have e := rb_three c d 0 k (lt M) (rt W)
  rw [blk2] at e
  exact e

theorem c_b_three (c d j k : Nat) (M W : List Nat) :
    steps (10 * c + 7 * (j + 1) + 14) (enc ⟨.B, 0, (3 * j + 6) :: c :: d :: M, (k + 1) :: W⟩) =
      some (enc ⟨.A, 1, (c + 2) :: (d + 2) :: M, tw 2 j (k + 1) ++ W⟩) := by
  have e := rb_three c d (j + 1) k (lt M) (rt W)
  rw [blk2] at e
  unfold enc lt; rw [show 3 * j + 6 = 3 * (j + 1) + 3 by omega, ones_three, rt_tw]; exact e

theorem c_k_start (c j : Nat) (M : List Nat) :
    steps (7 * j + 7) (K (c :: M) (3 * j + 2)) = some (enc ⟨.B, 0, c :: M, 0 :: 1 :: tw 2 j 0⟩) := by
  have e := k_start c j (lt M)
  rw [show rep j [true, false, true] (cons true blank) = cons true (rep j [false, true, true] blank) from
    (rep_rotate j [true] [false, true, true] [true, false, true] rfl blank).symm] at e
  unfold K enc; rw [ones_three, ← List.append_nil (tw 2 j 0)]; simp only [rt, rep_zero]; rw [rt_tw]
  exact e

theorem c_c_move (k : Nat) (M W : List Nat) : ∀ c : Nat,
    steps (9 * c) (enc ⟨.C, 0, c :: M, 1 :: k :: W⟩) = some (enc ⟨.C, 0, 0 :: M, 1 :: (k + c) :: W⟩)
  | 0 => rfl
  | c + 1 => by
    have h₁ := c_c_tok c 1 M (k :: W)
    have h₂ := c_b_one 0 0 k (c :: M) W
    have h₃ := c_b_zero c 0 M ((1 + k) :: W)
    have h₄ := c_c_move (1 + k) M W c
    rw [show 1 + k + c = k + (c + 1) by omega] at h₄
    exact steps_congr trans (by omega) (steps_seq trans h₁ (steps_seq trans h₂ (steps_seq trans h₃ h₄)))

/-- `bstep` with its step count. -/
def bstepC (n c d : Nat) (M : List Nat) (k : Nat) (W : List Nat) : Option (Out × Nat) :=
  if n % 3 = 1 then some (.go ⟨.B, 0, c :: d :: M, 0 :: (tw 1 (n / 3) k ++ W)⟩, 7 * (n / 3) + 2)
  else if n = 2 then some (.go ⟨.E, k + 1, (c + 3) :: d :: M, W⟩, 6)
  else if n % 3 = 2 then some (.go ⟨.E, 1, (c + 3) :: d :: M, tw 2 (n / 3 - 1) k ++ W⟩, 7 * (n / 3 - 1) + 13)
  else if k = 0 then some (.go ⟨.C, 0, c :: d :: M, tw 1 (n / 3) 0 ++ W⟩, 7 * (n / 3) + 1)
  else if n = 0 then some (.go ⟨.C, 0, c :: d :: M, (k + 1) :: W⟩, 1)
  else if n = 3 then some (.go ⟨.A, k + 1, (c + 2) :: (d + 2) :: M, W⟩, 10 * c + 7 * 0 + 14)
  else some (.go ⟨.A, 1, (c + 2) :: (d + 2) :: M, tw 2 (n / 3 - 2) k ++ W⟩, 10 * c + 7 * (n / 3 - 2 + 1) + 14)

theorem bstepC_sound {n c d k s : Nat} {M W : List Nat} {o : Out} (e : bstepC n c d M k W = some (o, s)) :
    LeadsIn (enc ⟨.B, 0, n :: c :: d :: M, k :: W⟩) s o := by
  unfold bstepC at e
  split at e
  · cases e
    obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j + 1 := ⟨n / 3, by omega⟩
    rw [show (3 * j + 1) / 3 = j by omega]; exact c_b_one c j k (d :: M) W
  split at e
  · cases e; subst n; exact rb_two0 c k (lt (d :: M)) (rt W)
  split at e
  · cases e
    obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j + 5 := ⟨n / 3 - 1, by omega⟩
    rw [show (3 * j + 5) / 3 - 1 = j by omega]; exact c_b_two c j k (d :: M) W
  split at e
  · cases e; subst k
    obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j := ⟨n / 3, by omega⟩
    rw [show 3 * j / 3 = j by omega]; exact c_b_zero c j (d :: M) W
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  split at e
  · cases e; subst n; exact rb_empty c k (lt (d :: M)) (rt W)
  split at e
  · cases e; subst n; exact c_b_three0 c d k M W
  · cases e
    obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j + 6 := ⟨n / 3 - 2, by omega⟩
    rw [show (3 * j + 6) / 3 - 2 = j by omega]; exact c_b_three c d j k M W

/-- `astep'` with its step count: the same cases in the same order. -/
def astepC' : St → Nat → List Nat → List Nat → Option (Out × Nat)
  | .A, h + 1, a :: M, W => some (.go ⟨.A, 0, (a + h + 1) :: M, W⟩, h + 1)
  | .A, 0, (n + 1) :: M, [] => some (.pass M n, 3)
  | .A, 0, L, (k + 1) :: W => some (.go ⟨.B, 0, 1 :: zs k L, W⟩, 3 * k + 4)
  | .D, 0, _, [] => some (.halt, 1)
  | .D, 0, a :: M, 1 :: W => some (.go ⟨.D, 0, (a + 2) :: M, W⟩, 2)
  | .D, 0, a :: M, 2 :: W => some (.go ⟨.F, 0, 0 :: (a + 2) :: M, W⟩, 3)
  | .D, 0, a :: M, (k + 3) :: W => some (.go ⟨.B, 0, 1 :: zs k ((a + 2) :: M), W⟩, 3 * k + 4)
  | .E, 1, _, [] => some (.halt, 2)
  | .E, 1, a :: M, 1 :: W => some (.go ⟨.D, 0, (a + 3) :: M, W⟩, 3)
  | .E, 1, a :: M, 2 :: W => some (.go ⟨.F, 0, 0 :: (a + 3) :: M, W⟩, 4)
  | .E, 1, a :: M, (k + 3) :: W => some (.go ⟨.B, 0, 1 :: zs k ((a + 3) :: M), W⟩, 3 * k + 5)
  | .F, 0, a :: M, [] => some (.pass M a, 1 + 3)
  | .F, 0, a :: M, k :: W => some (.go ⟨.A, 0, (a + k + 1) :: M, W⟩, k + 1)
  | .C, 0, (c + 1) :: M, 1 :: k :: W => some (.go ⟨.C, 0, 0 :: M, 1 :: (k + c + 1) :: W⟩, 9 * (c + 1))
  | .C, 0, (c + 1) :: M, k :: W => some (.go ⟨.B, 0, 1 :: zs k (c :: M), W⟩, 3 * k + 3)
  | .C, 0, 0 :: d :: M, 1 :: W => some (.go ⟨.F, 0, 0 :: (d + 2) :: M, W⟩, 4)
  | .C, 0, 0 :: d :: M, (k + 2) :: W => some (.go ⟨.B, 0, 1 :: zs k ((d + 2) :: M), W⟩, 3 * k + 5)
  | .B, 0, 1 :: 0 :: y :: x :: M, [] => some (.pass ((x + 2) :: M) (y + 1), 10 * y + 12)
  | .B, 0, n :: c :: d :: M, k :: W => bstepC n c d M k W
  | _, _, _, _ => none

def astepC (c : ACfg) : Option (Out × Nat) := astepC' c.q c.h (pad 4 c.L) c.W

theorem astepC'_sound {q : St} {h : Nat} {L W : List Nat} {o : Out} {s : Nat} (e : astepC' q h L W = some (o, s)) :
    LeadsIn (enc ⟨q, h, L, W⟩) s o := by
  unfold astepC' at e
  split at e <;> first | cases e | skip
  · exact c_a_run _ _ _ _
  · exact start _ _
  · exact c_a_tok _ _ _
  · exact ⟨_, rfl, rfl⟩
  · exact rd_one _ _ _
  · exact rd_two _ _ _
  · exact c_d_tok _ _ _ _
  · exact ⟨_, rfl, rfl⟩
  · exact re_one _ _ _
  · exact re_two _ _ _
  · exact c_e_tok _ _ _ _
  · exact c_f_end _ _
  · exact c_f_tok _ _ _ _
  · exact c_c_move _ _ _ _
  · exact c_c_tok _ _ _ _
  · exact rc_one _ _ _
  · exact c_c_more _ _ _ _
  · exact c_b_end _ _ _
  · exact bstepC_sound e

theorem astepC_sound {c : ACfg} {o : Out} {s : Nat} (e : astepC c = some (o, s)) : LeadsIn (enc c) s o := by
  have h := astepC'_sound e
  rwa [show enc ⟨c.q, c.h, pad 4 c.L, c.W⟩ = enc c by unfold enc; rw [lt_pad]] at h

/-- `arun` with its step count. -/
def arunC : Nat → ACfg → Option (Out × Nat)
  | 0, _ => none
  | f + 1, c =>
    match astepC c with
    | some (.go c', s) =>
      match arunC f c' with
      | some (o, s') => some (o, s + s')
      | none => none
    | some o => some o
    | none => none

theorem arunC_sound : ∀ (f : Nat) {c : ACfg} {o : Out} {s : Nat}, arunC f c = some (o, s) → LeadsIn (enc c) s o := by
  intro f
  induction f with
  | zero => intro c o s e; cases e
  | succ f ih =>
    intro c o s e
    unfold arunC at e
    split at e
    · rename_i h
      split at e
      · cases e; exact LeadsIn.seq (astepC_sound h) (ih (by assumption))
      · cases e
    · cases e; exact astepC_sound (by assumption)
    · cases e

/-! ## The whole pass, counted -/

/-- `pass` with its step count. -/
def passC (f : Nat) (ls : List Nat) (n : Nat) : Option (Out × Nat) :=
  match nextC ls n with
  | some (ls', n', s) => some (.pass ls' n', s)
  | none =>
    if n = 0 then some (.halt, 6)
    else if n % 3 = 2 then
      match arunC f ⟨.B, 0, pad 1 ls, 0 :: 1 :: tw 2 (n / 3) 0⟩ with
      | some (o, s) => some (o, 7 * (n / 3) + 7 + s)
      | none => none
    else none

theorem passC_sound {f : Nat} {ls : List Nat} {n s : Nat} {o : Out} (e : passC f ls n = some (o, s)) :
    LeadsIn (K ls n) s o := by
  unfold passC at e
  split at e
  · rename_i h; cases e; exact nextC_sound h
  split at e
  · cases e; subst n; exact K_zero_halts ls
  split at e
  · split at e
    · rename_i h; cases e
      obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j + 2 := ⟨n / 3, by omega⟩
      rw [show (3 * j + 2) / 3 = j by omega] at h ⊢
      rw [K_pad1]
      exact LeadsIn.seq (c_k_start _ j _) (arunC_sound f h)
    · cases e
  · cases e

/-- `passes` with its step count. -/
def passesC (f : Nat) : Nat → List Nat → Nat → Option (Out × Nat)
  | 0, ls, n => some (.pass ls n, 0)
  | p + 1, ls, n =>
    match passC f ls n with
    | some (.pass ls' n', s) =>
      match passesC f p ls' n' with
      | some (o, s') => some (o, s + s')
      | none => none
    | o => o

/-- **The counted pass map is sound**: whatever `passesC` returns, the machine does, in exactly that many steps
(kernel only). -/
theorem passesC_sound (f : Nat) : ∀ (p : Nat) {ls : List Nat} {n s : Nat} {o : Out},
    passesC f p ls n = some (o, s) → LeadsIn (K ls n) s o := by
  intro p
  induction p with
  | zero => intro ls n s o e; cases e; rfl
  | succ p ih =>
    intro ls n s o e
    unfold passesC at e
    split at e
    · rename_i h
      split at e
      · cases e; exact LeadsIn.seq (passC_sound h) (ih (by assumption))
      · cases e
    · exact passC_sound e

/-! ## From blank tape -/

/-- Blank tape to `K [10] 2` (`1^10 0 1^3 A>0`, the fourth pass start, at step 183, then three steps), in exactly 186
steps (kernel only). -/
theorem blank_passesC : steps 186 init = some (K [10] 2) := by
  have h₀ : steps 13 init = some (K [2] 1) := by
    have h := blank_reaches trans (q := St.A) (n := 13) (c := ⟨[true, false, true, true], [true, false, true], .B⟩)
      (by decide +kernel)
    refine h.trans ?_
    simp only [K, lt, FCfg.toCfg, app, rep, cons_false_blank]
  have h₁ := nextC_sound (ls := [2]) (n := 1) (ls' := [2]) (n' := 4) (s := 36) (by decide +kernel)
  have h₂ := nextC_sound (ls := [2]) (n := 4) (ls' := [4]) (n' := 6) (s := 109) (by decide +kernel)
  have h₃ := nextC_sound (ls := [4]) (n := 6) (ls' := [10]) (n' := 2) (s := 28) (by decide +kernel)
  exact steps_congr trans (show 13 + 36 + 109 + 28 = 186 from rfl)
    (steps_seq trans (steps_seq trans (steps_seq trans h₀ h₁) h₂) h₃)

set_option maxHeartbeats 0 in
/-- 8,257 passes of `passC` from `K [10] 2`, 2,654 of them recursive, evaluated by `native_decide` (about 2.5
minutes): the run reaches the pass start `1^11866 0 1^17246 A>0` at step 1,000,110,302,407, so `K` three steps later.
Every pass start on the way agrees, in step and blocks, with the C run `tools/c/tmrun` to 10¹¹ steps (3,843 of
them). -/
theorem blank_reaches_1e12 : steps 1000110302410 init = some (K [11866] 17245) := by
  have h : passesC 1000000000 8257 [10] 2 = some (.pass [11866, 0, 0, 0] 17245, 1000110302224) := by native_decide
  have e : K [11866, 0, 0, 0] 17245 = K [11866] 17245 := by simp only [K, lt, rep_zero, cons_false_blank]
  have h₂ : steps 1000110302410 init = some (K [11866, 0, 0, 0] 17245) :=
    steps_congr trans (show 186 + 1000110302224 = 1000110302410 from rfl)
      (steps_seq trans blank_passesC (passesC_sound _ _ h))
  exact e ▸ h₂

/-- **No halt in the first 10¹² steps** from blank tape (trusts `native_decide`). -/
theorem blank_runs_1e12 : ∃ c, steps 1000000000000 init = some c :=
  steps_le trans (steps_congr trans (show 1000110302410 = 1000000000000 + 110302410 from rfl) blank_reaches_1e12)

/-- No halt in the first 10¹⁰ steps, the range of the pass starts checked so far (trusts `native_decide`). -/
theorem blank_runs_1e10 : ∃ c, steps 10000000000 init = some c :=
  steps_le trans (steps_congr trans (show 1000110302410 = 10000000000 + 990110302410 from rfl) blank_reaches_1e12)

/-- No halt in the first 10¹¹ steps, the range of the C run (trusts `native_decide`). -/
theorem blank_runs_1e11 : ∃ c, steps 100000000000 init = some c :=
  steps_le trans (steps_congr trans (show 1000110302410 = 100000000000 + 900110302410 from rfl) blank_reaches_1e12)

end BB6c
