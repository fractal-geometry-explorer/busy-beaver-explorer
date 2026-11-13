import Trip

/-! # The run from blank tape enters the right-end regime, twice

After 35,911 steps from blank tape the configuration is `T 108 [29, 4] 16`, and after 7,677,126 steps it is
`T 714 ks4 0` with a list of 125 blocks. In both cases the trip theorem then runs the regime to its end, `a = 0`
(108 and 714 round trips). The bounded runs are evaluated with the list simulator of `TM/Fin.lean`: by the kernel
for the first, by `native_decide` for the second.
-/

namespace H14847

open TM

set_option maxRecDepth 100000

/-- The left tape of `T a ks m` as a list (nearest cell first). -/
def BLl : List Nat → List Bool
  | [] => []
  | k :: ks => (List.replicate (k + 2) [false, true]).flatten ++ true :: BLl ks

def Tl (a : Nat) (ks : List Nat) (m : Nat) : List Bool :=
  (List.replicate (m + 1) w7).flatten ++ (BLl ks ++ (List.replicate (a + 2) [false, true]).flatten)

theorem app_flatten (n : Nat) (w l : List Bool) (s : Tape) :
    app ((List.replicate n w).flatten ++ l) s = rep n w (app l s) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.append_assoc, ← app_app, ih]; rfl

theorem app_BLl (ks : List Nat) (l : List Bool) (s : Tape) : app (BLl ks ++ l) s = BL ks (app l s) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    rw [BLl, List.append_assoc, app_flatten, List.cons_append, app_cons, ih]; rfl

theorem Tl_toCfg (a : Nat) (ks : List Nat) (m : Nat) :
    (⟨Tl a ks m, [], .A⟩ : FCfg St).toCfg = T a ks m := by
  show (⟨app (Tl a ks m) blank, blank, .A⟩ : Config) = _
  rw [Tl, app_flatten, app_BLl, ← List.append_nil (List.replicate (a + 2) [false, true]).flatten, app_flatten]
  rfl

/-- After 35,911 steps from blank tape: `T 108 [29, 4] 16` (kernel). -/
theorem reach1 : steps 35911 init = some (T 108 [29, 4] 16) := by
  have h : TM.fsteps trans 35911 (FCfg.blank .A) = some ⟨Tl 108 [29, 4] 16, [], .A⟩ := by decide +kernel
  rw [← Tl_toCfg]
  exact blank_reaches trans h

/-- Then 108 round trips, to `T 0 [29, 4] 124`: the first block is down to `(10)^2`. -/
theorem reach1_end : ∃ t, steps t init = some (T 0 [29, 4] 124) := by
  obtain ⟨t, ht⟩ := trip_iter [29, 4] 108 0 16
  exact ⟨35911 + t, steps_seq trans reach1 ht⟩

/-- The 125 blocks of the second regime, from the right: `8`, then `3, 11` 57 times, then
`16, 123, 35, 123, 35, 123, 35, 123, 35, 235`. -/
def ks4 : List Nat :=
  8 :: ((List.replicate 57 [3, 11]).flatten ++ [16, 123, 35, 123, 35, 123, 35, 123, 35, 235])

/-- After 7,677,126 steps from blank tape: `T 714 ks4 0` (`native_decide`). -/
theorem reach2 : steps 7677126 init = some (T 714 ks4 0) := by
  have h : TM.fsteps trans 7677126 (FCfg.blank .A) = some ⟨Tl 714 ks4 0, [], .A⟩ := by native_decide
  rw [← Tl_toCfg]
  exact blank_reaches trans h

/-- Then 714 round trips, to `T 0 ks4 714`. -/
theorem reach2_end : ∃ t, steps t init = some (T 0 ks4 714) := by
  obtain ⟨t, ht⟩ := trip_iter ks4 714 0 0
  exact ⟨7677126 + t, steps_seq trans reach2 ht⟩

end H14847
