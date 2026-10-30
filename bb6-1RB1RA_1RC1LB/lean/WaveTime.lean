import Wave

/-!
# The super step with its step count

`Wave.lean` follows the macro run from one super-step tape `X (5 :: L) 0 []` to the next without counting machine
steps.  This file counts them.  The macro steps of `Macro.lean` carry exact step counts (`next_sound`), so the wave
of `carry_wave` is followed again, this time with the times, and they add up to a closed form:

* while the wave passes a block with even value `d` (and `q = d / 2`) it takes `2q² + q − 5` steps (`evenT`);
* where it turns at an odd value `d` (`q = d / 2`) it takes `2q² + 4q + 17` steps, plus the sweep back over the blocks
  the wave has left on the right (`oddT`): the accumulator `A` starts at 3 and grows by `q + 1` at each block passed;
* at the left end it goes on with `p = 0`, and when it halts (at `d = 4`, the last block of 2) it takes 11 steps;
* the start of a super step, from `X (5 :: p :: L) 0 []` to the first carry, takes 200 steps.

`superT` is the sum, and `super_steps` proves it: the machine goes from the tape `[p_1, …, p_m, 5, 0]` (A on the blank
right of it) to the tape `[P', 5, 0]` in exactly `superT` steps, or halts after exactly that many (kernel-checked, every
list).  `orbitT` runs the super orbit with the time, and `orbitT_steps` turns a computed orbit into a statement about
the machine: the tape it ends at is reached from blank tape at the step it says.  `OrbitKernel.lean` and
`OrbitNative.lean` use this for long runs (`runs_of_orbitT`), with the orbit checked in chunks (`orbit_gen.py`).
-/

namespace BB6b

open TM

/-! ## The macro run with times -/

theorem Out.addT_addT (a b : Nat) (o : Out) : (o.addT b).addT a = o.addT (a + b) := by
  cases o <;> simp only [Out.addT, Nat.add_assoc]

theorem runFrom_addT : ∀ (m k : Nat) (o : Out), runFrom m (o.addT k) = (runFrom m o).map (Out.addT k) := by
  intro m
  induction m with
  | zero => intro k o; rfl
  | succ m ih =>
    intro k o
    cases o with
    | halt t => rfl
    | go ls n cs t =>
      simp only [Out.addT, runFrom]
      cases next ls n cs with
      | none => rfl
      | some o' => simp only; rw [← ih]; cases o' <;> simp only [Out.addT, Nat.add_assoc]

theorem runFrom_sound' : ∀ (m : Nat) (c : Config) (o o' : Out), o.Sound c → runFrom m o = some o' → o'.Sound c := by
  intro m
  induction m with
  | zero => intro c o o' ho h; cases h; exact ho
  | succ m ih =>
    intro c o o' ho h
    cases o with
    | halt t => cases h; exact ho
    | go ls n cs t =>
      simp only [runFrom] at h
      cases e : next ls n cs with
      | none => rw [e] at h; cases h
      | some o₁ =>
        rw [e] at h
        exact ih c _ _ (Out.sound_addT ho (next_sound ls n cs o₁ e)) h

/-- The macro run goes from the outcome `o` to `o'`, with the times. -/
def Reach (o : Option Out) (o' : Out) : Prop := ∃ x a, o = some x ∧ runFrom a x = some o'

theorem reach_eq {x y : Out} (h : x = y) : Reach (some x) y := ⟨x, 0, rfl, by rw [h]; rfl⟩

theorem reach_congr {o : Option Out} {x y : Out} (h : Reach o x) (e : x = y) : Reach o y := e ▸ h

theorem reach_map {k : Nat} {o : Option Out} {o' : Out} (h : Reach o o') : Reach (o.map (Out.addT k)) (o'.addT k) := by
  obtain ⟨x, a, rfl, h⟩ := h
  exact ⟨x.addT k, a, rfl, by rw [runFrom_addT, h]; rfl⟩

theorem reach_go {ls n cs t} {o' : Out} (h : Reach (next ls n cs) o') : Reach (some (.go ls n cs t)) (o'.addT t) := by
  obtain ⟨x, a, e, h⟩ := h
  refine ⟨_, a + 1, rfl, ?_⟩
  simp only [runFrom, e]
  rw [runFrom_addT, h]
  rfl

theorem reach_sound {c : Config} {o : Option Out} {o' : Out} (hc : ∀ x, o = some x → x.Sound c) (h : Reach o o') :
    o'.Sound c := by
  obtain ⟨x, a, e, h⟩ := h
  exact runFrom_sound' a c x o' (hc x e) h

/-! ## The times of the wave -/

/-- Steps while the wave passes a block with even value `d`: `2q² + q − 5` with `q = d / 2`. -/
def evenT (d : Nat) : Nat := 2 * (d / 2) * (d / 2) + d / 2 - 5

/-- Steps from a block with odd value `d` to the end of the super step: `2q² + 4q + 17 + A` with `q = d / 2`; `A`
pays for the sweep back over the blocks the wave left on the right. -/
def oddT (d A : Nat) : Nat := 2 * (d / 2) * (d / 2) + 4 * (d / 2) + 17 + A

/-- The time of the wave at the left end, with fuel `f` (as `leftEnd`): the halt at `d = 4` takes 11 steps. -/
def leftTime : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | f + 1, d, A =>
    if d % 2 = 1 then oddT d A
    else if d = 4 then 11
    else evenT d + leftTime f (d / 2) (A + d / 2 + 1)

/-- The time of `wave d L` to the end of the super step, with `A` the cost of the blocks on the right. -/
def waveTime : Nat → List Nat → Nat → Nat
  | d, [], A => leftTime d d A
  | d, p :: L, A => if d % 2 = 1 then oddT d A else evenT d + waveTime (p + d / 2) L (A + d / 2 + 1)

/-- The cost of the blocks on the right of the wave, `replicate e 1 ++ (c0 + 1) :: R ++ [1]`. -/
def acc (R : List Nat) (c0 e : Nat) : Nat := c0 + 3 * e + (R.map (· + 2)).sum

/-- Where the wave ends: at `X (P ++ W) 0 []` after `t` steps, or at a halt after `t` steps. -/
def outOf : Option (List Nat) → List Nat → Nat → Out
  | some W, P, t => .go (P ++ W) 0 [] t
  | none, _, t => .halt t

theorem outOf_addT (k : Nat) (x : Option (List Nat)) (P : List Nat) (t : Nat) :
    (outOf x P t).addT k = outOf x P (k + t) := by
  cases x <;> rfl

theorem leftTime_odd (f d A : Nat) (h : d % 2 = 1) : leftTime (f + 1) d A = oddT d A := by
  rw [leftTime, ite_eq_left h]

theorem leftTime_even (f d A : Nat) (h : d % 2 = 0) (h₄ : d ≠ 4) :
    leftTime (f + 1) d A = evenT d + leftTime f (d / 2) (A + d / 2 + 1) := by
  rw [leftTime, ite_eq_right (by omega), ite_eq_right h₄]

theorem waveTime_odd (d p : Nat) (L : List Nat) (A : Nat) (h : d % 2 = 1) : waveTime d (p :: L) A = oddT d A := by
  rw [waveTime, ite_eq_left h]

theorem waveTime_even (d p : Nat) (L : List Nat) (A : Nat) (h : d % 2 = 0) :
    waveTime d (p :: L) A = evenT d + waveTime (p + d / 2) L (A + d / 2 + 1) := by
  rw [waveTime, ite_eq_right (by omega)]

/-! ## The sweep, timed -/

theorem sweep_app_one_t : ∀ (cs ls : List Nat) (m : Nat), (∀ c ∈ cs, 0 < c) →
    sweep ls m (cs ++ [1]) = some (.go ((cs.map (· + 1)).reverse ++ (m + 2) :: ls) 0 [] (m + 3 + (cs.map (· + 2)).sum)) := by
  intro cs
  induction cs with
  | nil => intro ls m _; rfl
  | cons c cs ih =>
    intro ls m h
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp only [List.cons_append, sweep, ih ((m + 2) :: ls) c' h.2, Option.map_some, Out.addT, List.map_cons,
      List.reverse_cons, List.append_assoc, List.nil_append, List.sum_cons]

theorem sum_replicate' (e k : Nat) : (List.replicate e k).sum = e * k := by
  induction e with
  | zero => simp
  | succ e ih => rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]; omega

theorem sweep_pre_t (R : List Nat) (c0 e m : Nat) (ls : List Nat) (hR : ∀ r ∈ R, 0 < r) :
    sweep ls m (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))
      = some (.go (pre R c0 e ++ (m + 2) :: ls) 0 [] (m + 6 + acc R c0 e)) := by
  rw [show List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]) = (List.replicate e 1 ++ (c0 + 1) :: R) ++ [1] by simp,
    sweep_app_one_t _ ls m (pre_pos R c0 e hR)]
  simp only [pre, acc, List.map_append, List.map_replicate, List.map_cons, List.reverse_append, List.reverse_cons,
    List.reverse_replicate, List.sum_append, sum_replicate', List.sum_cons, List.append_assoc, List.cons_append,
    List.nil_append, Option.some.injEq, Out.go.injEq, true_and]
  omega

theorem acc_step (R : List Nat) (c0 e j : Nat) :
    acc (List.replicate e 1 ++ (c0 + 1) :: R) (1 + j) 0 = acc R c0 e + (j + 3) + 1 := by
  simp only [acc, List.map_append, List.map_replicate, List.map_cons, List.sum_append, sum_replicate',
    List.sum_cons]
  omega

/-! ## The wave, timed -/

theorem carry_left_t : ∀ (f d e c0 : Nat) (R : List Nat), 3 ≤ d → d ≤ f → (∀ r ∈ R, 0 < r) →
    Reach (carry [d - 2] e (c0 :: (R ++ [1]))) (outOf (leftEnd f d) (pre R c0 e) (leftTime f d (acc R c0 e))) := by
  intro f
  induction f with
  | zero => intro d e c0 R h₃ hf _; omega
  | succ f ih =>
    intro d e c0 R h₃ hf hR
    have hd : d = 3 ∨ d = 4 ∨ (d % 2 = 1 ∧ 5 ≤ d) ∨ (d % 2 = 0 ∧ 6 ≤ d) := by omega
    rcases hd with rfl | rfl | ⟨hd, hd'⟩ | ⟨hd, hd'⟩
    · -- d = 3: the carry meets a block of 1 and A sweeps right
      show Reach ((sweep [1] 2 (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))).map (Out.addT 15)) _
      rw [sweep_pre_t R c0 e 2 [1] hR, leftEnd_odd f 3 (by omega) (by decide), leftTime_odd f 3 _ (by decide)]
      refine reach_eq ?_
      simp only [Out.addT, outOf, oddT, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Out.go.injEq,
        true_and] <;> omega
    · -- d = 4: the carry eats the last block of 2 and the machine halts
      have h : leftEnd (f + 1) 4 = none := by rw [leftEnd_even f 4 (by omega) (by omega)]; rw [leftEnd_two]; rfl
      rw [h]
      exact reach_eq rfl
    · -- d odd: a new block at the left end, a transfer phase, and a sweep
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 5 := ⟨(d - 5) / 2, by omega⟩
      rw [leftEnd_odd f _ (by omega) hd, leftTime_odd f _ _ hd, show 2 * j + 5 - 2 = 2 * j + 3 by omega,
        show (2 * j + 5 + 5) / 2 = j + 5 by omega, show (2 * j + 5 - 1) / 2 = j + 2 by omega]
      show Reach (some (.go [1] (2 * j) (1 :: (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))) (2 * j + 9))) _
      refine reach_congr (reach_go (o' := .go (pre R c0 e ++ [j + 5, j + 2]) 0 [] (j * (2 * j + 9) + (15 + (j + 3 + 6 + acc R c0 e)))) ?_) ?_
      · show Reach ((exit [1 + 2 * j / 2] (2 * j % 2) (bumpBy (2 * j / 2) _)).map (Out.addT (tsteps (2 * j % 2) (2 * j / 2)))) _
        rw [show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega]
        show Reach (((sweep [1 + j + 1] (1 + j + 2) (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))).map (Out.addT 15)).map
          (Out.addT (tsteps 0 j))) _
        rw [sweep_pre_t R c0 e (1 + j + 2) [1 + j + 1] hR]
        refine reach_eq ?_
        simp only [Out.addT, tsteps, Out.go.injEq, true_and]
        refine ⟨by rw [show 1 + j + 2 + 2 = j + 5 by omega, show 1 + j + 1 = j + 2 by omega], ?_⟩
        simp only [Nat.mul_add, Nat.mul_zero, Nat.zero_add]
        omega
      · simp only [Out.addT, outOf, oddT, Out.go.injEq, true_and]
        rw [show (2 * j + 5) / 2 = j + 2 by omega]
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm]
        omega
    · -- d even: a new block at the left end, a transfer phase, and the carry again with d / 2
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 6 := ⟨(d - 6) / 2, by omega⟩
      rw [leftEnd_even f _ (by omega) hd, leftTime_even f _ _ hd (by omega), show 2 * j + 6 - 2 = 2 * j + 1 + 3 by omega,
        show (2 * j + 6) / 2 = j + 3 by omega]
      show Reach (some (.go [1] (2 * j + 1) (1 :: (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))) (2 * j + 1 + 9))) _
      refine reach_congr (reach_go (o' := (outOf (leftEnd f (j + 3)) (pre (List.replicate e 1 ++ (c0 + 1) :: R) (1 + j) 0) (leftTime f (j + 3) (acc R c0 e + (j + 3) + 1))).addT (tsteps 1 j + 6)) ?_) ?_
      · show Reach ((exit [1 + (2 * j + 1) / 2] ((2 * j + 1) % 2) (bumpBy ((2 * j + 1) / 2) _)).map
          (Out.addT (tsteps ((2 * j + 1) % 2) ((2 * j + 1) / 2)))) _
        rw [show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]
        show Reach (((carry [1 + j] 0 ((1 + j) :: (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1])))).map (Out.addT 6)).map
          (Out.addT (tsteps 1 j))) _
        have h := ih (j + 3) 0 (1 + j) _ (by omega) (by omega) (pre_pos R c0 e hR)
        rw [show j + 3 - 2 = 1 + j by omega, acc_step,
          show (List.replicate e 1 ++ (c0 + 1) :: R) ++ [1] = List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]) by simp] at h
        rw [← Out.addT_addT]
        exact reach_map (reach_map h)
      · simp only [outOf_addT]
        cases leftEnd f (j + 3) with
        | none =>
          simp only [Option.map_none, outOf, Out.halt.injEq, evenT, tsteps]
          rw [show (2 * j + 6) / 2 = j + 3 by omega]
          simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          omega
        | some W =>
          simp only [Option.map_some, outOf, pre_eq, Out.go.injEq, true_and, evenT, tsteps]
          rw [show (2 * j + 6) / 2 = j + 3 by omega]
          simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          omega

/-- **The wave, timed**: from a carry with value `d - 2` at the blocks `L`, the macro run ends at
`X (pre R c0 e ++ W) 0 []` where `wave d L = some W`, or halts where `wave d L = none`, after `waveTime d L A` steps. -/
theorem carry_wave_t : ∀ (L : List Nat) (d e c0 : Nat) (R : List Nat), 3 ≤ d → (∀ p ∈ L, 0 < p) → (∀ r ∈ R, 0 < r) →
    Reach (carry ((d - 2) :: L) e (c0 :: (R ++ [1]))) (outOf (wave d L) (pre R c0 e) (waveTime d L (acc R c0 e))) := by
  intro L
  induction L with
  | nil => intro d e c0 R h₃ _ hR; exact carry_left_t d d e c0 R h₃ (Nat.le_refl d) hR
  | cons p L ih =>
    intro d e c0 R h₃ hL hR
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    obtain ⟨hp, hL⟩ := hL
    have hd : d = 3 ∨ d = 4 ∨ (d % 2 = 1 ∧ 5 ≤ d) ∨ (d % 2 = 0 ∧ 6 ≤ d) := by omega
    rcases hd with rfl | rfl | ⟨hd, hd'⟩ | ⟨hd, hd'⟩
    · -- d = 3: the carry meets a block of 1 and A sweeps right
      rw [wave_odd 3 p L (by decide), waveTime_odd 3 p L _ (by decide)]
      show Reach ((sweep ((p + 1) :: L) 2 (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))).map (Out.addT 15)) _
      rw [sweep_pre_t R c0 e 2 ((p + 1) :: L) hR]
      refine reach_eq ?_
      simp only [Out.addT, outOf, oddT, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Out.go.injEq,
        true_and] <;> omega
    · -- d = 4: the carry eats a block of 2 and goes on to `p`
      rw [wave_even 4 p L (by decide), waveTime_even 4 p L _ (by decide)]
      show Reach ((carry (p :: L) (e + 1) (c0 :: (R ++ [1]))).map (Out.addT 5)) _
      have h := ih (p + 2) (e + 1) c0 R (by omega) hL hR
      rw [show p + 2 - 2 = p by omega] at h
      refine reach_congr (reach_map h) ?_
      rw [outOf_addT]
      have ha : acc R c0 (e + 1) = acc R c0 e + 4 / 2 + 1 := by simp only [acc]; omega
      rw [ha, show evenT 4 = 5 by rfl]
      cases wave (p + 2) L with
      | none => rfl
      | some W => simp [outOf, pre, List.replicate_succ']
    · -- d odd: the head's block takes a transfer phase, then A sweeps right
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 5 := ⟨(d - 5) / 2, by omega⟩
      rw [wave_odd _ p L hd, waveTime_odd _ p L _ hd, show 2 * j + 5 - 2 = 2 * j + 3 by omega,
        show (2 * j + 5 + 5) / 2 = j + 5 by omega, show (2 * j + 5 - 1) / 2 = j + 2 by omega]
      show Reach (some (.go ((p + 1) :: L) (2 * j) (1 :: (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))) (2 * j + 9))) _
      refine reach_congr (reach_go (o' := .go (pre R c0 e ++ (j + 5) :: (p + (j + 2)) :: L) 0 [] (j * (2 * j + 9) + (15 + (j + 3 + 6 + acc R c0 e)))) ?_) ?_
      · show Reach ((exit ((p + 1 + 2 * j / 2) :: L) (2 * j % 2) (bumpBy (2 * j / 2) _)).map
          (Out.addT (tsteps (2 * j % 2) (2 * j / 2)))) _
        rw [show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega]
        show Reach (((sweep ((p + 1 + j + 1) :: L) (1 + j + 2) (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]))).map
          (Out.addT 15)).map (Out.addT (tsteps 0 j))) _
        rw [sweep_pre_t R c0 e (1 + j + 2) ((p + 1 + j + 1) :: L) hR]
        refine reach_eq ?_
        simp only [Out.addT, tsteps, Out.go.injEq, true_and]
        refine ⟨by rw [show 1 + j + 2 + 2 = j + 5 by omega, show p + 1 + j + 1 = p + (j + 2) by omega], ?_⟩
        simp only [Nat.mul_add, Nat.mul_zero, Nat.zero_add]
        omega
      · simp only [Out.addT, outOf, oddT, Out.go.injEq, true_and]
        rw [show (2 * j + 5) / 2 = j + 2 by omega]
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm]
        omega
    · -- d even: a transfer phase, and the carry goes on to `p` with `p + d / 2`
      obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 6 := ⟨(d - 6) / 2, by omega⟩
      rw [wave_even _ p L hd, waveTime_even _ p L _ hd, show 2 * j + 6 - 2 = 2 * j + 1 + 3 by omega,
        show (2 * j + 6) / 2 = j + 3 by omega]
      show Reach (some (.go ((p + 1) :: L) (2 * j + 1) (1 :: (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1])))
        (2 * j + 1 + 9))) _
      refine reach_congr (reach_go (o' := (outOf (wave (p + (j + 3)) L) (pre (List.replicate e 1 ++ (c0 + 1) :: R) (1 + j) 0) (waveTime (p + (j + 3)) L (acc R c0 e + (j + 3) + 1))).addT (tsteps 1 j + 6)) ?_) ?_
      · show Reach ((exit ((p + 1 + (2 * j + 1) / 2) :: L) ((2 * j + 1) % 2) (bumpBy ((2 * j + 1) / 2) _)).map
          (Out.addT (tsteps ((2 * j + 1) % 2) ((2 * j + 1) / 2)))) _
        rw [show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]
        show Reach (((carry ((p + 1 + j) :: L) 0 ((1 + j) :: (List.replicate e 1 ++ (c0 + 1) :: (R ++ [1])))).map
          (Out.addT 6)).map (Out.addT (tsteps 1 j))) _
        have h := ih (p + (j + 3)) 0 (1 + j) _ (by omega) hL (pre_pos R c0 e hR)
        rw [show p + (j + 3) - 2 = p + 1 + j by omega, acc_step,
          show (List.replicate e 1 ++ (c0 + 1) :: R) ++ [1] = List.replicate e 1 ++ (c0 + 1) :: (R ++ [1]) by simp] at h
        rw [← Out.addT_addT]
        exact reach_map (reach_map h)
      · simp only [outOf_addT]
        cases wave (p + (j + 3)) L with
        | none =>
          simp only [Option.map_none, outOf, Out.halt.injEq, evenT, tsteps]
          rw [show (2 * j + 6) / 2 = j + 3 by omega]
          simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          omega
        | some W =>
          simp only [Option.map_some, outOf, pre_eq, Out.go.injEq, true_and, evenT, tsteps]
          rw [show (2 * j + 6) / 2 = j + 3 by omega]
          simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          omega

/-! ## The super step, timed -/

/-- **The machine steps of a super step** from the tape `[p_1, …, p_m, 5, 0]`, with `L = [p_m, …, p_1]`: 200 to the
first carry of the wave, then the wave from `d = p_m + 10`. -/
def superT : List Nat → Nat
  | [] => 0
  | p :: L => 200 + waveTime (p + 10) L 3

/-- The five macro steps from `X (5 :: p :: L) 0 []` before the wave, with their 164 machine steps. -/
theorem super_start (p : Nat) (L : List Nat) :
    runFrom 5 (.go (5 :: p :: L) 0 [] 0) = some (.go ((p + 6) :: L) 5 [1, 1] 164) := rfl

/-- **The super step, with its step count**: from `X (5 :: L) 0 []` the machine reaches `X (5 :: W) 0 []` in exactly
`superT L` steps if `superL L = some W`, and halts after exactly `superT L` steps (the next transition is the halting
one) if `superL L = none`. -/
theorem super_steps (L : List Nat) (hL : GoodL L) :
    (∀ W, superL L = some W → steps (superT L) (X (5 :: L) 0 []) = some (X (5 :: W) 0 [])) ∧
    (superL L = none → ∃ c', steps (superT L) (X (5 :: L) 0 []) = some c' ∧ step c' = none) := by
  match L, hL with
  | p :: L, ⟨_, hL⟩ =>
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    have h₀ : steps 164 (X (5 :: p :: L) 0 []) = some (X ((p + 6) :: L) 5 [1, 1]) :=
      runFrom_sound' 5 _ (.go (5 :: p :: L) 0 [] 0) _ rfl (super_start p L)
    have hw := carry_wave_t L (p + 10) 0 3 [] (by omega) hL.2 (by simp)
    rw [show p + 10 - 2 = p + 8 by rfl] at hw
    have hr : Reach (next ((p + 6) :: L) 5 [1, 1])
        ((outOf (wave (p + 10) L) (pre [] 3 0) (waveTime (p + 10) L (acc [] 3 0))).addT (tsteps 1 2 + 6)) := by
      rw [← Out.addT_addT]
      exact reach_map (reach_map hw)
    have hs := Out.sound_addT h₀ (reach_sound (next_sound _ _ _) hr)
    simp only [outOf_addT] at hs
    have ht : 164 + (tsteps 1 2 + 6 + waveTime (p + 10) L (acc [] 3 0)) = superT (p :: L) := by
      simp only [superT, tsteps, acc, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero] <;> omega
    rw [ht] at hs
    simp only [superL]
    constructor
    · intro W hW
      rw [hW] at hs
      exact hs
    · intro hW
      rw [hW] at hs
      exact hs

/-! ## The super orbit with times -/

/-- `j` super steps from `L`, with the machine step `t` at `L`: `some (W, t')` with `W` the list after `j` super steps
and `t'` its machine step, or `none` if a super step on the way halts.  Tail recursive, for long runs. -/
def orbitT : Nat → List Nat → Nat → Option (List Nat × Nat)
  | 0, L, t => some (L, t)
  | j + 1, L, t =>
    match superL L with
    | none => none
    | some W => orbitT j W (t + superT L)

theorem orbitT_add : ∀ (a b : Nat) (L : List Nat) (t : Nat),
    orbitT (a + b) L t = (orbitT a L t).bind (fun x => orbitT b x.1 x.2) := by
  intro a
  induction a with
  | zero => intro b L t; simp [orbitT]
  | succ a ih =>
    intro b L t
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [orbitT]
    cases superL L with
    | none => rfl
    | some W => exact ih b W _

/-- **A computed orbit is the machine's run**: if the machine is at the tape `[L, 5, 0]` after `t` steps and
`orbitT j L t = some (W, t')`, it is at the tape `[W, 5, 0]` after `t'` steps. -/
theorem orbitT_steps : ∀ (j : Nat) (L : List Nat) (t : Nat) (W : List Nat) (t' : Nat), GoodL L →
    steps t init = some (X (5 :: L) 0 []) → orbitT j L t = some (W, t') → steps t' init = some (X (5 :: W) 0 []) := by
  intro j
  induction j with
  | zero => intro L t W t' _ hs h; cases h; exact hs
  | succ j ih =>
    intro L t W t' hL hs h
    simp only [orbitT] at h
    cases e : superL L with
    | none => rw [e] at h; cases h
    | some V =>
      rw [e] at h
      exact ih V _ W t' (superL_good L V hL e) (steps_seq trans hs ((super_steps L hL).1 V e)) h

theorem orbitT_trans {L W V : List Nat} {t t' t'' : Nat} (h₁ : ∃ j, orbitT j L t = some (W, t'))
    (h₂ : ∃ j, orbitT j W t' = some (V, t'')) : ∃ j, orbitT j L t = some (V, t'') := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  exact ⟨a + b, by rw [orbitT_add, ha]; exact hb⟩

/-- The machine halts at the step the orbit says: if the orbit is at `[L, 5, 0]` after `t` steps and its next super
step halts, the machine makes `t + superT L` steps and then the halting transition. -/
theorem orbitT_halt (L : List Nat) (t : Nat) (hL : GoodL L) (hs : steps t init = some (X (5 :: L) 0 []))
    (h : superL L = none) : ∃ c', steps (t + superT L) init = some c' ∧ step c' = none := by
  obtain ⟨c', h₁, h₂⟩ := (super_steps L hL).2 h
  exact ⟨c', steps_seq trans hs h₁, h₂⟩

/-- The first tape of the super orbit, `[1, 6, 5, 0]`, after 136 steps. -/
theorem orbit_start : steps 136 init = some (X (5 :: [6, 1]) 0 []) := runM_sound 5 (.go [5, 6, 1] 0 [] 136) (by decide)

/-- **No halt while the orbit runs**: if `j` super steps from `[1, 6, 5, 0]` (at step 136) are defined and end at
step `t ≥ n`, the machine does not halt in its first `n` steps. -/
theorem runs_of_orbitT {W : List Nat} {t : Nat} (n : Nat) (h : ∃ j, orbitT j [6, 1] 136 = some (W, t)) (hn : n ≤ t) :
    ∃ c, steps n init = some c := by
  obtain ⟨j, h⟩ := h
  have hs := orbitT_steps j [6, 1] 136 W t ⟨by simp, by simp⟩ orbit_start h
  rw [show t = n + (t - n) by omega] at hs
  exact steps_le trans hs

/-! Checks against `py/waves.py` (`events`): the super-step tapes are its events 3, 7, 11, 15, 19, at steps 136, 544,
1,186, 1,604 and 2,812. -/

example : superT [6, 1] = 408 := by decide
example : superT [8, 7, 4] = 642 := by decide
example : orbitT 4 [6, 1] 136 = some ([11, 14, 10, 9, 10, 1], 2812) := by decide

end BB6b
