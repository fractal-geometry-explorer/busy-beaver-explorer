import StepRule
import Glue

/-!
# Tools for the generated step theorems

`py/gen_fam.py` writes each step of the walk as a chain of local passes (proved by symtm, stated in the counters'
blocks by `py/symglue.py`) and phases of ticks.  A phase here always fills the up-counter; `phase_split` gives the
down-counter after it as its low bits (which the next pass reads) and an unknown rest with its value.
-/

namespace H49767
open TM

local notation "rf" => List.replicate

theorem ones_of_val : ∀ (x : List Bool) (w : Nat), x.length = w → val x + 1 = 2 ^ w → x = rf w true := by
  intro x w hl hv
  apply val_inj
  · simp [hl]
  · have := val_ones w; omega

theorem mod_two_mul (b : Nat) (hb : b < 2) (Y M : Nat) (hM : 0 < M) : (b + 2 * Y) % (M * 2) = b + 2 * (Y % M) := by
  have h1 := Nat.mod_add_div Y M
  have h2 : Y % M < M := Nat.mod_lt _ hM
  have e : b + 2 * Y = (b + 2 * (Y % M)) + (M * 2) * (Y / M) := by
    have : 2 * Y = 2 * (Y % M) + 2 * (M * (Y / M)) := by omega
    rw [this, Nat.mul_left_comm, Nat.mul_assoc M 2]; omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem split_low : ∀ (m : Nat) (y : List Bool), m ≤ y.length →
    ∃ z, y = bitsOf m (val y % 2 ^ m) ++ z ∧ z.length + m = y.length ∧ val y = val y % 2 ^ m + 2 ^ m * val z
  | 0, y, _ => ⟨y, by simp [bitsOf], by simp, by simp [Nat.mod_one]⟩
  | m + 1, [], h => by simp at h
  | m + 1, b :: y, h => by
    obtain ⟨z, h1, h2, h3⟩ := split_low m y (by simp at h; omega)
    have hM : 0 < 2 ^ m := Nat.two_pow_pos m
    have key : val (b :: y) % 2 ^ (m + 1) = (if b then 1 else 0) + 2 * (val y % 2 ^ m) := by
      simp only [val, Nat.pow_succ]
      exact mod_two_mul _ (by cases b <;> simp) _ _ hM
    refine ⟨z, ?_, by simp; omega, ?_⟩
    · have e1 : (val (b :: y) % 2 ^ (m + 1) % 2 == 1) = b := by
        rw [key]; cases b <;> simp <;> omega
      have e2 : val (b :: y) % 2 ^ (m + 1) / 2 = val y % 2 ^ m := by
        rw [key]; cases b <;> simp <;> omega
      simp only [bitsOf, e1, e2, List.cons_append, ← h1]
    · rw [key]
      have : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
      rw [this]
      cases b <;> simp [val] <;> rw [h3] <;> simp [Nat.mul_add, Nat.mul_assoc] <;> omega

/-- A phase that fills the up-counter (width w), with the low m bits of the down-counter after it given. -/
theorem phase_split (H : List Bool) (hH : H = hdr0 ∨ H = hdr1) (u v : List Bool) (L R : Tape) (w : Nat)
    (hw : u.length = w) (k : Nat) (hk : k ≤ val v) (hfull : val u + k + 1 = 2 ^ w) (m c : Nat) (hm : m ≤ v.length)
    (hc : (val v - k) % 2 ^ m = c) :
    ∃ z, Reach (tcfg H u v L R) (tcfg H (rf w true) (bitsOf m c ++ z) L R) ∧ z.length + m = v.length ∧
      val v = k + c + 2 ^ m * val z := by
  obtain ⟨x, y, s, hs, lx, ly, vx, vy⟩ := phase H hH u v L R k hk (by rw [hw]; omega)
  have ex : x = rf w true := ones_of_val x w (by omega) (by omega)
  obtain ⟨z, e1, e2, e3⟩ := split_low m y (by omega)
  have hy : val y = val v - k := by omega
  rw [hy, hc] at e1 e3
  subst ex
  rw [e1] at hs
  exact ⟨z, ⟨s, hs⟩, by omega, by omega⟩

/-- A carry: the full up-counter (width w) becomes 0, the cell above it 0 becomes 1, and V goes down by one. -/
theorem carry_dec (H : List Bool) (hH : H = hdr0 ∨ H = hdr1) (w : Nat) (v : List Bool) (hv : true ∈ v) (L R : Tape) :
    Reach (tcfg H (rf w true) v (cons false L) R) (tcfg H (rf w false) (dec v) (cons true L) R) := by
  obtain ⟨i, v', rfl, hd⟩ := split_dec v hv
  rw [hd]
  simp only [tcfg, encU_replicate, encV_rep_false, encV_rep_true]
  cases i with
  | zero =>
    rcases hH with rfl | rfl
    · exact ⟨_, by simpa [encU, encV, dU, dV, rep, hdr0, app] using carry0_odd w L (encV v' R)⟩
    · exact ⟨_, by simpa [encU, encV, dU, dV, rep, hdr1, app] using carry1_odd w L (encV v' R)⟩
  | succ i =>
    rcases hH with rfl | rfl
    · have h := carry0_even i w L (encV v' R)
      rw [← rep_app_comm i [false, true]]
      exact ⟨_, by simpa [encU, encV, dU, dV, rep, hdr0, app] using h⟩
    · have h := carry1_even i w L (encV v' R)
      rw [← rep_app_comm i [false, true]]
      exact ⟨_, by simpa [encU, encV, dU, dV, rep, hdr1, app] using h⟩

/-- A carry with the low m bits of the down-counter after it given. -/
theorem carry_split (H : List Bool) (hH : H = hdr0 ∨ H = hdr1) (w : Nat) (v : List Bool) (L R : Tape)
    (hk : 1 ≤ val v) (m c : Nat) (hm : m ≤ v.length) (hc : (val v - 1) % 2 ^ m = c) :
    ∃ z, Reach (tcfg H (rf w true) v (cons false L) R) (tcfg H (rf w false) (bitsOf m c ++ z) (cons true L) R) ∧
      z.length + m = v.length ∧ val v = 1 + c + 2 ^ m * val z := by
  have hv : true ∈ v := mem_true_of_pos v (by omega)
  have h1 := val_dec v hv
  have h2 := length_dec v
  obtain ⟨z, e1, e2, e3⟩ := split_low m (dec v) (by omega)
  rw [show val (dec v) = val v - 1 by omega, hc] at e1 e3
  have st := carry_dec H hH w v hv L R
  rw [e1] at st
  exact ⟨z, st, by omega, by omega⟩

/-- A pass that lowers the down-counter by one above its known low bits K (written as K'), borrowing through any
number of zeros: given the pass for every borrow length i, it holds for every v of value at least 1. -/
theorem dec_pass (A B : List Bool → Config) (K K' : List Bool)
    (P : ∀ (i : Nat) (v' : List Bool), Reach (A (K ++ (rf i false ++ true :: v'))) (B (K' ++ (rf i true ++ false :: v'))))
    (v : List Bool) (hv : 1 ≤ val v) :
    ∃ z, Reach (A (K ++ v)) (B (K' ++ z)) ∧ z.length = v.length ∧ val z + 1 = val v := by
  have hm := mem_true_of_pos v (by omega)
  have h1 := val_dec v hm
  have h2 := length_dec v
  obtain ⟨i, v', rfl, hd⟩ := split_dec _ hm
  refine ⟨_, ?_, h2, h1⟩
  rw [hd]
  exact P i v'

theorem le_length_of_le_val (v : List Bool) (m : Nat) (h : 2 ^ m ≤ val v) : m ≤ v.length := by
  have h1 := val_lt v
  have h2 : 2 ^ m < 2 ^ v.length := by omega
  exact Nat.le_of_lt_succ (by
    have := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h2
    omega)

/-- A tick of the walk: the suffix cell next to the gap goes from 0 to 1 and V goes down by one (the carry with an
empty up-counter).  These are the steps 0 → 1, 000 → 001, 0000 → 0001, 1000 → 1001 and 10 → 11. -/
theorem tick_step (H : List Bool) (hH : H = hdr0 ∨ H = hdr1) (S0 : List Bool) (L : Tape) (v : List Bool) (R : Tape)
    (hv : 1 ≤ val v) :
    ∃ z : List Bool, z.length = v.length ∧ val z + 1 = val v ∧
      Reach ⟨cons false (cons false (app (false :: S0) L)), app H (encV v R), .D⟩
        ⟨cons false (cons false (app (true :: S0) L)), app H (encV z R), .D⟩ := by
  have hm := mem_true_of_pos v (by omega)
  exact ⟨dec v, length_dec v, val_dec v hm, carry_dec H hH 0 v hm (app S0 L) R⟩

theorem Reach.of_eq {a b : Config} (h : a = b) : Reach a b := ⟨0, by rw [h]; rfl⟩

end H49767
