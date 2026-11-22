import Invariant

/-!
# Every overflow outside the halting family succeeds

`overflowStart d M Y` satisfies `Inv` for every reachable input (`2 ≤ Y < 2^M`, `d + 1 ≤ M`) except the halting
family `(d, M, Y) = (M - 2, M, 2^(M-1) + 1)`.  So `phase_some`: outside that family `phase` returns a configuration,
and it is again a reachable input.
-/

namespace H140108

open TM

/-! ## The bits of a number -/

theorem valOf_bitsOf : ∀ (n x : Nat), valOf (bitsOf n x) = x % 2 ^ n
  | 0, x => by simp [valOf, bitsOf, Nat.mod_one]
  | n + 1, x => by
    rw [bitsOf_succ]
    show (if (x % 2 == 1) = true then 1 else 0) + 2 * valOf (bitsOf n (x / 2)) = _
    rw [valOf_bitsOf n, pow_succ', Nat.mod_mul]
    have := Nat.mod_two_eq_zero_or_one x
    rcases this with h | h <;> simp [h]

theorem tl_bitsOf : ∀ (n x : Nat), tl (bitsOf (n + 1) x) = 2 ^ n * (if x / 2 ^ n % 2 = 1 then 2 else 1)
  | 0, x => by
    show (if (x % 2 == 1) = true then 2 else 1) = _
    have := Nat.mod_two_eq_zero_or_one x
    rcases this with h | h <;> simp [h]
  | n + 1, x => by
    rw [bitsOf_succ, tl_cons _ (by rw [← List.length_pos_iff, length_bitsOf]; omega), tl_bitsOf n,
      Nat.div_div_eq_div_mul, ← pow_succ', pow_succ' n, Nat.mul_assoc]

theorem lastT_bitsOf : ∀ (n x : Nat), lastT (bitsOf (n + 1) x) = decide (x / 2 ^ n % 2 = 1)
  | 0, x => by
    show (x % 2 == 1) = _
    have := Nat.mod_two_eq_zero_or_one x
    rcases this with h | h <;> simp [h]
  | n + 1, x => by
    rw [bitsOf_succ, lastT_cons _ (by rw [← List.length_pos_iff, length_bitsOf]; omega), lastT_bitsOf n,
      Nat.div_div_eq_div_mul, ← pow_succ']

theorem lz_le : ∀ H : List Bool, lz H ≤ H.length
  | [] => Nat.le_refl _
  | true :: _ => Nat.zero_le _
  | false :: H => by have := lz_le H; show lz H + 1 ≤ H.length + 1; omega

theorem lz_bitsOf_dvd : ∀ (n x : Nat), 2 ^ lz (bitsOf n x) ∣ x
  | 0, x => by simp [bitsOf, lz]
  | n + 1, x => by
    rw [bitsOf_succ]
    have := Nat.mod_two_eq_zero_or_one x
    rcases this with h | h
    · have hb : (x % 2 == 1) = false := by simp [h]
      rw [hb]
      show 2 ^ (lz (bitsOf n (x / 2)) + 1) ∣ x
      have h1 := lz_bitsOf_dvd n (x / 2)
      rw [pow_succ', show x = 2 * (x / 2) by omega]
      exact Nat.mul_dvd_mul_left 2 (by rwa [show 2 * (x / 2) / 2 = x / 2 by omega])
    · have hb : (x % 2 == 1) = true := by simp [h]
      rw [hb]
      show 2 ^ 0 ∣ x
      simp

theorem fac_ge4 {l : Nat} (hl : 1 ≤ l) : 4 ≤ fac l := by
  unfold fac
  split
  · rename_i h
    have : 1 ≤ l / 2 := by omega
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show 3 ≤ 3 * (l / 2) by omega)
    simp at this; omega
  · have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show 2 ≤ 3 * (l / 2) + 2 by omega)
    simp at this; omega

/-! ## The two starts of an overflow -/

/-- The counter value right after the overflowing count. -/
abbrev cz (d M Y : Nat) : Nat := 2 ^ d + (2 ^ M - 2 + Y % 2 - Y) / 2 + 1

theorem cz_bounds {d M Y : Nat} (hM : 1 ≤ M) (hYM : Y < 2 ^ M) (hov : ¬ Y + 2 ^ (d + 1) < 2 ^ M) :
    2 ^ d < cz d M Y ∧ cz d M Y ≤ 2 ^ (d + 1) ∧ 2 * (cz d M Y - 2 ^ d - 1) = 2 ^ M - 2 + Y % 2 - Y := by
  have := pow_succ' d
  have := Nat.mod_two_eq_zero_or_one Y
  have : 2 ^ M = 2 * 2 ^ (M - 1) := by rw [← pow_succ']; congr 1; omega
  unfold cz
  refine ⟨by omega, by omega, by omega⟩

theorem start_J {d M Y : Nat} (hY : 2 ≤ Y) (hYM : Y < 2 ^ M) (hd : d + 1 ≤ M) (hov : ¬ Y + 2 ^ (d + 1) < 2 ^ M)
    (he : Y % 2 = 0) : Inv (overflowStart d M Y) ∧ mu (overflowStart d M Y) < fuel d := by
  obtain ⟨h1, h2, h3⟩ := cz_bounds (by omega) hYM hov
  unfold overflowStart
  rw [if_neg (by omega)]
  generalize hc : 2 ^ d + (2 ^ M - 2 + Y % 2 - Y) / 2 + 1 = c0
  have hc' : cz d M Y = c0 := hc
  rw [hc'] at h1 h2 h3
  have hp1 := pow_succ' d
  have hp2 : 2 ^ (d + 2) = 2 * 2 ^ (d + 1) := pow_succ' (d + 1)
  have hpM := pow_succ' M
  have hlt : c0 < 2 ^ (d + 2) := by omega
  have hne : bitsOf (d + 2) c0 ≠ [] := by rw [← List.length_pos_iff, length_bitsOf]; omega
  have hv : valOf (bitsOf (d + 2) c0) = c0 := by rw [valOf_bitsOf, Nat.mod_eq_of_lt hlt]
  have hdm : 2 ^ (d + 1) ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) hd
  refine ⟨Or.inl ⟨rfl, by simp, fun h => absurd h hne, fun _ => ⟨?_, ?_⟩⟩, ?_⟩
  · show 1 + 2 * (2 ^ 0 * tl (bitsOf (d + 1 + 1) c0)) + 1 ≤ 2 ^ (M + 1) + 2 * (0 + 2 ^ 0 * valOf (bitsOf (d + 2) c0))
    rw [tl_bitsOf, hv]
    by_cases htop : c0 = 2 ^ (d + 1)
    · rw [htop, Nat.div_self (pow_pos' _)]
      simp only [Nat.one_mod, ↓reduceIte, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
      have : d + 2 ≤ M := by
        rcases (show d + 2 ≤ M ∨ M = d + 1 by omega) with h | h
        · exact h
        · subst h; omega
      have := Nat.pow_le_pow_right (show 0 < 2 by omega) this
      omega
    · rw [Nat.div_eq_of_lt (by omega)]
      simp only [Nat.zero_mod, Nat.zero_ne_one, ↓reduceIte, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.mul_one]
      omega
  · show 0 + (bitsOf (d + 2) c0).length + (if lastT (bitsOf (d + 1 + 1) c0) then 1 else 0) ≤ M + 1
    rw [length_bitsOf, lastT_bitsOf]
    by_cases htop : c0 = 2 ^ (d + 1)
    · have : d + 2 ≤ M := by
        rcases (show d + 2 ≤ M ∨ M = d + 1 by omega) with h | h
        · exact h
        · subst h; omega
      split <;> omega
    · rw [Nat.div_eq_of_lt (by omega)]; simp; omega
  · show 2 * (bitsOf (d + 2) c0).length + (if 0 + 1 < 2 ^ 0 then 1 else 0) < 2 * d + 12
    rw [length_bitsOf]; simp; omega

/-- Outside the halting family, the counter after an odd overflow has a 1 low enough. -/
theorem start_K_lz {d M Y : Nat} (hY : 2 ≤ Y) (hYM : Y < 2 ^ M) (hd : d + 1 ≤ M) (hov : ¬ Y + 2 ^ (d + 1) < 2 ^ M)
    (ho : Y % 2 = 1) (hnf : ¬ (d + 2 = M ∧ Y = 2 ^ (M - 1) + 1)) :
    lz (bitsOf (d + 2) (cz d M Y)) + 2 ≤ M ∧ lz (bitsOf (d + 2) (cz d M Y)) < d + 2 := by
  obtain ⟨h1, h2, h3⟩ := cz_bounds (by omega) hYM hov
  generalize hc : cz d M Y = c0 at h1 h2 h3
  generalize hq : lz (bitsOf (d + 2) c0) = q
  have hdv : 2 ^ q ∣ c0 := hq ▸ lz_bitsOf_dvd (d + 2) c0
  have hqc : 2 ^ q ≤ c0 := Nat.le_of_dvd (by omega) hdv
  have hqd : q ≤ d + 1 := by
    have : 2 ^ q ≤ 2 ^ (d + 1) := by omega
    exact (Nat.pow_le_pow_iff_right (by omega)).mp this
  refine ⟨?_, by omega⟩
  by_cases hcon : q + 2 ≤ M
  · exact hcon
  exfalso
  have hM1 : 2 ^ (M - 1) ∣ c0 := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hdv
  obtain ⟨j, hj⟩ := hM1
  have hp1 := pow_succ' d
  have hp2 : 2 ^ (d + 2) = 2 * 2 ^ (d + 1) := pow_succ' (d + 1)
  rcases (show d + 1 = M ∨ d + 2 = M by omega) with e | e
  · subst e
    simp only [Nat.add_sub_cancel] at hj
    rw [hp1] at h3
    rcases j with _ | _ | _ | j
    · omega
    · omega
    · omega
    · rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_succ] at hj; omega
  · subst e
    simp only [show d + 2 - 1 = d + 1 by omega, true_and] at hj hnf
    rw [hp2, hp1] at h3
    rw [hp1] at hj hnf h2
    rcases j with _ | _ | j
    · omega
    · omega
    · rw [Nat.mul_succ, Nat.mul_succ] at hj; omega

theorem start_K {d M Y : Nat} (hY : 2 ≤ Y) (hYM : Y < 2 ^ M) (hd : d + 1 ≤ M) (hov : ¬ Y + 2 ^ (d + 1) < 2 ^ M)
    (ho : Y % 2 = 1) (hnf : ¬ (d + 2 = M ∧ Y = 2 ^ (M - 1) + 1)) :
    Inv (overflowStart d M Y) ∧ mu (overflowStart d M Y) < fuel d := by
  obtain ⟨hq2, hqd⟩ := start_K_lz hY hYM hd hov ho hnf
  obtain ⟨h1, h2, h3⟩ := cz_bounds (by omega) hYM hov
  unfold overflowStart
  rw [if_pos ho]
  generalize hc : 2 ^ d + (2 ^ M - 2 + Y % 2 - Y) / 2 + 1 = c0
  have hc' : cz d M Y = c0 := hc
  rw [hc'] at h1 h2 h3 hq2 hqd
  generalize hq : lz (bitsOf (d + 2) c0) = q at hq2 hqd
  have hM : M - 1 + 1 = M := by omega
  have hM2 : M - 1 + 2 = M + 1 := by omega
  refine ⟨Or.inr (Or.inr ⟨rfl, by simp, ?_, ?_, ?_⟩), ?_⟩
  · show lz (bitsOf (d + 2) c0) + 1 < (bitsOf (d + 2) c0).length + 1
    rw [length_bitsOf]; omega
  · show 0 + 2 * (2 ^ (0 + (lz (bitsOf (d + 2) c0) + 1)) - 1 - 0) + 1 ≤ 2 ^ (M - 1 + 1)
    simp only [hq, Nat.zero_add, Nat.sub_zero]
    rw [hM]
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) hq2
    rw [show q + 2 = (q + 1) + 1 by omega, pow_succ' (q + 1)] at this
    have := pow_pos' (q + 1)
    omega
  · show SInv (absorbState (M - 1) (0 + 2 * (2 ^ (0 + (lz (bitsOf (d + 2) c0) + 1)) - 1 - 0))
      (0 + (lz (bitsOf (d + 2) c0) + 1)) ((false :: bitsOf (d + 2) c0).drop (lz (bitsOf (d + 2) c0) + 1 + 1)))
    rw [hq, List.drop_succ_cons, Nat.zero_add, Nat.zero_add, Nat.sub_zero]
    apply absorbS_fac
    · rw [List.length_drop, length_bitsOf, hM2]
      have hf := fac_ge4 (show 1 ≤ q + 1 by omega)
      generalize fac (q + 1) = f at hf
      obtain ⟨t, ht⟩ : ∃ t, M + 1 = (q + 3) + t := ⟨M + 1 - (q + 3), by omega⟩
      have hC : 8 ≤ 2 ^ (q + 3) := by
        have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show 3 ≤ q + 3 by omega); simpa using this
      have hB := pow_pos' t
      have hW : 2 ^ (M + 1) = 2 ^ (q + 3) * 2 ^ t := by rw [ht, Nat.pow_add]
      have hZ : 2 ^ (d + 2 - (q + 1) + 1) ≤ 2 ^ (t + 3) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h8 : 2 ^ (t + 3) = 8 * 2 ^ t := by rw [Nat.pow_add]; omega
      have hX : 2 * (2 ^ (q + 1) - 1) * 2 + 1 + 3 = 2 ^ (q + 3) := by
        have := pow_pos' (q + 1)
        have e1 : 2 ^ (q + 3) = 2 * 2 ^ (q + 2) := pow_succ' (q + 2)
        have e2 : 2 ^ (q + 2) = 2 * 2 ^ (q + 1) := pow_succ' (q + 1)
        omega
      generalize 2 ^ (q + 3) = C at hC hW hX
      generalize 2 ^ t = B at hB hW h8
      -- f * (2 va + 1) + Z ≤ f * (C B) with 2 va + 1 = C - 3
      have hCB : 8 * (B - 1) ≤ C * (B - 1) := Nat.mul_le_mul_right _ hC
      have hCB' : C * (B - 1) + C = C * B := by
        rw [← Nat.mul_succ]; congr 1; omega
      have hF : C - 3 + (C * B - (C - 3)) = C * B := by omega
      rw [hW]
      have hva : 2 * (2 * (2 ^ (q + 1) - 1)) + 1 = C - 3 := by omega
      rw [hva]
      have := Nat.mul_le_mul_right (C * B - (C - 3)) hf
      have hfm : f * (C * B) = f * (C - 3) + f * (C * B - (C - 3)) := by
        rw [← Nat.mul_add]; congr 1; omega
      rw [hfm]
      rw [Nat.mul_comm 4] at this
      omega
    · rw [List.length_drop, length_bitsOf, hM2]
      split <;> omega
  · show 2 * (false :: bitsOf (d + 2) c0).length + (if 0 + 1 < 2 ^ 0 then 1 else 0) < 2 * d + 12
    simp [length_bitsOf]; omega

/-! ## One phase -/

/-- The halting family: `(d, M, Y) = (M - 2, M, 2^(M-1) + 1)`. -/
def Fam (d M Y : Nat) : Prop := d + 2 = M ∧ Y = 2 ^ (M - 1) + 1

/-- What every configuration of the orbit satisfies. -/
def Good (d M Y : Nat) : Prop := 2 ≤ Y ∧ Y < 2 ^ M ∧ d + 1 ≤ M

theorem phase_some {d M Y : Nat} (hg : Good d M Y) (hnf : ¬ Fam d M Y) :
    ∃ d' M' Y', phase d M Y = some (d', M', Y') ∧ Good d' M' Y' := by
  obtain ⟨hY, hYM, hd⟩ := hg
  have hM0 : M ≠ 0 := by rintro rfl; simp at hYM; omega
  unfold phase
  rw [if_neg (by omega)]
  by_cases hev : Y + 2 ^ (d + 1) < 2 ^ M
  · rw [if_pos hev]
    have := pow_pos' d
    refine ⟨_, _, _, rfl, by omega, hev, ?_⟩
    have : 2 ^ (d + 1) < 2 ^ M := by omega
    have := (Nat.pow_lt_pow_iff_right (by omega)).mp this
    omega
  · rw [if_neg hev]
    have hst : Inv (overflowStart d M Y) ∧ mu (overflowStart d M Y) < fuel d := by
      rcases Nat.mod_two_eq_zero_or_one Y with h | h
      · exact start_J hY hYM hd hev h
      · exact start_K hY hYM hd hev h hnf
    obtain ⟨d1, w1, v1, hr, hv2, hvw, hdw⟩ := arun_inv (fuel d) _ hst.1 hst.2
    have hm := arun_mono _ _ hr
    have guard : ¬ (d1 = d ∧ w1 + 1 = M) := by
      unfold overflowStart at hm
      split at hm
      · simp only [List.length_cons, length_bitsOf] at hm; omega
      · simp only [length_bitsOf] at hm; omega
    rw [hr]
    simp only [guard, ↓reduceIte]
    exact ⟨d1, w1 + 1, v1, rfl, hv2, hvw, by omega⟩

end H140108
