import Phase

/-!
# The machine follows the phase map; it halts only if the map gets stuck

`phase d M Y` (one phase: either the event rule or a whole overflow) is a computable function on numbers.
`phase_sound`: if it returns `(d', M', Y')`, the machine goes from `PN d M Y` to `PN d' M' Y'`.  From blank tape
the machine reaches `PN 0 2 2` (step 69), so `orbit n` (the map iterated) is always reached, and
`not_halts_of_orbit`: **if the orbit of the map never gets stuck, the machine never halts.**
-/

namespace H140108

open TM

/-- Steps allowed to the junction machine in an overflow (it takes at most `2 (d + 3) + 3`). -/
def fuel (d : Nat) : Nat := 2 * d + 12

/-- The junction machine right after the overflowing count of a phase `PN d M Y`. -/
def overflowStart (d M Y : Nat) : AS :=
  if Y % 2 = 1 then ⟨M - 1, 0, 0, 0, true, false :: bitsOf (d + 2) (2 ^ d + (2 ^ M - 2 + Y % 2 - Y) / 2 + 1)⟩
  else ⟨M, 1, 0, 0, false, bitsOf (d + 2) (2 ^ d + (2 ^ M - 2 + Y % 2 - Y) / 2 + 1)⟩

/-- One phase of the machine, from one post-event configuration to the next. -/
def phase (d M Y : Nat) : Option (Nat × Nat × Nat) :=
  if M = 0 ∨ 2 ^ M ≤ Y then none
  else if Y + 2 ^ (d + 1) < 2 ^ M then some (d + 1, M, Y + 2 ^ (d + 1))
  else match arun (fuel d) (overflowStart d M Y) with
    | .done d' w' v' => if d' = d ∧ w' + 1 = M then none else some (d', w' + 1, v')
    | _ => none

theorem ctr_P_pad (d : Nat) : ctr (List.replicate d false ++ [true]) blank = ctr (bitsOf (d + 2) (2 ^ d)) blank := by
  rw [show bitsOf (d + 2) (2 ^ d) = bitsOf ((d + 1) + 1) (2 ^ d + 2 ^ (d + 1) * 0) by simp,
    bitsOf_append _ _ _ _ (by rw [pow_succ']; have := two_pow_pos d; omega), bitsOf_pow]
  show _ = ctr (List.replicate d false ++ [true] ++ [false]) blank
  rw [ctr_blank]

theorem phase_sound {d M Y d' M' Y' : Nat} (h : phase d M Y = some (d', M', Y')) :
    Reach (PN d M Y) (PN d' M' Y') := by
  unfold phase at h
  split at h
  · cases h
  · rename_i hMY
    obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    have hY : Y < 2 ^ (m + 1) := by omega
    have hpM := pow_succ' m
    have hpd := pow_succ' d
    have hp0 := two_pow_pos d
    have hp1 := two_pow_pos m
    unfold PN P
    rw [ctr_P_pad]
    split at h
    · -- the event rule: 2^d counts
      rename_i hno
      cases h
      have := count_many m Y (d + 2) (2 ^ d) L0 blank (2 ^ d) (by omega) (by rw [pow_succ', pow_succ']; omega)
      rw [show 2 ^ d + 2 ^ d = 2 ^ (d + 1) by omega, bitsOf_pow, show Y + 2 * 2 ^ d = Y + 2 ^ (d + 1) by omega] at this
      exact this
    · -- an overflow
      rename_i hov
      have hb : Y % 2 = 0 ∨ Y % 2 = 1 := Nat.mod_two_eq_zero_or_one Y
      have hi0 : 2 * ((2 ^ (m + 1) - 2 + Y % 2 - Y) / 2) = 2 ^ (m + 1) - 2 + Y % 2 - Y := by omega
      generalize hI : (2 ^ (m + 1) - 2 + Y % 2 - Y) / 2 = i0 at hi0
      have hi0d : i0 < 2 ^ d := by omega
      have hc := count_many m Y (d + 2) (2 ^ d) L0 blank i0 (by omega) (by rw [pow_succ', pow_succ']; omega)
      refine Reach.trans' hc ?_
      have hds : false ∈ bitsOf (d + 2) (2 ^ d + i0) :=
        false_mem_bitsOf _ _ (by rw [pow_succ', pow_succ']; omega)
      have hinc : inc (bitsOf (d + 2) (2 ^ d + i0)) = bitsOf (d + 2) (2 ^ d + i0 + 1) :=
        bitsOf_inc _ _ (by rw [pow_succ', pow_succ']; omega)
      split at h
      · rename_i s0 d1 w1 v1 hrun
        split at h
        · cases h
        · cases h
          have hr := arun_done _ _ hrun
          unfold overflowStart at hr
          rw [hI] at hr
          rcases hb with hb | hb
          · -- b1 = 0
            rw [if_neg (show ¬ (Y % 2 = 1) by omega)] at hr
            have e : Y + 2 * i0 = 2 ^ (m + 1) - 2 + (if false then 1 else 0) := by simp; omega
            rw [e, bitsOf_top]
            refine Reach.trans' (overflow_false m _ hds) ?_
            rw [hinc]
            have e2 : bitsOf (m + 1 + 1) 1 = true :: List.replicate (m + 1) false := by
              rw [bitsOf_succ, show (1 : Nat) / 2 = 0 from rfl, bitsOf_zero]; rfl
            rw [← e2]
            exact hr
          · rw [if_pos hb] at hr
            have e : Y + 2 * i0 = 2 ^ (m + 1) - 2 + (if true then 1 else 0) := by simp; omega
            rw [e, bitsOf_top]
            refine Reach.trans' (overflow_true m _ hds) ?_
            rw [hinc, ← bitsOf_zero]
            rw [show m + 1 - 1 = m by omega] at hr
            exact hr
      · cases h

/-- The orbit of the phase map from the first post-event configuration (step 69 from blank tape). -/
def orbit : Nat → Option (Nat × Nat × Nat)
  | 0 => some (0, 2, 2)
  | n + 1 =>
    match orbit n with
    | some (d, M, Y) => phase d M Y
    | none => none

/-! ## Consecutive configurations differ -/

theorem ctr_get : ∀ (d i : Nat), ctr (List.replicate d false ++ [true]) blank i = decide (i = 3 * d + 2)
  | 0, 0 => rfl
  | 0, 1 => rfl
  | 0, 2 => rfl
  | 0, i + 3 => by show blank i = _; simp [blank]
  | d + 1, 0 => by show false = _; simp
  | d + 1, 1 => by show false = _; simp
  | d + 1, 2 => by show false = _; simp
  | d + 1, i + 3 => by
    show ctr (List.replicate d false ++ [true]) blank i = _
    rw [ctr_get d i]; simp only [decide_eq_decide]; omega

theorem enc_get : ∀ (l : List Bool) (T : Tape) (i : Nat), enc l T (2 * l.length + i) = T i
  | [], _, _ => by simp [enc]
  | b :: l, T, i => by
    show cons true (cons b (enc l T)) (2 * (l.length + 1) + i) = _
    rw [show 2 * (l.length + 1) + i = (2 * l.length + i) + 1 + 1 by omega]
    exact enc_get l T i

theorem PN_left_get (d M Y j : Nat) : (PN d M Y).l (2 * M + 3 + j) = decide (j = 0) := by
  show enc (false :: bitsOf M Y) L0 (2 * M + 3 + j) = _
  have := enc_get (false :: bitsOf M Y) L0 (1 + j)
  rw [List.length_cons, length_bitsOf, show 2 * (M + 1) + (1 + j) = 2 * M + 3 + j by omega] at this
  rw [this]
  cases j with
  | zero => rfl
  | succ j => rw [show 1 + (j + 1) = j + 2 by omega]; show blank j = _; simp [blank]

theorem PN_inj {d M Y d' M' Y' : Nat} (h : PN d M Y = PN d' M' Y') : d = d' ∧ M = M' := by
  have hl := congrArg Cfg.l h
  have hr := congrArg Cfg.r h
  refine ⟨?_, ?_⟩
  · have := congrFun hr (3 * d + 2)
    simp only [PN, P] at this
    rw [ctr_get, ctr_get] at this
    simp at this; omega
  · rcases Nat.lt_trichotomy M M' with hlt | heq | hgt
    · have := congrFun hl (2 * M' + 3)
      have a1 := PN_left_get d M Y (2 * (M' - M))
      have a2 := PN_left_get d' M' Y' 0
      rw [show 2 * M + 3 + 2 * (M' - M) = 2 * M' + 3 by omega] at a1
      rw [Nat.add_zero] at a2
      rw [a1, a2] at this
      simp at this; omega
    · exact heq
    · have := congrFun hl (2 * M + 3)
      have a1 := PN_left_get d M Y 0
      have a2 := PN_left_get d' M' Y' (2 * (M - M'))
      rw [show 2 * M' + 3 + 2 * (M - M') = 2 * M + 3 by omega] at a2
      rw [Nat.add_zero] at a1
      rw [a1, a2] at this
      simp at this; omega

theorem phase_ne {d M Y d' M' Y' : Nat} (h : phase d M Y = some (d', M', Y')) : ¬ (d' = d ∧ M' = M) := by
  unfold phase at h
  split at h
  · cases h
  · split at h
    · cases h; omega
    · split at h
      · split at h
        · cases h
        · rename_i hne; cases h; exact hne
      · cases h

theorem bitsOf_2_2 : bitsOf 2 2 = [false, true] := rfl

/-- **The machine follows the map.**  Every configuration of the orbit is reached from blank tape, at a time at
least its index. -/
theorem orbit_reach : ∀ n : Nat, ∀ d M Y, orbit n = some (d, M, Y) → ∃ t, n ≤ t ∧ steps t init = some (PN d M Y)
  | 0, d, M, Y, h => by
    simp only [orbit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨69, by omega, ?_⟩
    rw [blank_to_P]; unfold PN; rw [bitsOf_2_2]
  | n + 1, d', M', Y', h => by
    simp only [orbit] at h
    split at h
    · rename_i d M Y hn
      obtain ⟨t, ht, hs⟩ := orbit_reach n d M Y hn
      obtain ⟨s, hs2⟩ := phase_sound h
      have hpos : s ≠ 0 := by
        intro e; subst e
        simp at hs2
        exact phase_ne h ⟨(PN_inj hs2).1.symm, (PN_inj hs2).2.symm⟩
      exact ⟨t + s, by omega, TM.steps_seq trans hs hs2⟩
    · cases h

/-- **Non-halting reduces to the phase map.**  If the orbit of `phase` from `PN 0 2 2` never gets stuck, the
machine never halts from blank tape. -/
theorem not_halts_of_orbit (h : ∀ n, orbit n ≠ none) : ¬ HaltsFromBlank := by
  rintro ⟨n, c', hn, hstep⟩
  have ho := h (n + 1)
  obtain ⟨⟨d, M, Y⟩, hx⟩ := Option.ne_none_iff_exists'.mp ho
  obtain ⟨t, ht, hs⟩ := orbit_reach (n + 1) d M Y hx
  have := TM.steps_halt trans hn hstep (t - n - 1)
  rw [show n + (t - n - 1 + 1) = t by omega] at this
  have hs' : TM.steps trans t init = some (PN d M Y) := hs
  rw [hs'] at this
  cases this

end H140108
