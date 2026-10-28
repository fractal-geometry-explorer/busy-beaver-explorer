import BB6.WideEntry

/-!
# Loop entries whose chain cannot end at a right end below N

`BB6/SmallEnd.lean` checks at a loop entry that no run of full passes from it, nor from its half pass, ends at a right
end below 178 (`NoSmallAt`, `smallOK`).  Nothing in that check needs 178: `NoEndBelow N` is the same for the right
ends below N, and `endOK N` checks it on a class of one coordinate in the same way, for every p below a bound P and
every r < N, with P past the linear bounds of L₁ in R on the cone for r up to N − 1.  To end at a right end below a few
hundred, the chain from a loop entry wider than 2⁴¹ (where R > W/29.02) needs at least 7 full passes from its last
landing, and at 36 digits no loop entry has them: every one of the 28,660 passes `endOK 769` (`thm/CleanBigMass.lean`;
an untrusted run finds none up to r = 5,000).

`EntryBigEnd N` is `EntryNoSmall` with N for 178 and a width of at least 2⁴¹, from where a round-7 break lands too high
to end below 769 (`thm/BigEndHalt.lean`).  `cleanBigOK` is the entry check of the clean-tape tree with it and with the
far entries of `BB6/WideEntry.lean`.
-/

namespace BB6.Sym
open BB6

/-- No run of full passes from right end R and left countdown L ends at a right end r < N: never R = 16^p·r with
r < N and L = 64^p·ℓ with ℓ ≡ 3 (mod 7), as every left countdown is.  `NoSmallAt` is `NoEndBelow 178`. -/
def NoEndBelow (N : Nat) (R L : Int) : Prop :=
  ∀ (p r : Nat) (ℓ : Int), r < N → R = (16 : Int) ^ p * (r : Int) → L = (64 : Int) ^ p * ℓ → ℓ % 7 = 3 → False

/-- `smallOK` for the right ends below N: the bounds of `q` hold on the cone, P is past them for right ends up to
N − 1, and for every p < P and r < N the point where R = 16^p·r is not an integer point of the cone with 64^p
dividing L. -/
def endOK (N : Nat) (R L : YForm) (ts : List YForm) (Γ : Int) (q : ExclCert) : Bool :=
  ltDec L ((R.smul q.β).addc (q.β₀ + 1)) ts Γ == some true &&
  ltDec ((R.smul q.α).addc (q.α₀ - 1)) L ts Γ == some true &&
  decide ((q.β.natAbs : Int) * ((N : Int) - 1) + (q.β₀.natAbs : Int) < (4 : Int) ^ q.P) &&
  decide ((q.α.natAbs : Int) * ((N : Int) - 1) + (q.α₀.natAbs : Int) < (4 : Int) ^ q.P) &&
  (List.range q.P).all (fun p =>
    (List.range N).all (fun r => smallPt1 R L ts Γ ((16 : Int) ^ p * (r : Int)) ((64 : Int) ^ p)))

/-- `lin_bound177` for right ends up to M. -/
theorem lin_boundM {X a a₀ r M : Int} (hX : 1 ≤ X) (hr0 : 0 ≤ r) (hr : r ≤ M) :
    a * (X * r) + a₀ ≤ X * ((a.natAbs : Int) * M + (a₀.natAbs : Int)) := by
  have ha : a ≤ (a.natAbs : Int) := Int.le_natAbs
  have ha₀ : a₀ ≤ (a₀.natAbs : Int) := Int.le_natAbs
  have hn : (0 : Int) ≤ (a.natAbs : Int) := Int.natCast_nonneg _
  have hn₀ : (0 : Int) ≤ (a₀.natAbs : Int) := Int.natCast_nonneg _
  have e1 : a * (X * r) ≤ (a.natAbs : Int) * (X * r) :=
    Int.mul_le_mul_of_nonneg_right ha (Int.mul_nonneg (by omega) hr0)
  have e2 : (a.natAbs : Int) * (X * r) ≤ (a.natAbs : Int) * (X * M) :=
    Int.mul_le_mul_of_nonneg_left (Int.mul_le_mul_of_nonneg_left hr (by omega)) hn
  have e3 : (a₀.natAbs : Int) ≤ X * (a₀.natAbs : Int) := by
    have := Int.mul_le_mul_of_nonneg_right hX hn₀
    rw [Int.one_mul] at this; exact this
  have e4 : X * ((a.natAbs : Int) * M + (a₀.natAbs : Int)) =
      (a.natAbs : Int) * (X * M) + X * (a₀.natAbs : Int) := by
    rw [Int.mul_add, Int.mul_left_comm]
  omega

theorem endOK_sound {N : Nat} {R L : YForm} {ts : List YForm} {Γ : Int} {q : ExclCert}
    (h : endOK N R L ts Γ q = true) {y0 y1 : Int} (hy : inCone ts Γ [y0, y1]) :
    NoEndBelow N (R.eval [y0, y1]) (L.eval [y0, y1]) := by
  intro p r ℓ hr hR hL h7
  simp only [endOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hb, ha⟩, hPb⟩, hPa⟩, hall⟩ := h
  by_cases hp : p < q.P
  · exact smallPt1_sound (hall p (List.mem_range.mpr hp) r (List.mem_range.mpr hr)) hy hR hL
  · -- p ≥ P: 64^p = 16^p · 4^p and 4^p ≥ 4^P, so the bounds leave only ℓ = 0
    have ub := (ltDec_sound _ _ ts Γ _ hy true hb).mpr rfl
    have lb := (ltDec_sound _ _ ts Γ _ hy true ha).mpr rfl
    simp only [eval_addc, eval_smul] at ub lb
    rw [hR, hL] at ub lb
    have hPp : q.P ≤ p := by omega
    have hX : (0 : Int) < 16 ^ p := Int.pow_pos (by decide)
    have h64 : (64 : Int) ^ p = 16 ^ p * 4 ^ p := by
      rw [show (64 : Int) = 16 * 4 by decide, Int.mul_pow]
    have h4 : (4 : Int) ^ q.P ≤ (4 : Int) ^ p := by exact_mod_cast Nat.pow_le_pow_right (by decide) hPp
    have hr0 : (0 : Int) ≤ (r : Int) := Int.natCast_nonneg r
    have hr1 : (r : Int) ≤ (N : Int) - 1 := by omega
    have hM : (0 : Int) ≤ (N : Int) - 1 := by omega
    have hβ : (0 : Int) ≤ (q.β.natAbs : Int) * ((N : Int) - 1) := Int.mul_nonneg (Int.natCast_nonneg _) hM
    have hα : (0 : Int) ≤ (q.α.natAbs : Int) * ((N : Int) - 1) := Int.mul_nonneg (Int.natCast_nonneg _) hM
    have hβ₀ : (0 : Int) ≤ (q.β₀.natAbs : Int) := Int.natCast_nonneg _
    have hα₀ : (0 : Int) ≤ (q.α₀.natAbs : Int) := Int.natCast_nonneg _
    have h70 : ℓ ≠ 0 := by omega
    rcases Int.lt_or_le 0 ℓ with hpos | hneg
    · have lb' := lin_boundM (X := 16 ^ p) (a := q.β) (a₀ := q.β₀) (by omega) hr0 hr1
      have hb : (16 : Int) ^ p * 4 ^ p * ℓ ≤
          16 ^ p * ((q.β.natAbs : Int) * ((N : Int) - 1) + (q.β₀.natAbs : Int)) := by
        rw [← h64]; omega
      exact big_p hX (by omega) (by omega) hb (by omega)
    · have lb' := lin_boundM (X := 16 ^ p) (a := -q.α) (a₀ := -q.α₀) (by omega) hr0 hr1
      simp only [Int.natAbs_neg] at lb'
      have hm : (16 : Int) ^ p * 4 ^ p * (-ℓ) ≤
          16 ^ p * ((q.α.natAbs : Int) * ((N : Int) - 1) + (q.α₀.natAbs : Int)) := by
        rw [Int.mul_neg, ← h64]
        have : -q.α * (16 ^ p * (r : Int)) = -(q.α * (16 ^ p * (r : Int))) := Int.neg_mul _ _
        omega
      exact big_p hX (by omega) (by omega) hm (by omega)

/-- The bounds of `exclCert` (only checked, never trusted), with P past them for right ends up to N − 1. -/
def endCert (N : Nat) (R L : YForm) (ts : List YForm) (Γ : Int) : ExclCert :=
  let q := exclCert R L ts Γ
  let B := max ((q.α.natAbs : Int) * ((N : Int) - 1) + q.α₀.natAbs)
    ((q.β.natAbs : Int) * ((N : Int) - 1) + q.β₀.natAbs)
  { q with P := log4Above B 64 0 }

/-! ## The entry -/

/-- From the loop entry with three walls `ms` and width W, no run of full passes ends at a right end below N, nor
does one after a half pass (when W ≡ 2 mod 4); and W ≥ 2⁴¹.  Stated for every reading of `ms` as three walls with the
last at W − R − 1, as `EntryNoSmall` is. -/
def EntryBigEnd (N : Nat) (ms : List Mark) (W : Nat) : Prop :=
  2 ^ 41 ≤ W ∧ ∀ R a b, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] → R + 1 ≤ W →
    NoEndBelow N R (passL1 ms W) ∧
    (W % 4 = 2 → ∀ R' L' : Int, 2 * R' = (R : Int) → 2 * L' = passL1 ms W + 35 * (W : Int) - 147 * (R : Int) - 60 →
      NoEndBelow N R' L')

/-- For N ≥ 178, `EntryBigEnd N` gives `EntryNoSmall`. -/
theorem EntryBigEnd.small {N : Nat} {ms : List Mark} {W : Nat} (hN : 178 ≤ N) (h : EntryBigEnd N ms W) :
    EntryNoSmall ms W := by
  refine ⟨Nat.le_trans (Nat.pow_le_pow_right (by decide) (by decide)) h.1, fun R a b hms hRW => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 R a b hms hRW
  exact ⟨fun p r ℓ hr => h1 p r ℓ (by omega),
    fun h4 R' L' e1 e2 p r ℓ hr => h2 h4 R' L' e1 e2 p r ℓ (by omega)⟩

/-- The check of `EntryBigEnd N` on a class of one coordinate (decided on the whole class): the round start is three
walls, the width is at least 2⁴¹, `endOK N` holds for the right end and the left countdown, and, unless W ≡ 0
(mod 4) on the class, for those after a half pass. -/
def bigEntryOK (N : Nat) (Γ : Int) (ts : List YForm) (ss : List SMark) (sW : YForm) : Bool :=
  match swwwOf ss with
  | none => false
  | some (_, b, c) =>
    let R := (sW.sub c).addc (-1)
    let L := L1Form b c sW
    ltDec (YForm.const (2 ^ 41 - 1)) sW ts Γ == some true &&
    endOK N R L ts Γ (endCert N R L ts Γ) &&
    (sW.modDec 4 == some 0 ||
      match R.half?, (halfL L sW R).half? with
      | some Rh, some Lh => endOK N Rh Lh ts Γ (endCert N Rh Lh ts Γ)
      | _, _ => false)

theorem bigEntryOK_sound {N : Nat} {Γ : Int} {ts : List YForm} {ss : List SMark} {sW : YForm}
    (h : bigEntryOK N Γ ts ss sW = true) {y : List Int} (hlen : y.length = 2) (hy : inCone ts Γ y)
    {ms : List Mark} {W : Nat} (hs : agL y ss ms) (hW : agN y sW W) : EntryBigEnd N ms W := by
  obtain ⟨y0, y1, rfl⟩ : ∃ y0 y1, y = [y0, y1] := by
    match y, hlen with
    | [y0, y1], _ => exact ⟨y0, y1, rfl⟩
  have hag := wwwOf_agree hs
  unfold bigEntryOK at h
  cases hsw : swwwOf ss with
  | none => rw [hsw] at h; cases h
  | some f =>
    obtain ⟨fa, fb, fc⟩ := f
    rw [hsw] at h
    obtain ⟨a, b, c, rfl, -, h2, h3⟩ := hag.2 fa fb fc hsw
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
    obtain ⟨⟨gw, hx⟩, hh⟩ := h
    have lw := (ltDec_sound _ _ ts Γ _ hy true gw).mpr rfl
    have hL := eval_L1Form fb fc sW [y0, y1]
    unfold agN at h2 h3 hW
    simp only [eval_const] at lw
    have hx' := endOK_sound hx hy
    simp only [eval_addc, eval_sub] at hx'
    have h41 : (2 : Nat) ^ 41 = 2199023255552 := rfl
    refine ⟨by rw [h41]; omega, ?_⟩
    intro R a' b' hms hRW
    simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms
    obtain ⟨rfl, rfl, hc⟩ := hms
    have eR : (R : Int) = sW.eval [y0, y1] - fc.eval [y0, y1] - 1 := by omega
    have e2 : passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W = (L1Form fb fc sW).eval [y0, y1] := by
      simp only [passL1, loopL1]; rw [hL]; omega
    refine ⟨?_, ?_⟩
    · rw [eR, e2]; exact hx'
    · intro h4 R' L' hR' hL'
      rcases hh with hh | hh
      · have := modDec_nat hW (m := 4) hh; omega
      · cases hRh : ((sW.sub fc).addc (-1)).half? with
        | none => rw [hRh] at hh; simp at hh
        | some Rh =>
          cases hLh : (halfL (L1Form fb fc sW) sW ((sW.sub fc).addc (-1))).half? with
          | none => rw [hRh, hLh] at hh; simp at hh
          | some Lh =>
            rw [hRh, hLh] at hh
            have hn := endOK_sound hh hy
            have eR' := eval_half _ _ hRh [y0, y1]
            have eL' := eval_half _ _ hLh [y0, y1]
            simp only [halfL, eval_addc, eval_sub, eval_add, eval_smul] at eR' eL'
            have r1 : Rh.eval [y0, y1] = R' := by omega
            have r2 : Lh.eval [y0, y1] = L' := by omega
            rw [← r1, ← r2]; exact hn

/-- The entry check of the clean-tape tree whose loop entries end big and far: `cleanEntryOK` (a loop entry that
cannot close, wider than the start), `bigEntryOK N` and `farEntryOK`. -/
def cleanBigOK (N : Nat) (Γ : Int) (ts : List YForm) (ss : List SMark) (sW w0 : YForm) : Bool :=
  cleanEntryOK Γ ts ss sW w0 && bigEntryOK N Γ ts ss sW && farEntryOK Γ ts ss sW

theorem cleanBigOK_sound {N : Nat} {Γ : Int} {ts : List YForm} {ss : List SMark} {sW w0 : YForm}
    (h : cleanBigOK N Γ ts ss sW w0 = true) {y : List Int} (hlen : y.length = 2) (hy : inCone ts Γ y)
    {ms : List Mark} {W W0 : Nat} (hs : agL y ss ms) (hW : agN y sW W) (h0 : agN y w0 W0) :
    EntryNoClose ms W ∧ EntryBigEnd N ms W ∧ EntryFar ms W ∧ W0 < W := by
  simp only [cleanBigOK, Bool.and_eq_true] at h
  obtain ⟨⟨hc, hb⟩, hf⟩ := h
  obtain ⟨hn, hw⟩ := cleanEntryOK_sound hc hlen hy hs hW h0
  exact ⟨hn, bigEntryOK_sound hb hlen hy hs hW, farEntryOK_sound hf hy hs hW, hw⟩

end BB6.Sym
