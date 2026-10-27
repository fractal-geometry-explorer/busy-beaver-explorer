import BB6.CleanEntryTree

/-!
# Loop entries whose chain cannot end at a small right end

The pass-start trees for the right ends R < 178 (`passTreeR`, `thm/PassHalt.lean`) are where the known halts past the
loop's end live (1/8 of the pass starts with R = 6, some with R = 4 and R = 8), so the question is whether the run
from blank tape can reach such a pass start at all.  It reaches pass starts through the clean-tape tree's loop entries
and then the loop's chain.  A run of full passes divides R by 16 and the left countdown L₁ by 64, so it ends at a right
end r < 178 only if R = 16^p·r and L₁ = 64^p·ℓ for some p, with ℓ ≡ 3 (mod 7) as every left countdown is
(`NoSmallAt` says this never happens).  On a class of one coordinate, as in the clean-tape trees, R = 16^p·r fixes the
point, and `smallOK` checks every such point for the whole class at once, as `exclOK` (`BB6/RouteEntry.lean`) does
for the closing classes: for each p below a bound P and each r < 178 the point is not an integer point of the cone, or
64^p does not divide L₁ there (`smallPt1`); and past P the linear bounds α·R + α₀ ≤ L₁ ≤ β·R + β₀ on the cone leave
only ℓ = 0, which no left countdown is.  The bounds are those of `exclCert`, with P raised for r up to 177
(`smallCert`).

`smallEntryOK` asks this at a loop entry for the full passes from it and, when W ≡ 2 (mod 4) is not excluded on the
class, for the full passes after a half pass (R → R/2, 2·L₁′ = L₁ + 35W − 147R − 60), and the entry's width at least
2³⁷, from where a round-7 break lands far above the small right ends (`thm/SmallEndHalt.lean`).  `EntryNoSmall` is
what it certifies.
-/

namespace BB6.Sym
open BB6

/-- No run of full passes from right end R and left countdown L ends at a right end r < 178: never R = 16^p·r with
r < 178 and L = 64^p·ℓ with ℓ ≡ 3 (mod 7), as every left countdown is. -/
def NoSmallAt (R L : Int) : Prop :=
  ∀ (p r : Nat) (ℓ : Int), r < 178 → R = (16 : Int) ^ p * (r : Int) → L = (64 : Int) ^ p * ℓ → ℓ % 7 = 3 → False

/-- On a class of one coordinate, at the point where R = N (R = N fixes y₀): y₀ is not an integer, or S does not
divide L there, or the point is outside the cone. -/
def smallPt1 (R L : YForm) (ts : List YForm) (Γ N S : Int) : Bool :=
  let r0 := R.c.getD 0 0
  let y0 := (N - R.k) / r0
  R.c.getD 1 0 == 0 && L.c.getD 1 0 == 0 && ts.all (fun t => t.c.getD 1 0 == 0) && r0 != 0 &&
    ((N - R.k) % r0 != 0 || (L.k + L.c.getD 0 0 * y0) % S != 0 ||
      ts.any (fun t => decide (t.k + t.c.getD 0 0 * y0 < Γ)))

theorem smallPt1_sound {R L : YForm} {ts : List YForm} {Γ N S : Int} (h : smallPt1 R L ts Γ N S = true)
    {y0 y1 : Int} (hy : inCone ts Γ [y0, y1]) (hR : R.eval [y0, y1] = N) {ℓ : Int}
    (hL : L.eval [y0, y1] = S * ℓ) : False := by
  simp only [smallPt1, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true,
    List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hR1, hL1⟩, hts⟩, hr0⟩, h⟩ := h
  rw [eval_two, hR1] at hR
  rw [eval_two, hL1] at hL
  have e : N - R.k = R.c.getD 0 0 * y0 := by omega
  rw [e, Int.mul_emod_right, Int.mul_ediv_cancel_left _ hr0] at h
  rcases h with (h | h) | ⟨t, ht, hlt⟩
  · exact h rfl
  · apply h
    rw [show L.k + L.c.getD 0 0 * y0 = S * ℓ by omega]
    exact Int.mul_emod_right S ℓ
  · have := hy t ht
    rw [eval_two, hts t ht] at this
    omega

/-- No run of full passes from any point of the class inside the cone ends at a right end below 178
(`smallOK_sound`): the bounds of `q` hold on the cone, P is past them, and for every p < P and r < 178 the point
where R = 16^p·r is not an integer point of the cone with 64^p dividing L. -/
def smallOK (R L : YForm) (ts : List YForm) (Γ : Int) (q : ExclCert) : Bool :=
  ltDec L ((R.smul q.β).addc (q.β₀ + 1)) ts Γ == some true &&
  ltDec ((R.smul q.α).addc (q.α₀ - 1)) L ts Γ == some true &&
  decide ((q.β.natAbs : Int) * 177 + (q.β₀.natAbs : Int) < (4 : Int) ^ q.P) &&
  decide ((q.α.natAbs : Int) * 177 + (q.α₀.natAbs : Int) < (4 : Int) ^ q.P) &&
  (List.range q.P).all (fun p =>
    (List.range 178).all (fun r => smallPt1 R L ts Γ ((16 : Int) ^ p * (r : Int)) ((64 : Int) ^ p)))

/-- `lin_bound` for right ends up to 177. -/
theorem lin_bound177 {X a a₀ r : Int} (hX : 1 ≤ X) (hr0 : 0 ≤ r) (hr : r ≤ 177) :
    a * (X * r) + a₀ ≤ X * ((a.natAbs : Int) * 177 + (a₀.natAbs : Int)) := by
  have ha : a ≤ (a.natAbs : Int) := Int.le_natAbs
  have ha₀ : a₀ ≤ (a₀.natAbs : Int) := Int.le_natAbs
  have hn : (0 : Int) ≤ (a.natAbs : Int) := Int.natCast_nonneg _
  have hn₀ : (0 : Int) ≤ (a₀.natAbs : Int) := Int.natCast_nonneg _
  have e1 : a * (X * r) ≤ (a.natAbs : Int) * (X * r) :=
    Int.mul_le_mul_of_nonneg_right ha (Int.mul_nonneg (by omega) hr0)
  have e2 : (a.natAbs : Int) * (X * r) ≤ (a.natAbs : Int) * (X * 177) :=
    Int.mul_le_mul_of_nonneg_left (Int.mul_le_mul_of_nonneg_left hr (by omega)) hn
  have e3 : (a₀.natAbs : Int) ≤ X * (a₀.natAbs : Int) := by
    have := Int.mul_le_mul_of_nonneg_right hX hn₀
    rw [Int.one_mul] at this; exact this
  have e4 : X * ((a.natAbs : Int) * 177 + (a₀.natAbs : Int)) =
      (a.natAbs : Int) * (X * 177) + X * (a₀.natAbs : Int) := by grind
  omega

theorem smallOK_sound {R L : YForm} {ts : List YForm} {Γ : Int} {q : ExclCert} (h : smallOK R L ts Γ q = true)
    {y0 y1 : Int} (hy : inCone ts Γ [y0, y1]) : NoSmallAt (R.eval [y0, y1]) (L.eval [y0, y1]) := by
  intro p r ℓ hr hR hL h7
  simp only [smallOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
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
    have hr1 : (r : Int) ≤ 177 := by omega
    have h70 : ℓ ≠ 0 := by omega
    rcases Int.lt_or_le 0 ℓ with hpos | hneg
    · have lb' := lin_bound177 (X := 16 ^ p) (a := q.β) (a₀ := q.β₀) (by omega) hr0 hr1
      have hb : (16 : Int) ^ p * 4 ^ p * ℓ ≤ 16 ^ p * ((q.β.natAbs : Int) * 177 + (q.β₀.natAbs : Int)) := by
        rw [← h64]; omega
      exact big_p hX (by omega) (by omega) hb (by omega)
    · have lb' := lin_bound177 (X := 16 ^ p) (a := -q.α) (a₀ := -q.α₀) (by omega) hr0 hr1
      simp only [Int.natAbs_neg] at lb'
      have hm : (16 : Int) ^ p * 4 ^ p * (-ℓ) ≤
          16 ^ p * ((q.α.natAbs : Int) * 177 + (q.α₀.natAbs : Int)) := by
        rw [Int.mul_neg, ← h64]
        have : -q.α * (16 ^ p * (r : Int)) = -(q.α * (16 ^ p * (r : Int))) := Int.neg_mul _ _
        omega
      exact big_p hX (by omega) (by omega) hm (by omega)

/-- The bounds of `exclCert` (only checked, never trusted), with P past them for right ends up to 177. -/
def smallCert (R L : YForm) (ts : List YForm) (Γ : Int) : ExclCert :=
  let q := exclCert R L ts Γ
  let B := max ((q.α.natAbs : Int) * 177 + q.α₀.natAbs) ((q.β.natAbs : Int) * 177 + q.β₀.natAbs)
  { q with P := log4Above B 64 0 }

/-! ## The entry -/

/-- From the loop entry with three walls `ms` and width W, no run of full passes ends at a right end below 178, nor
does one after a half pass (when W ≡ 2 mod 4); and W ≥ 2³⁷.  Stated for every reading of `ms` as three walls with the
last at W − R − 1, so that it applies to the right end of any pass start at `ms`. -/
def EntryNoSmall (ms : List Mark) (W : Nat) : Prop :=
  2 ^ 37 ≤ W ∧ ∀ R a b, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] → R + 1 ≤ W →
    NoSmallAt R (passL1 ms W) ∧
    (W % 4 = 2 → ∀ R' L' : Int, 2 * R' = (R : Int) → 2 * L' = passL1 ms W + 35 * (W : Int) - 147 * (R : Int) - 60 →
      NoSmallAt R' L')

/-- The check of `EntryNoSmall` on a class of one coordinate (decided on the whole class): the round start is three
walls, the width is at least 2³⁷, `smallOK` holds for the right end and the left countdown, and, unless W ≡ 0 (mod 4)
on the class, for those after a half pass. -/
def smallEntryOK (Γ : Int) (ts : List YForm) (ss : List SMark) (sW : YForm) : Bool :=
  match swwwOf ss with
  | none => false
  | some (_, b, c) =>
    let R := (sW.sub c).addc (-1)
    let L := L1Form b c sW
    ltDec (YForm.const (2 ^ 37 - 1)) sW ts Γ == some true &&
    smallOK R L ts Γ (smallCert R L ts Γ) &&
    (sW.modDec 4 == some 0 ||
      match R.half?, (halfL L sW R).half? with
      | some Rh, some Lh => smallOK Rh Lh ts Γ (smallCert Rh Lh ts Γ)
      | _, _ => false)

theorem smallEntryOK_sound {Γ : Int} {ts : List YForm} {ss : List SMark} {sW : YForm}
    (h : smallEntryOK Γ ts ss sW = true) {y : List Int} (hlen : y.length = 2) (hy : inCone ts Γ y) {ms : List Mark}
    {W : Nat} (hs : agL y ss ms) (hW : agN y sW W) : EntryNoSmall ms W := by
  obtain ⟨y0, y1, rfl⟩ : ∃ y0 y1, y = [y0, y1] := by
    match y, hlen with
    | [y0, y1], _ => exact ⟨y0, y1, rfl⟩
  have hag := wwwOf_agree hs
  unfold smallEntryOK at h
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
    have hx' := smallOK_sound hx hy
    simp only [eval_addc, eval_sub] at hx'
    have h37 : (2 : Nat) ^ 37 = 137438953472 := rfl
    refine ⟨by rw [h37]; omega, ?_⟩
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
            have hn := smallOK_sound hh hy
            have eR' := eval_half _ _ hRh [y0, y1]
            have eL' := eval_half _ _ hLh [y0, y1]
            simp only [halfL, eval_addc, eval_sub, eval_add, eval_smul] at eR' eL'
            have r1 : Rh.eval [y0, y1] = R' := by omega
            have r2 : Lh.eval [y0, y1] = L' := by omega
            rw [← r1, ← r2]; exact hn

/-- The entry check of the clean-tape tree with small-end exclusions: `cleanEntryOK` (a loop entry that cannot close,
wider than the start) and `smallEntryOK`. -/
def cleanSmallOK (Γ : Int) (ts : List YForm) (ss : List SMark) (sW w0 : YForm) : Bool :=
  cleanEntryOK Γ ts ss sW w0 && smallEntryOK Γ ts ss sW

theorem cleanSmallOK_sound {Γ : Int} {ts : List YForm} {ss : List SMark} {sW w0 : YForm}
    (h : cleanSmallOK Γ ts ss sW w0 = true) {y : List Int} (hlen : y.length = 2) (hy : inCone ts Γ y)
    {ms : List Mark} {W W0 : Nat} (hs : agL y ss ms) (hW : agN y sW W) (h0 : agN y w0 W0) :
    EntryNoClose ms W ∧ EntryNoSmall ms W ∧ W0 < W := by
  simp only [cleanSmallOK, Bool.and_eq_true] at h
  obtain ⟨hn, hw⟩ := cleanEntryOK_sound h.1 hlen hy hs hW h0
  exact ⟨hn, smallEntryOK_sound h.2 hlen hy hs hW, hw⟩

end BB6.Sym
