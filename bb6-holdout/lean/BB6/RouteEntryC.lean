import BB6.CleanEntryTree

/-!
# Loop entries whose loop cannot close, with the narrower closing classes

`BB6/RouteEntry.lean` checks, for a whole class at once, that no point of it closes through the loop, with the closing
set and classes of `closeClasses` (`closeTable`).  Once the endgame trees pass the end meetings at distance 2, a close
from a pass start of width at least 2²⁰ needs only the narrower classes of `closeClassC` (`loop_halt_wide_close`,
`thm/LoopClose.lean`): R = 2 or 4 with L₁ even, R = 8 with L₁ ≡ 0 mod 32, R = 16 with L₁ ≡ 0 mod 64, and R = 32 or 48
with L₁ ≡ 0 mod 128; none from R = 24, 64 or 176.  Fewer classes are easier to exclude.  This file is the check of
`BB6/RouteEntry.lean` with the table as a parameter (`NoCloseAtT`, `exclOKT`, `entryOKT`, `EntryNoCloseT`; with
`closeTable` they are `NoCloseAt`, `exclOK`, `entryOK` and `EntryNoClose`), and its instance for the table of
`closeClassC`, `closeTableC` (`entryOKC`, `EntryNoCloseC`, and `cleanEntryOKC` for the clean-tape trees).  The check of
each class of `closeTableC` is that of R's class of `closeTable` on fewer ℓ, so every class that passes `entryOK` passes
`entryOKC`; and every loop entry of `EntryNoClose` is one of `EntryNoCloseC` (`EntryNoClose.toC`).
-/

namespace BB6.Sym
open BB6

/-- No close after any number of full passes from right end R and left countdown L, with the closing set and classes
of the table `tb`: `NoCloseAt` with `tb` in place of `closeTable`. -/
def NoCloseAtT (tb : List (Nat × Int × Int)) (R L : Int) : Prop :=
  ∀ (p r : Nat) (M c ℓ : Int), (r, M, c) ∈ tb → R = (16 : Int) ^ p * (r : Int) → L = (64 : Int) ^ p * ℓ →
    ℓ % M = c → ℓ % 7 = 3 → False

/-- `exclOK` with the table `tb` in place of `closeTable` (`exclOKT_sound`). -/
def exclOKT (tb : List (Nat × Int × Int)) (R L : YForm) (ts : List YForm) (Γ : Int) (q : ExclCert) : Bool :=
  ltDec L ((R.smul q.β).addc (q.β₀ + 1)) ts Γ == some true &&
  ltDec ((R.smul q.α).addc (q.α₀ - 1)) L ts Γ == some true &&
  decide ((q.β.natAbs : Int) * 176 + (q.β₀.natAbs : Int) < (4 : Int) ^ q.P) &&
  decide ((q.α.natAbs : Int) * 176 + (q.α₀.natAbs : Int) < (4 : Int) ^ q.P) &&
  tb.all (fun e => decide (0 < e.2.1) && decide (0 ≤ e.2.2) && decide (e.2.2 < e.2.1) &&
    decide (e.1 ≤ 176) && (List.range q.P).all (fun p => winOK R L ts Γ q e.1 e.2.1 e.2.2 p))

theorem exclOKT_sound {tb : List (Nat × Int × Int)} {R L : YForm} {ts : List YForm} {Γ : Int} {q : ExclCert}
    (h : exclOKT tb R L ts Γ q = true) {y0 y1 : Int} (hy : inCone ts Γ [y0, y1]) :
    NoCloseAtT tb (R.eval [y0, y1]) (L.eval [y0, y1]) := by
  intro p r M c ℓ hmem hR hL hc h7
  simp only [exclOKT, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hb, ha⟩, hPb⟩, hPa⟩, hall⟩ := h
  have ub := (ltDec_sound _ _ ts Γ _ hy true hb).mpr rfl
  have lb := (ltDec_sound _ _ ts Γ _ hy true ha).mpr rfl
  simp only [eval_addc, eval_smul] at ub lb
  rw [hR, hL] at ub lb
  have hall' := hall (r, M, c) hmem
  dsimp only at hall'
  obtain ⟨⟨⟨⟨hM, hc0⟩, hcM⟩, hr176⟩, hwin⟩ := hall'
  by_cases hp : p < q.P
  · exact winOK_sound (hwin p (List.mem_range.mpr hp)) hM hy hR hL (by omega) (by omega) hc h7
  · -- p ≥ P: 64^p = 16^p · 4^p and 4^p ≥ 4^P, so the window holds only ℓ = 0
    have hPp : q.P ≤ p := by omega
    have hX : (0 : Int) < 16 ^ p := Int.pow_pos (by decide)
    have h64 : (64 : Int) ^ p = 16 ^ p * 4 ^ p := by
      rw [show (64 : Int) = 16 * 4 by decide, Int.mul_pow]
    have h4 : (4 : Int) ^ q.P ≤ (4 : Int) ^ p := by exact_mod_cast Nat.pow_le_pow_right (by decide) hPp
    have hr0 : (0 : Int) ≤ (r : Int) := Int.natCast_nonneg r
    have hr1 : (r : Int) ≤ 176 := by omega
    have h70 : ℓ ≠ 0 := by omega
    rcases Int.lt_or_le 0 ℓ with hpos | hneg
    · have lb' := lin_bound (X := 16 ^ p) (a := q.β) (a₀ := q.β₀) (by omega) hr0 hr1
      have hb : (16 : Int) ^ p * 4 ^ p * ℓ ≤ 16 ^ p * ((q.β.natAbs : Int) * 176 + (q.β₀.natAbs : Int)) := by
        rw [← h64]; omega
      exact big_p hX (by omega) (by omega) hb (by omega)
    · have lb' := lin_bound (X := 16 ^ p) (a := -q.α) (a₀ := -q.α₀) (by omega) hr0 hr1
      simp only [Int.natAbs_neg] at lb'
      have hm : (16 : Int) ^ p * 4 ^ p * (-ℓ) ≤
          16 ^ p * ((q.α.natAbs : Int) * 176 + (q.α₀.natAbs : Int)) := by
        rw [Int.mul_neg, ← h64]
        have : -q.α * (16 ^ p * (r : Int)) = -(q.α * (16 ^ p * (r : Int))) := Int.neg_mul _ _
        omega
      exact big_p hX (by omega) (by omega) hm (by omega)

/-- `entryOK` with the table `tb` in place of `closeTable`: the round start is a phase-0 pass start with every gap at
least 448, width at least 2²⁴ and, when W ≡ 2 mod 4, the middle wall at least 896 below the width (decided on the
class), and no point of the class closes through the loop from it in a class of `tb`, after full passes or after a
half pass and full passes. -/
def entryOKT (tb : List (Nat × Int × Int)) (Γ : Int) (ts : List YForm) (ss : List SMark) (sW : YForm) : Bool :=
  match swwwOf ss with
  | none => false
  | some (a, b, c) =>
    let R := (sW.sub c).addc (-1)
    let L := L1Form b c sW
    a.modDec 2 == some 1 && b.modDec 2 == some 0 && sW.modDec 2 == some 0 && R.modDec 2 == some 0 &&
    ltDec (YForm.const 1) R ts Γ == some true && ltDec (YForm.const 447) a ts Γ == some true &&
    ltDec (a.addc 447) b ts Γ == some true && ltDec (b.addc 447) c ts Γ == some true &&
    ltDec (YForm.const (2 ^ 24 - 1)) sW ts Γ == some true &&
    (sW.modDec 4 == some 0 || ltDec (b.addc 895) sW ts Γ == some true) &&
    exclOKT tb R L ts Γ (exclCert R L ts Γ) &&
    (sW.modDec 4 == some 0 ||
      match R.half?, (halfL L sW R).half? with
      | some Rh, some Lh => exclOKT tb Rh Lh ts Γ (exclCert Rh Lh ts Γ)
      | _, _ => false)

/-- `EntryNoClose` with the table `tb` in place of `closeTable`: a pass start with every gap at least 448 and width at
least 2²⁴, and with the middle wall at least 896 below the width when W ≡ 2 mod 4, from which the loop cannot close in
a class of `tb`: not after full passes, and (when W ≡ 2 mod 4) not after a half pass (2R′ = R,
2L₁′ = L₁ + 35W − 147R − 60) and full passes. -/
def EntryNoCloseT (tb : List (Nat × Int × Int)) (ms : List Mark) (W : Nat) : Prop :=
  2 ^ 24 ≤ W ∧ ∃ R a b, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] ∧ PassStart448 ms W R ∧
    (W % 4 = 2 → b + 896 ≤ W) ∧ NoCloseAtT tb R (passL1 ms W) ∧
    (W % 4 = 2 → ∀ R' L' : Int, 2 * R' = (R : Int) → 2 * L' = passL1 ms W + 35 * (W : Int) - 147 * (R : Int) - 60 →
      NoCloseAtT tb R' L')

theorem entryOKT_sound {tb : List (Nat × Int × Int)} {Γ : Int} {ts : List YForm} {ss : List SMark} {sW : YForm}
    (h : entryOKT tb Γ ts ss sW = true) {y : List Int} (hlen : y.length = 2) (hy : inCone ts Γ y)
    {ms : List Mark} {W : Nat} (hs : agL y ss ms) (hW : agN y sW W) : EntryNoCloseT tb ms W := by
  obtain ⟨y0, y1, rfl⟩ : ∃ y0 y1, y = [y0, y1] := by
    match y, hlen with
    | [y0, y1], _ => exact ⟨y0, y1, rfl⟩
  have hag := wwwOf_agree hs
  unfold entryOKT at h
  cases hsw : swwwOf ss with
  | none => rw [hsw] at h; cases h
  | some f =>
    obtain ⟨fa, fb, fc⟩ := f
    rw [hsw] at h
    obtain ⟨a, b, c, rfl, h1, h2, h3⟩ := hag.2 fa fb fc hsw
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨pa, pb⟩, pW⟩, pR⟩, g1⟩, ga⟩, gb⟩, gc⟩, gw⟩, g896⟩, hx⟩, hh⟩ := h
    have ma := modDec_nat h1 (m := 2) pa
    have mb := modDec_nat h2 (m := 2) pb
    have mW := modDec_nat hW (m := 2) pW
    have l1 := (ltDec_sound _ _ ts Γ _ hy true g1).mpr rfl
    have la := (ltDec_sound _ _ ts Γ _ hy true ga).mpr rfl
    have lb := (ltDec_sound _ _ ts Γ _ hy true gb).mpr rfl
    have lc := (ltDec_sound _ _ ts Γ _ hy true gc).mpr rfl
    have lw := (ltDec_sound _ _ ts Γ _ hy true gw).mpr rfl
    have pR' := eval_mod _ 2 0 pR [y0, y1]
    have hL := eval_L1Form fb fc sW [y0, y1]
    unfold agN at h1 h2 h3 hW
    simp only [eval_const, eval_addc, eval_sub] at l1 la lb lc lw pR'
    have hx' := exclOKT_sound hx hy
    simp only [eval_addc, eval_sub] at hx'
    have h24 : (2 : Nat) ^ 24 = 16777216 := rfl
    have hc' : W - (W - c - 1) - 1 = c := by omega
    refine ⟨by rw [h24]; omega, W - c - 1, a, b, by rw [hc'],
      ⟨a, b, by rw [hc'], by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩, ?_, ?_, ?_⟩
    · intro h4
      rcases g896 with g | g
      · have := modDec_nat hW (m := 4) g; omega
      · have := (ltDec_sound _ _ ts Γ _ hy true g).mpr rfl
        simp only [eval_addc] at this
        omega
    · have e1 : ((W - c - 1 : Nat) : Int) = sW.eval [y0, y1] - fc.eval [y0, y1] - 1 := by omega
      have e2 : passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W = (L1Form fb fc sW).eval [y0, y1] := by
        simp only [passL1, loopL1]; rw [hL]; omega
      rw [e1, e2]; exact hx'
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
            have hn := exclOKT_sound hh hy
            have eR := eval_half _ _ hRh [y0, y1]
            have eL := eval_half _ _ hLh [y0, y1]
            simp only [halfL, eval_addc, eval_sub, eval_add, eval_smul] at eR eL
            have e2 : passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W = (L1Form fb fc sW).eval [y0, y1] := by
              simp only [passL1, loopL1]; rw [hL]; omega
            have r1 : Rh.eval [y0, y1] = R' := by omega
            have r2 : Lh.eval [y0, y1] = L' := by omega
            rw [← r1, ← r2]; exact hn

/-- With `closeTable`, the table's check is that of `BB6/RouteEntry.lean`. -/
theorem NoCloseAtT_closeTable : NoCloseAtT closeTable = NoCloseAt := rfl

theorem exclOKT_closeTable : exclOKT closeTable = exclOK := rfl

theorem entryOKT_closeTable : entryOKT closeTable = entryOK := rfl

theorem EntryNoCloseT_closeTable : EntryNoCloseT closeTable = EntryNoClose := rfl

/-! ## The narrower classes -/

/-- The closing set with the class (modulus, residue) of the left countdown that a close from each right end needs once
the end meetings at distance 2 are passed (`closeClassC` in `thm/EndgameCloseStart.lean`). -/
def closeTableC : List (Nat × Int × Int) :=
  [(2, 2, 0), (4, 2, 0), (8, 32, 0), (16, 64, 0), (32, 128, 0), (48, 128, 0)]

/-- No close after any number of full passes in a class of `closeTableC`. -/
def NoCloseAtC (R L : Int) : Prop := NoCloseAtT closeTableC R L

/-- The entry check with the classes of `closeTableC`. -/
def entryOKC (Γ : Int) (ts : List YForm) (ss : List SMark) (sW : YForm) : Bool := entryOKT closeTableC Γ ts ss sW

/-- A loop entry from which the loop cannot close in a class of `closeTableC`. -/
def EntryNoCloseC (ms : List Mark) (W : Nat) : Prop := EntryNoCloseT closeTableC ms W

theorem entryOKC_sound {Γ : Int} {ts : List YForm} {ss : List SMark} {sW : YForm} (h : entryOKC Γ ts ss sW = true)
    {y : List Int} (hlen : y.length = 2) (hy : inCone ts Γ y) {ms : List Mark} {W : Nat} (hs : agL y ss ms)
    (hW : agN y sW W) : EntryNoCloseC ms W :=
  entryOKT_sound (tb := closeTableC) h hlen hy hs hW

/-- Each class of `closeTableC` lies in R's class of `closeTable`. -/
theorem closeTableC_sub {r : Nat} {M c ℓ : Int} (h : (r, M, c) ∈ closeTableC) (hc : ℓ % M = c) :
    ∃ M' c', (r, M', c') ∈ closeTable ∧ ℓ % M' = c' := by
  simp only [closeTableC, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  · exact ⟨2, 0, by simp [closeTable], hc⟩
  · exact ⟨2, 0, by simp [closeTable], hc⟩
  · exact ⟨8, 0, by simp [closeTable], by omega⟩
  · exact ⟨32, 0, by simp [closeTable], by omega⟩
  · exact ⟨64, 0, by simp [closeTable], by omega⟩
  · exact ⟨128, 0, by simp [closeTable], hc⟩

theorem NoCloseAt.toC {R L : Int} (h : NoCloseAt R L) : NoCloseAtC R L := by
  intro p r M c ℓ hmem hR hL hc h7
  obtain ⟨M', c', hmem', hc'⟩ := closeTableC_sub hmem hc
  exact h p r M' c' ℓ hmem' hR hL hc' h7

/-- Every loop entry that cannot close in a class of `closeTable` cannot close in one of `closeTableC`. -/
theorem EntryNoClose.toC {ms : List Mark} {W : Nat} (h : EntryNoClose ms W) : EntryNoCloseC ms W := by
  obtain ⟨hW, R, a, b, hms, hP, hh, hn, hhalf⟩ := h
  exact ⟨hW, R, a, b, hms, hP, hh, hn.toC, fun h4 R' L' h1 h2 => (hhalf h4 R' L' h1 h2).toC⟩

/-- The entry check of the clean-tape trees with the classes of `closeTableC`: `entryOKC`, and the entry is decided to
be wider than the start (`cleanEntryOK` with `entryOKC`). -/
def cleanEntryOKC (Γ : Int) (ts : List YForm) (ss : List SMark) (sW w0 : YForm) : Bool :=
  entryOKC Γ ts ss sW && widerB sW w0 ts Γ

theorem cleanEntryOKC_sound {Γ : Int} {ts : List YForm} {ss : List SMark} {sW w0 : YForm}
    (h : cleanEntryOKC Γ ts ss sW w0 = true) {y : List Int} (hlen : y.length = 2) (hy : inCone ts Γ y)
    {ms : List Mark} {W W0 : Nat} (hs : agL y ss ms) (hW : agN y sW W) (h0 : agN y w0 W0) :
    EntryNoCloseC ms W ∧ W0 < W := by
  simp only [cleanEntryOKC, Bool.and_eq_true] at h
  exact ⟨entryOKC_sound h.1 hlen hy hs hW, widerB_sound hy hW h0 h.2⟩

end BB6.Sym
