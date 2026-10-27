import BB6.SmallEnd

/-!
# Loop entries with a wide right end

The loop entries of the clean-tape trees are early: their right end is a fixed fraction of the width (at 36 digits
over the widths ≥ 2⁴¹, R > W/29.02 at every member of every entry class; untrusted, `EntryForms.lean`).  `EntryWide`
states the part of this that `thm/WideHalt.lean` uses, W ≤ 32R, and `wideEntryOK` decides it on a class of one
coordinate.  `cleanWideOK` is the entry check of the clean-tape tree with the small-end check (`cleanSmallOK`) with
this test added.
-/

namespace BB6.Sym
open BB6

/-- At the loop entry with three walls `ms` and width W, the right end is at least a 32nd of the width.  Stated for
every reading of `ms` as three walls with the last at W − R − 1, as `EntryNoSmall` is. -/
def EntryWide (ms : List Mark) (W : Nat) : Prop :=
  ∀ R a b, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] → R + 1 ≤ W → W ≤ 32 * R

/-- The check of `EntryWide` on a class (decided on the whole cone): the round start is three walls and W − 1 < 32R. -/
def wideEntryOK (Γ : Int) (ts : List YForm) (ss : List SMark) (sW : YForm) : Bool :=
  match swwwOf ss with
  | none => false
  | some (_, _, c) => ltDec (sW.addc (-1)) (((sW.sub c).addc (-1)).smul 32) ts Γ == some true

theorem wideEntryOK_sound {Γ : Int} {ts : List YForm} {ss : List SMark} {sW : YForm}
    (h : wideEntryOK Γ ts ss sW = true) {y : List Int} (hy : inCone ts Γ y) {ms : List Mark} {W : Nat}
    (hs : agL y ss ms) (hW : agN y sW W) : EntryWide ms W := by
  have hag := wwwOf_agree hs
  unfold wideEntryOK at h
  cases hsw : swwwOf ss with
  | none => rw [hsw] at h; cases h
  | some f =>
    obtain ⟨fa, fb, fc⟩ := f
    rw [hsw] at h
    obtain ⟨a, b, c, rfl, -, -, h3⟩ := hag.2 fa fb fc hsw
    simp only [beq_iff_eq] at h
    have lt := (ltDec_sound _ _ ts Γ _ hy true h).mpr rfl
    simp only [eval_addc, eval_sub, eval_smul] at lt
    unfold agN at h3 hW
    intro R a' b' hms hRW
    simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms
    obtain ⟨-, -, hc⟩ := hms
    omega

/-- The entry check of the clean-tape tree with wide entries: `cleanSmallOK` (a loop entry that cannot close nor end
small, wider than the start) and `wideEntryOK`. -/
def cleanWideOK (Γ : Int) (ts : List YForm) (ss : List SMark) (sW w0 : YForm) : Bool :=
  cleanSmallOK Γ ts ss sW w0 && wideEntryOK Γ ts ss sW

theorem cleanWideOK_sound {Γ : Int} {ts : List YForm} {ss : List SMark} {sW w0 : YForm}
    (h : cleanWideOK Γ ts ss sW w0 = true) {y : List Int} (hlen : y.length = 2) (hy : inCone ts Γ y)
    {ms : List Mark} {W W0 : Nat} (hs : agL y ss ms) (hW : agN y sW W) (h0 : agN y w0 W0) :
    EntryNoClose ms W ∧ EntryNoSmall ms W ∧ EntryWide ms W ∧ W0 < W := by
  simp only [cleanWideOK, Bool.and_eq_true] at h
  obtain ⟨hn, hs', hw⟩ := cleanSmallOK_sound h.1 hlen hy hs hW h0
  exact ⟨hn, hs', wideEntryOK_sound h.2 hy hs hW, hw⟩

end BB6.Sym
