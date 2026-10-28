import BB6.RouteEntryC
import BB6.BigEnd

/-!
# The clean-tape trees' entry tests, with the narrower closing classes

`cleanSmallOK`, `cleanWideOK`, `cleanFarOK` and `cleanBigOK` (`BB6/SmallEnd.lean`, `BB6/WideEntry.lean`,
`BB6/BigEnd.lean`) add tests of the loop entry to `cleanEntryOK`.  Here they are with `cleanEntryOKC`
(`BB6/RouteEntryC.lean`) in its place: the entry cannot close in a class of `closeClassC` (`EntryNoCloseC`), and the
other tests are as they were.
-/

namespace BB6.Sym
open BB6

/-- `cleanSmallOK` with `cleanEntryOKC`: a loop entry that cannot close in a class of `closeClassC` nor end small,
wider than the start. -/
def cleanSmallOKC (Γ : Int) (ts : List YForm) (ss : List SMark) (sW w0 : YForm) : Bool :=
  cleanEntryOKC Γ ts ss sW w0 && smallEntryOK Γ ts ss sW

theorem cleanSmallOKC_sound {Γ : Int} {ts : List YForm} {ss : List SMark} {sW w0 : YForm}
    (h : cleanSmallOKC Γ ts ss sW w0 = true) {y : List Int} (hlen : y.length = 2) (hy : inCone ts Γ y)
    {ms : List Mark} {W W0 : Nat} (hs : agL y ss ms) (hW : agN y sW W) (h0 : agN y w0 W0) :
    EntryNoCloseC ms W ∧ EntryNoSmall ms W ∧ W0 < W := by
  simp only [cleanSmallOKC, Bool.and_eq_true] at h
  obtain ⟨hn, hw⟩ := cleanEntryOKC_sound h.1 hlen hy hs hW h0
  exact ⟨hn, smallEntryOK_sound h.2 hlen hy hs hW, hw⟩

/-- `cleanWideOK` with `cleanSmallOKC`. -/
def cleanWideOKC (Γ : Int) (ts : List YForm) (ss : List SMark) (sW w0 : YForm) : Bool :=
  cleanSmallOKC Γ ts ss sW w0 && wideEntryOK Γ ts ss sW

theorem cleanWideOKC_sound {Γ : Int} {ts : List YForm} {ss : List SMark} {sW w0 : YForm}
    (h : cleanWideOKC Γ ts ss sW w0 = true) {y : List Int} (hlen : y.length = 2) (hy : inCone ts Γ y)
    {ms : List Mark} {W W0 : Nat} (hs : agL y ss ms) (hW : agN y sW W) (h0 : agN y w0 W0) :
    EntryNoCloseC ms W ∧ EntryNoSmall ms W ∧ EntryWide ms W ∧ W0 < W := by
  simp only [cleanWideOKC, Bool.and_eq_true] at h
  obtain ⟨hn, hs', hw⟩ := cleanSmallOKC_sound h.1 hlen hy hs hW h0
  exact ⟨hn, hs', wideEntryOK_sound h.2 hy hs hW, hw⟩

/-- `cleanFarOK` with `cleanSmallOKC`. -/
def cleanFarOKC (Γ : Int) (ts : List YForm) (ss : List SMark) (sW w0 : YForm) : Bool :=
  cleanSmallOKC Γ ts ss sW w0 && farEntryOK Γ ts ss sW

theorem cleanFarOKC_sound {Γ : Int} {ts : List YForm} {ss : List SMark} {sW w0 : YForm}
    (h : cleanFarOKC Γ ts ss sW w0 = true) {y : List Int} (hlen : y.length = 2) (hy : inCone ts Γ y)
    {ms : List Mark} {W W0 : Nat} (hs : agL y ss ms) (hW : agN y sW W) (h0 : agN y w0 W0) :
    EntryNoCloseC ms W ∧ EntryNoSmall ms W ∧ EntryFar ms W ∧ W0 < W := by
  simp only [cleanFarOKC, Bool.and_eq_true] at h
  obtain ⟨hn, hs', hw⟩ := cleanSmallOKC_sound h.1 hlen hy hs hW h0
  exact ⟨hn, hs', farEntryOK_sound h.2 hy hs hW, hw⟩

/-- `cleanBigOK` with `cleanEntryOKC`. -/
def cleanBigOKC (N : Nat) (Γ : Int) (ts : List YForm) (ss : List SMark) (sW w0 : YForm) : Bool :=
  cleanEntryOKC Γ ts ss sW w0 && bigEntryOK N Γ ts ss sW && farEntryOK Γ ts ss sW

theorem cleanBigOKC_sound {N : Nat} {Γ : Int} {ts : List YForm} {ss : List SMark} {sW w0 : YForm}
    (h : cleanBigOKC N Γ ts ss sW w0 = true) {y : List Int} (hlen : y.length = 2) (hy : inCone ts Γ y)
    {ms : List Mark} {W W0 : Nat} (hs : agL y ss ms) (hW : agN y sW W) (h0 : agN y w0 W0) :
    EntryNoCloseC ms W ∧ EntryBigEnd N ms W ∧ EntryFar ms W ∧ W0 < W := by
  simp only [cleanBigOKC, Bool.and_eq_true] at h
  obtain ⟨⟨hc, hb⟩, hf⟩ := h
  obtain ⟨hn, hw⟩ := cleanEntryOKC_sound hc hlen hy hs hW h0
  exact ⟨hn, bigEntryOK_sound hb hlen hy hs hW, farEntryOK_sound hf hy hs hW, hw⟩

end BB6.Sym
