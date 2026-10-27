import BB6.Meets

/-!
# A halt needs a contact; at the right end, a contact is a close

The mark model `roundZ` never halts by itself: its only halting outcomes are a packet reaching a block on its left
(`pktBack`, `pktLand`) or a packet starting right after a block (`pktFrom`), and blocks never lie left of the active
gap or packet — the gap phase pushes only markers, walls and sleeping gaps onto the left list, and the packet phase
only takes marks off it.  So every halt of the machine from a well-formed state has to go through a configuration
the model calls `uncovered`, and this file says exactly which configurations those are: two neighbouring marks
touching (no stripe cell between them) in one of a few ways.

* `GapContact`: the gap meets a marker at distance 0 while a mark touches the gap from the left (`swap0`); a block
  touches the gap (`blockAtGap`); the wall or block that the gap meets is followed by a mark that touches the mark
  after it (`shift`).
* `LandContact`, `BackContact`: the packet, crossing a run of markers leftwards, finds a sleeping gap or a wall
  touching the marker it has just crossed, or a wall touched from its own left.

All other ways two marks can touch are either covered by the proven rules or impossible in a well-formed state
(the stripe between two 1-marks or two 0-marks is odd, so it is never empty; a packet never starts against a wall).

**Main theorem** (`halt_needs_contact`, `blank_halt_needs_contact`).  From any well-formed gap configuration with no
block on its left and no sleeping gap on its right — in particular from any well-formed round start without sleeping
gaps, and from blank tape — if the machine halts, then the mark model, run event by event across as many rounds as
needed (`Reach`), reaches a configuration where one of these contacts occurs (`Stuck`).  No fuel and no bound on the
number of rounds is involved: the induction is on the machine's halting time.

**Where the close comes in** (`stuck_cases`).  Of these contacts exactly one involves the gap meeting the end marker:
`swap0` with the marker being the last mark, an end meeting at distance d = 0 (`meetsOf g msR = [0]`) — the close
through which the halts found in the notes go (the d = 0 swap puts the end marker against a 1, forming a block).  All
the others are contacts between two marks of the tape away from an end meeting.  So: **a halt needs a close, or one
of the listed interior contacts.**  That the interior contacts never occur on the machine's tapes is not proved here
(it is measured: none occurs below 2^57, see "Checked against what the rules do not cover" in the notes).
-/

namespace BB6

/-! ## Touching marks -/

/-- The next mark of `ms` starts on the cell right after `m` ends: no stripe cell between them. -/
def touches (m : Mark) : List Mark → Prop
  | [] => False
  | m' :: _ => m'.p = m.p + mlen m.t

/-- The nearest mark of `msL` (left of the point `p`) ends right at `p`. -/
def touchesL (p : Nat) : List Mark → Prop
  | [] => False
  | m :: _ => m.p + mlen m.t = p

/-- No block among the marks. -/
def noB (ms : List Mark) : Prop := ∀ m ∈ ms, m.t ≠ .B

/-- No sleeping gap among the marks. -/
def noG (ms : List Mark) : Prop := ∀ m ∈ ms, m.t ≠ .G

theorem noB_cons {m : Mark} {ms : List Mark} (h : m.t ≠ .B) (hs : noB ms) : noB (m :: ms) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h
  · exact hs x hx

theorem noB_tail {m : Mark} {ms : List Mark} (h : noB (m :: ms)) : noB ms :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem noB_head {m : Mark} {ms : List Mark} (h : noB (m :: ms)) : m.t ≠ .B :=
  h m (List.mem_cons_self ..)

theorem noG_cons {m : Mark} {ms : List Mark} (h : m.t ≠ .G) (hs : noG ms) : noG (m :: ms) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h
  · exact hs x hx

theorem noG_tail {m : Mark} {ms : List Mark} (h : noG (m :: ms)) : noG ms :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem noG_head {m : Mark} {ms : List Mark} (h : noG (m :: ms)) : m.t ≠ .G :=
  h m (List.mem_cons_self ..)

theorem noG_nil : noG [] := fun _ h => absurd h List.not_mem_nil

theorem noG_shift (s : Nat) {ms : List Mark} (h : noG ms) : noG (shiftMarks s ms) := by
  intro x hx
  simp only [shiftMarks, List.mem_map] at hx
  obtain ⟨m, hm, rfl⟩ := hx
  exact h m hm

/-! ## Contacts -/

/-- The contacts at which the gap phase is not covered. -/
inductive GapContact : List Mark → Nat → List Mark → Prop
  /-- The gap meets a marker at distance 0 while a mark touches the gap from the left. -/
  | swap0 (msL : List Mark) (g : Nat) (msR : List Mark) (h : touchesL g msL) : GapContact msL g (⟨.M, g + 3⟩ :: msR)
  /-- A block touches the gap from the right. -/
  | blockAtGap (msL : List Mark) (g : Nat) (msR : List Mark) : GapContact msL g (⟨.B, g + 3⟩ :: msR)
  /-- The gap meets a wall or a block, and the mark after it touches the next one. -/
  | shift (msL : List Mark) (g : Nat) (m₁ m₂ : Mark) (r : List Mark) (h₁ : m₁.t = .W ∨ m₁.t = .B) (h : touches m₂ r) :
      GapContact msL g (m₁ :: m₂ :: r)

/-- The contacts at which the packet, having just crossed the marker at `y` (with the marks `msL` left of it), is
not covered: a sleeping gap or a wall touching that marker, a wall touched from its left, or one of these further
along a run of markers. -/
inductive LandContact : List Mark → Nat → Prop
  | gap (p : Nat) (L : List Mark) : LandContact (⟨.G, p⟩ :: L) (p + 3)
  | wall (p : Nat) (L : List Mark) : LandContact (⟨.W, p⟩ :: L) (p + 2)
  | wallL (p y : Nat) (L : List Mark) (h : touchesL p L) : LandContact (⟨.W, p⟩ :: L) y
  | next (p y : Nat) (L : List Mark) (h : LandContact L p) : LandContact (⟨.M, p⟩ :: L) y

/-- The contacts at which the packet phase started at a plain packet is not covered. -/
inductive BackContact : List Mark → Prop
  | wallL (p : Nat) (L : List Mark) (h : touchesL p L) : BackContact (⟨.W, p⟩ :: L)
  | land (p : Nat) (L : List Mark) (h : LandContact L p) : BackContact (⟨.M, p⟩ :: L)

/-! ## The model never halts while no block is left of the head -/

theorem leftOK_touch_val {g : Nat} {v : Bool} {m : Mark} {L : List Mark} (h : leftOK g v (m :: L))
    (ht : g ≤ m.p + mlen m.t) : m.p + mlen m.t = g ∧ mval m.t = !v := by
  obtain ⟨h1, h2, -⟩ := h
  have e : m.p + mlen m.t = g := by omega
  refine ⟨e, ?_⟩
  rw [e, Nat.sub_self] at h2
  cases hv : mval m.t <;> cases v <;> simp_all

theorem leftOK_pos {g : Nat} {L : List Mark} (h : leftOK g false L) : 1 ≤ g := by
  cases L with
  | nil => simp [leftOK] at h; omega
  | cons m L =>
    obtain ⟨h1, -, -⟩ := h
    have := mlen_ge m.t
    omega

theorem wallFreeB_false {g : Nat} {L : List Mark} (hL : leftOK g false L) (hw : wallFreeB g L = false) :
    touchesL g L := by
  cases L with
  | nil => simp only [wallFreeB, decide_eq_false_iff_not] at hw; have := leftOK_pos hL; omega
  | cons m L =>
    simp only [wallFreeB, decide_eq_false_iff_not, Nat.not_lt] at hw
    exact (leftOK_touch_val hL hw).1

theorem pktFrom_ne_uncovered {msL : List Mark} {g : Nat} {msR : List Mark} {W : Nat} (hL : leftOK g false msL) :
    pktFrom msL g msR W ≠ .uncovered := by
  unfold pktFrom
  cases hw : wallFreeB g msL with
  | true => simp
  | false =>
    cases msL with
    | nil => have h1 := leftOK_pos hL; simp [wallFreeB] at hw; omega
    | cons m L =>
      simp only [wallFreeB, decide_eq_false_iff_not, Nat.not_lt] at hw
      have hv := (leftOK_touch_val hL hw).2
      obtain ⟨t, p⟩ := m
      cases t <;> simp_all [mval]

theorem pktFrom_ne_halt {msL : List Mark} {g : Nat} {msR : List Mark} {W : Nat} (hB : noB msL) :
    pktFrom msL g msR W ≠ .halt := by
  unfold pktFrom
  split
  · simp
  · split
    · simp
    · rename_i m _ h; exact absurd rfl (noB_head hB)
    · simp

/-! ## One event of the gap phase -/

/-- What one gap event can produce from a well-formed configuration with no block on the left and no sleeping gap
on the right: the invariants again, the gap moving right relative to the width (`W' + g < W + g'`, the measure for
the induction below), never a halt, and `uncovered` only at a contact. -/
def GR.inv (msL : List Mark) (g : Nat) (msR : List Mark) (W : Nat) : GR → Prop
  | .gap a b c d => noB a ∧ noG c ∧ d + g < W + b
  | .pkt a _ c _ => noB a ∧ noG c
  | .pktM a _ c _ => noB a ∧ noG c
  | .halt => False
  | .uncovered => GapContact msL g msR

theorem pktFrom_inv {msL : List Mark} {g : Nat} {msR : List Mark} {W : Nat} (hL : leftOK g false msL) (hB : noB msL)
    (hG : noG msR) (msL₀ : List Mark) (g₀ : Nat) (msR₀ : List Mark) (W₀ : Nat) :
    GR.inv msL₀ g₀ msR₀ W₀ (pktFrom msL g msR W) := by
  have hnu := pktFrom_ne_uncovered (msR := msR) (W := W) hL
  have hnh := pktFrom_ne_halt (g := g) (msR := msR) (W := W) hB
  unfold pktFrom at hnu hnh ⊢
  cases hw : wallFreeB g msL with
  | true => exact ⟨hB, hG⟩
  | false =>
    simp only [hw, Bool.false_eq_true, if_false] at hnu hnh ⊢
    cases msL with
    | nil => exact absurd rfl hnu
    | cons m L =>
      obtain ⟨t, p⟩ := m
      cases t
      · exact absurd rfl hnu
      · exact ⟨noB_tail hB, hG⟩
      · exact absurd rfl hnu
      · exact absurd rfl hnh

theorem touches_of_freeAtB {m₂ : Mark} {v : Bool} {W : Nat} {r : List Mark} (hm : mlen m₂.t = 2)
    (hR : rightOK (m₂.p + mlen m₂.t) v W r) (hf : freeAtB (m₂.p + 2) W r = false) : touches m₂ r := by
  cases r with
  | nil => simp only [freeAtB, decide_eq_false_iff_not] at hf; simp only [rightOK] at hR; omega
  | cons m r =>
    simp only [freeAtB, decide_eq_false_iff_not, Nat.not_lt] at hf
    obtain ⟨h1, -, -⟩ := hR
    show m.p = m₂.p + mlen m₂.t
    omega

theorem touches_of_strictAfterB {m₂ : Mark} {v : Bool} {W : Nat} {r : List Mark} (k : Nat) (hm : mlen m₂.t = k)
    (hR : rightOK (m₂.p + mlen m₂.t) v W r) (hne : r ≠ []) (hf : strictAfterB (m₂.p + k) W r = false) :
    touches m₂ r := by
  cases r with
  | nil => exact absurd rfl hne
  | cons m r =>
    simp only [strictAfterB, decide_eq_false_iff_not, Nat.not_lt] at hf
    obtain ⟨h1, -, -⟩ := hR
    show m.p = m₂.p + mlen m₂.t
    omega

theorem gapEvent_inv (msL : List Mark) (g : Nat) (msR : List Mark) (W : Nat) (hwf : gapWF msL g msR W)
    (hB : noB msL) (hG : noG msR) : GR.inv msL g msR W (gapEvent msL g msR W) := by
  obtain ⟨hL, hR⟩ := hwf
  cases msR with
  | nil =>
    simp only [gapEvent]
    by_cases hW : W = g + 2
    · rw [if_pos hW]
      exact pktFrom_inv hL hB (noG_cons (by simp) noG_nil) _ _ _ _
    · rw [if_neg hW]
      exact ⟨hB, noG_cons (by simp) noG_nil⟩
  | cons m msR' =>
    have hR' : rightOK (g + 3) false W (m :: msR') := by
      rcases hR with h | ⟨h, -⟩
      · exact h
      · cases h
    obtain ⟨t, p⟩ := m
    have hG' := noG_tail hG
    obtain ⟨h1, h2, h3⟩ := hR'
    cases t with
    | G => exact absurd rfl (noG_head hG)
    | M =>
      simp only [mval, mlen] at h1 h2 h3
      have heven : (p - (g + 3)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h2.mp h) (by decide))
      have hnl : ¬ (p < g + 3) := by omega
      have hd2 : ¬ ((p - (g + 3)) % 2 = 1) := by omega
      simp only [gapEvent, hnl, hd2, if_false]
      by_cases hd4 : (p - (g + 3)) % 4 = 0
      · rw [if_pos hd4]
        by_cases hc : p - (g + 3) = 0 ∧ wallFreeB g msL = false
        · rw [if_pos hc]
          have hp : p = g + 3 := by omega
          subst hp
          exact GapContact.swap0 msL g msR' (wallFreeB_false hL hc.2)
        · rw [if_neg hc]
          refine ⟨noB_cons (by simp) hB, hG', ?_⟩
          omega
      · rw [if_neg hd4]
        by_cases hd : p - (g + 3) = 2
        · rw [if_pos hd]
          exact pktFrom_inv hL hB (noG_cons (by simp) hG') _ _ _ _
        · rw [if_neg hd]
          exact ⟨hB, noG_cons (by simp) hG'⟩
    | W =>
      simp only [mval, mlen] at h1 h2 h3
      cases msR' with
      | nil => exact ⟨hB, noG_cons (by simp) noG_nil⟩
      | cons m₂ r =>
        obtain ⟨t₂, p₂⟩ := m₂
        have hGr := noG_tail hG'
        obtain ⟨h4, h5, h6⟩ := h3
        try dsimp only at h4 h5 h6
        cases t₂ with
        | G => exact absurd rfl (noG_head hG')
        | M =>
          cases hf : freeAtB (p₂ + 2) W r with
          | true =>
            simp only [gapEvent, hf, if_true]
            refine ⟨hB, hGr, ?_⟩
            try simp only [mlen] at h4
            omega
          | false =>
            simp only [gapEvent, hf, Bool.false_eq_true, if_false]
            exact GapContact.shift msL g _ _ r (Or.inl rfl) (touches_of_freeAtB rfl h6 hf)
        | W =>
          cases hs : strictAfterB (p₂ + 2) W r with
          | true => simp only [gapEvent, hs, if_true]; exact ⟨hB, noG_cons (by simp) hGr⟩
          | false =>
            simp only [gapEvent, hs, Bool.false_eq_true, if_false]
            have hne : r ≠ [] := by
              rintro rfl
              simp only [strictAfterB, decide_eq_false_iff_not, Nat.not_lt] at hs
              simp only [rightOK, mval, mlen] at h6
              have : (W - (p₂ + 2)) % 2 = 1 := by first | exact h6.2.mpr rfl | exact h6.2.mpr trivial
              omega
            exact GapContact.shift msL g _ _ r (Or.inl rfl) (touches_of_strictAfterB 2 rfl h6 hne hs)
        | B =>
          simp only [gapEvent]
          by_cases hend : r.isEmpty = true ∧ W = p₂ + 3
          · rw [if_pos hend]; exact ⟨hB, noG_nil⟩
          · rw [if_neg hend]
            cases hs : strictAfterB (p₂ + 3) W r with
            | true => simp only [if_true]; exact ⟨hB, noG_cons (by simp) hGr⟩
            | false =>
              simp only [Bool.false_eq_true, if_false]
              have hne : r ≠ [] := by
                rintro rfl
                simp only [strictAfterB, decide_eq_false_iff_not, Nat.not_lt] at hs
                simp only [rightOK, mval, mlen] at h6
                exact hend ⟨rfl, by omega⟩
              exact GapContact.shift msL g _ _ r (Or.inl rfl) (touches_of_strictAfterB 3 rfl h6 hne hs)
    | B =>
      simp only [mval, mlen] at h1 h2 h3
      have heven : (p - (g + 3)) % 2 = 0 := mod_two_zero_of_not_one (fun h => absurd (h2.mp h) (by decide))
      simp only [gapEvent]
      by_cases hlt : p < g + 5
      · rw [if_pos hlt]
        have hp : p = g + 3 := by omega
        subst hp
        exact GapContact.blockAtGap msL g msR'
      · rw [if_neg hlt]
        have hBL : noB (⟨.G, g⟩ :: msL) := noB_cons (by simp) hB
        cases msR' with
        | nil => exact ⟨noB_cons (by simp) hBL, noG_cons (by simp) noG_nil, by omega⟩
        | cons m₂ r =>
          obtain ⟨t₂, p₂⟩ := m₂
          have hGr := noG_tail hG'
          obtain ⟨h4, h5, h6⟩ := h3
          try dsimp only at h4 h5 h6
          cases t₂ with
          | G => exact absurd rfl (noG_head hG')
          | M =>
            cases hf : freeAtB (p₂ + 2) W r with
            | true =>
              simp only [hf, if_true]
              refine ⟨noB_cons (by simp) hBL, hGr, ?_⟩
              omega
            | false =>
              simp only [hf, Bool.false_eq_true, if_false]
              exact GapContact.shift msL g _ _ r (Or.inr rfl) (touches_of_freeAtB (m₂ := ⟨.M, p₂⟩) rfl h6 hf)
          | W =>
            cases hs : strictAfterB (p₂ + 2) W r with
            | true =>
              simp only [hs, if_true]
              exact ⟨noB_cons (by simp) hBL, noG_cons (by simp) hGr, by omega⟩
            | false =>
              simp only [hs, Bool.false_eq_true, if_false]
              have hne : r ≠ [] := by
                rintro rfl
                simp only [strictAfterB, decide_eq_false_iff_not, Nat.not_lt] at hs
                simp only [rightOK, mval, mlen] at h6
                have : (W - (p₂ + 2)) % 2 = 1 := by first | exact h6.2.mpr rfl | exact h6.2.mpr trivial
                omega
              exact GapContact.shift msL g _ _ r (Or.inr rfl) (touches_of_strictAfterB (m₂ := ⟨.W, p₂⟩) 2 rfl h6 hne hs)
          | B =>
            simp only []
            by_cases hend : r.isEmpty = true ∧ W = p₂ + 3
            · rw [if_pos hend]
              refine ⟨noB_cons (by simp) hBL, noG_nil, ?_⟩
              omega
            · rw [if_neg hend]
              cases hs : strictAfterB (p₂ + 3) W r with
              | true =>
                simp only [if_true]
                exact ⟨noB_cons (by simp) hBL, noG_cons (by simp) hGr, by omega⟩
              | false =>
                simp only [Bool.false_eq_true, if_false]
                have hne : r ≠ [] := by
                  rintro rfl
                  simp only [strictAfterB, decide_eq_false_iff_not, Nat.not_lt] at hs
                  simp only [rightOK, mval, mlen] at h6
                  exact hend ⟨rfl, by omega⟩
                exact GapContact.shift msL g _ _ r (Or.inr rfl) (touches_of_strictAfterB (m₂ := ⟨.B, p₂⟩) 3 rfl h6 hne hs)

/-! ## The packet phase -/

/-- What the packet phase can produce, under the same invariants: never a halt, `uncovered` only at a contact. -/
def PR'.inv (C : Prop) : PR' → Prop
  | .gap a _ c _ => noB a ∧ noG c
  | .newRound ms _ => noG ms
  | .halt => False
  | .uncovered => C

theorem pktLand_inv (msL : List Mark) : ∀ (y : Nat) (msR : List Mark) (W : Nat), leftOK y true msL → noB msL →
    noG msR → (pktLand msL y msR W).inv (LandContact msL y) := by
  induction msL with
  | nil =>
    intro y msR W _ _ hG
    cases y with
    | zero => exact noG_cons (by simp) (noG_shift 4 hG)
    | succ y => exact noG_shift 2 (noG_cons (by simp) hG)
  | cons m L ih =>
    intro y msR W hL hB hG
    obtain ⟨t, p⟩ := m
    obtain ⟨h1, h2, h3⟩ := hL
    try dsimp only at h1 h2 h3
    have hBL := noB_tail hB
    cases t with
    | B => exact absurd rfl (noB_head hB)
    | M =>
      simp only [mval, mlen] at h1 h2 h3
      have hodd : (y - (p + 2)) % 2 = 1 := by first | exact h2.mpr rfl | exact h2.mpr trivial
      have hle : p + 3 ≤ y := by omega
      simp only [pktLand, hle, if_true]
      have := ih p (⟨.M, y⟩ :: msR) W h3 hBL (noG_cons (by simp) hG)
      generalize pktLand L p (⟨.M, y⟩ :: msR) W = r at this ⊢
      cases r with
      | uncovered => exact LandContact.next p y L this
      | _ => exact this
    | G =>
      simp only [mval, mlen] at h1 h2 h3
      simp only [pktLand]
      by_cases hlt : p + 3 < y
      · rw [if_pos hlt]; exact ⟨hBL, noG_cons (by simp) hG⟩
      · rw [if_neg hlt]
        have hy : y = p + 3 := by omega
        subst hy
        exact LandContact.gap p L
    | W =>
      simp only [mval, mlen] at h1 h2 h3
      simp only [pktLand]
      by_cases hc : p + 2 < y ∧ wallFreeB p L = true
      · rw [if_pos hc]; exact ⟨noB_cons (by simp) hBL, noG_cons (by simp) hG⟩
      · rw [if_neg hc]
        by_cases hy : y = p + 2
        · subst hy; exact LandContact.wall p L
        · have hw : wallFreeB p L = false := by
            cases hw : wallFreeB p L
            · rfl
            · exact absurd ⟨by omega, hw⟩ hc
          exact LandContact.wallL p y L (wallFreeB_false h3 hw)

theorem pktBack_inv (msL : List Mark) (x : Nat) (msR : List Mark) (W : Nat) (hL : leftOK x true msL) (hB : noB msL)
    (hG : noG msR) : (pktBack msL x msR W).inv (BackContact msL) := by
  cases msL with
  | nil => exact noG_shift 2 hG
  | cons m L =>
    obtain ⟨t, p⟩ := m
    obtain ⟨-, -, h3⟩ := hL
    try dsimp only at h3
    have hBL := noB_tail hB
    cases t with
    | B => exact absurd rfl (noB_head hB)
    | M =>
      simp only [pktBack]
      have := pktLand_inv L p msR W h3 hBL hG
      generalize pktLand L p msR W = r at this ⊢
      cases r with
      | uncovered => exact BackContact.land p L this
      | _ => exact this
    | G => exact ⟨hBL, hG⟩
    | W =>
      simp only [pktBack]
      cases hw : wallFreeB p L with
      | true => exact ⟨noB_cons (by simp) hBL, hG⟩
      | false => exact BackContact.wallL p L (wallFreeB_false h3 hw)

/-! ## Runs of the machine that halt -/

theorem steps_add (a b : Nat) (c : Cfg) : steps (a + b) c = (steps a c).bind (steps b) := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    cases hs : step c with
    | none => simp [steps, hs]
    | some d => rw [steps_succ_of_step _ hs, steps_succ_of_step _ hs, ih]

/-- A run that halts after `T` steps passes every configuration it reaches before `T`, and halts from there. -/
theorem steps_none_split {T n : Nat} {c c' : Cfg} (hT : steps T c = none) (hn : steps n c = some c') :
    n ≤ T ∧ steps (T - n) c' = none := by
  have hle : n ≤ T := by
    apply Nat.le_of_not_lt
    intro hlt
    have := steps_add T (n - T) c
    rw [show T + (n - T) = n by omega, hT, hn] at this
    cases this
  refine ⟨hle, ?_⟩
  have := steps_add n (T - n) c
  rw [show n + (T - n) = T by omega, hT, hn] at this
  exact this.symm

theorem steps_pos_of_st {n : Nat} {c c' : Cfg} (h : steps n c = some c') (hst : c.st ≠ c'.st) : 1 ≤ n := by
  cases n with
  | zero => simp at h; subst h; exact absurd rfl hst
  | succ n => omega

theorem rightOK_le {q : Nat} {u : Bool} {W : Nat} {ms : List Mark} (h : rightOK q u W ms) : q ≤ W := by
  induction ms generalizing q u with
  | nil => exact h.1
  | cons m ms ih => have := ih h.2.2; have := h.1; omega

/-! ## The model's run, event by event, across rounds -/

/-- A gap configuration of the mark model. -/
structure GS where
  msL : List Mark
  g : Nat
  msR : List Mark
  W : Nat

def GS.cfg (s : GS) : Cfg := midCfg s.msL s.g s.msR s.W
def GS.wf (s : GS) : Prop := gapWF s.msL s.g s.msR s.W
def GS.ev (s : GS) : GR := gapEvent s.msL s.g s.msR s.W

/-- Where the packet phase hands over: a woken gap, or the next round start (the gap at 1). -/
def PR'.next : PR' → Option GS
  | .gap a b c d => some ⟨a, b, c, d⟩
  | .newRound ms W => some ⟨[], 1, ms, W⟩
  | _ => none

/-- One step of the mark model between gap configurations: a gap event that leaves a gap, or a gap event that sends
a packet followed by the packet phase, up to the woken gap or the next round start. -/
inductive Step : GS → GS → Prop
  | gap {s : GS} {a : List Mark} {b : Nat} {c : List Mark} {d : Nat} (h : s.ev = .gap a b c d) : Step s ⟨a, b, c, d⟩
  | pkt {s t : GS} {a : List Mark} {x : Nat} {c : List Mark} {d : Nat} (h : s.ev = .pkt a x c d)
      (hn : (pktBack a x c d).next = some t) : Step s t
  | pktM {s t : GS} {a : List Mark} {y : Nat} {c : List Mark} {d : Nat} (h : s.ev = .pktM a y c d)
      (hn : (pktLand a y c d).next = some t) : Step s t

/-- The configurations the mark model reaches, any number of events and rounds on. -/
inductive Reach : GS → GS → Prop
  | refl (s : GS) : Reach s s
  | head {s t u : GS} : Step s t → Reach t u → Reach s u

/-- The mark model is stuck at `s`: its next event, or the packet phase it starts, meets a contact. -/
inductive Stuck (s : GS) : Prop
  | gap (h : GapContact s.msL s.g s.msR) : Stuck s
  | pkt {a : List Mark} {x : Nat} {c : List Mark} {d : Nat} (h : s.ev = .pkt a x c d) (hc : BackContact a) : Stuck s
  | pktM {a : List Mark} {y : Nat} {c : List Mark} {d : Nat} (h : s.ev = .pktM a y c d) (hc : LandContact a y) :
      Stuck s

theorem gapWF_of_wf {r : PR'} {t : GS} (hw : r.wf) (hn : r.next = some t) : t.wf := by
  cases r with
  | gap a b c d => cases hn; exact ⟨hw.1, Or.inl hw.2⟩
  | newRound ms W => cases hn; exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, Or.inl hw⟩
  | halt => cases hn
  | uncovered => cases hn

theorem inv_of_next {r : PR'} {C : Prop} {t : GS} (hi : r.inv C) (hn : r.next = some t) : noB t.msL ∧ noG t.msR := by
  cases r with
  | gap a b c d => cases hn; exact hi
  | newRound ms W => cases hn; exact ⟨fun _ h => absurd h List.not_mem_nil, hi⟩
  | halt => cases hn
  | uncovered => cases hn

theorem cfg_of_next {r : PR'} {t : GS} (hn : r.next = some t) : r.cfg = some t.cfg := by
  cases r with
  | gap a b c d => cases hn; rfl
  | newRound ms W => cases hn; rfl
  | halt => cases hn
  | uncovered => cases hn

/-- **A halt needs a contact.**  From a well-formed gap configuration with no block on its left and no sleeping gap
on its right, if the machine halts, then the mark model reaches (over any number of events and rounds) a well-formed
configuration at which it is stuck on a contact. -/
theorem halt_needs_contact : ∀ (T : Nat) (s : GS), s.wf → noB s.msL → noG s.msR → steps T s.cfg = none →
    ∃ t, Reach s t ∧ t.wf ∧ Stuck t := by
  intro T
  induction T using Nat.strongRecOn with
  | ind T ihT =>
  suffices H : ∀ (D : Nat) (s : GS), s.W - s.g = D → s.wf → noB s.msL → noG s.msR → steps T s.cfg = none →
      ∃ t, Reach s t ∧ t.wf ∧ Stuck t from fun s => H _ s rfl
  intro D
  induction D using Nat.strongRecOn with
  | ind D ihD =>
  intro s hD hwf hB hG hT
  have hinv := gapEvent_inv s.msL s.g s.msR s.W hwf hB hG
  have hok := gapEvent_ok s.msL s.g s.msR s.W hwf
  -- continue from a configuration reached in `n` steps, by the outer induction when n ≥ 1
  have cont : ∀ (n : Nat) (t : GS), 1 ≤ n → steps n s.cfg = some t.cfg → t.wf → noB t.msL → noG t.msR →
      Step s t → ∃ u, Reach s u ∧ u.wf ∧ Stuck u := by
    intro n t hn hs htw htB htG hst
    obtain ⟨hle, hT'⟩ := steps_none_split hT hs
    obtain ⟨u, hu, huw, hus⟩ := ihT (T - n) (by omega) t htw htB htG hT'
    exact ⟨u, Reach.head hst hu, huw, hus⟩
  have hev : s.ev = gapEvent s.msL s.g s.msR s.W := rfl
  generalize hr : gapEvent s.msL s.g s.msR s.W = r at hinv hok hev
  cases r with
  | halt => exact absurd hinv id
  | uncovered => exact ⟨s, Reach.refl s, hwf, Stuck.gap hinv⟩
  | gap a b c d =>
    obtain ⟨⟨n, hn⟩, hw'⟩ := hok
    obtain ⟨hB', hG', hlt⟩ := hinv
    let t : GS := ⟨a, b, c, d⟩
    by_cases hn0 : n = 0
    · subst hn0
      simp only [steps_zero, Option.some.injEq] at hn
      have hT' : steps T t.cfg = none := by
        show steps T (midCfg a b c d) = none
        rw [← hn]; exact hT
      have hW : s.g + 2 ≤ s.W := by
        rcases hwf.2 with h | ⟨-, h⟩
        · have := rightOK_le h; omega
        · omega
      have hW' : b + 2 ≤ d := by
        rcases hw'.2 with h | ⟨-, h⟩
        · have := rightOK_le h; omega
        · omega
      obtain ⟨u, hu, huw, hus⟩ := ihD (d - b) (by omega) t rfl hw' hB' hG' hT'
      exact ⟨u, Reach.head (Step.gap hev) hu, huw, hus⟩
    · exact cont n t (by omega) hn hw' hB' hG' (Step.gap hev)
  | pkt a x c d =>
    obtain ⟨⟨n₁, h₁⟩, hL', hR'⟩ := hok
    obtain ⟨hB', hG'⟩ := hinv
    have hpi := pktBack_inv a x c d hL' hB' hG'
    have hpw := pktBack_wf a x c d hL' hR'
    cases hpb : pktBack a x c d with
    | uncovered => rw [hpb] at hpi; exact ⟨s, Reach.refl s, hwf, Stuck.pkt hev hpi⟩
    | halt => rw [hpb] at hpi; exact absurd hpi id
    | gap a' b' c' d' =>
      have hnext : (pktBack a x c d).next = some ⟨a', b', c', d'⟩ := by rw [hpb]; rfl
      obtain ⟨n₂, h₂⟩ := pktBack_run a x c d hL' hR' (by rw [hpb]; simp)
      rw [cfg_of_next hnext] at h₂
      have hpos := steps_pos_of_st h₂ (by simp [pktCfg, GS.cfg, midCfg])
      exact cont (n₁ + n₂) _ (by omega) (steps_seq h₁ h₂) (gapWF_of_wf hpw hnext)
        (inv_of_next hpi hnext).1 (inv_of_next hpi hnext).2 (Step.pkt hev hnext)
    | newRound ms W' =>
      have hnext : (pktBack a x c d).next = some ⟨[], 1, ms, W'⟩ := by rw [hpb]; rfl
      obtain ⟨n₂, h₂⟩ := pktBack_run a x c d hL' hR' (by rw [hpb]; simp)
      rw [cfg_of_next hnext] at h₂
      have hpos := steps_pos_of_st h₂ (by simp [pktCfg, GS.cfg, midCfg])
      exact cont (n₁ + n₂) _ (by omega) (steps_seq h₁ h₂) (gapWF_of_wf hpw hnext)
        (inv_of_next hpi hnext).1 (inv_of_next hpi hnext).2 (Step.pkt hev hnext)
  | pktM a y c d =>
    obtain ⟨⟨n₁, h₁⟩, hL', hR'⟩ := hok
    obtain ⟨hB', hG'⟩ := hinv
    have hpi := pktLand_inv a y c d hL' hB' hG'
    have hpw := pktLand_wf a y c d hL' hR'
    cases hpb : pktLand a y c d with
    | uncovered => rw [hpb] at hpi; exact ⟨s, Reach.refl s, hwf, Stuck.pktM hev hpi⟩
    | halt => rw [hpb] at hpi; exact absurd hpi id
    | gap a' b' c' d' =>
      have hnext : (pktLand a y c d).next = some ⟨a', b', c', d'⟩ := by rw [hpb]; rfl
      obtain ⟨n₂, h₂⟩ := pktLand_run a y c d hL' hR' (by rw [hpb]; simp)
      rw [cfg_of_next hnext] at h₂
      have hpos := steps_pos_of_st h₂ (by simp [pktCfgM, GS.cfg, midCfg])
      exact cont (n₁ + n₂) _ (by omega) (steps_seq h₁ h₂) (gapWF_of_wf hpw hnext)
        (inv_of_next hpi hnext).1 (inv_of_next hpi hnext).2 (Step.pktM hev hnext)
    | newRound ms W' =>
      have hnext : (pktLand a y c d).next = some ⟨[], 1, ms, W'⟩ := by rw [hpb]; rfl
      obtain ⟨n₂, h₂⟩ := pktLand_run a y c d hL' hR' (by rw [hpb]; simp)
      rw [cfg_of_next hnext] at h₂
      have hpos := steps_pos_of_st h₂ (by simp [pktCfgM, GS.cfg, midCfg])
      exact cont (n₁ + n₂) _ (by omega) (steps_seq h₁ h₂) (gapWF_of_wf hpw hnext)
        (inv_of_next hpi hnext).1 (inv_of_next hpi hnext).2 (Step.pktM hev hnext)

/-- From a well-formed round start without sleeping gaps. -/
theorem round_halt_needs_contact (ms : List Mark) (W T : Nat) (h : roundWF ms W) (hG : noG ms)
    (hT : steps T (roundStart ms W) = none) : ∃ t, Reach ⟨[], 1, ms, W⟩ t ∧ t.wf ∧ Stuck t :=
  halt_needs_contact T ⟨[], 1, ms, W⟩ ⟨⟨fun _ => rfl, fun _ => rfl⟩, Or.inl h⟩
    (fun _ h => absurd h List.not_mem_nil) hG hT

/-- **From blank tape: if the machine ever halts, the mark model, run from the first round start, reaches a
contact.**  Equivalently: if no configuration the model reaches from the first round start is stuck on a contact,
the machine never halts. -/
theorem blank_halt_needs_contact (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ t, Reach ⟨[], 1, [], 5⟩ t ∧ t.wf ∧ Stuck t := by
  obtain ⟨-, hT'⟩ := steps_none_split hT first_round_start
  exact round_halt_needs_contact [] 5 _ first_round_start_wf noG_nil hT'

/-! ## Closes -/

/-- A close: the gap meets the end marker (the last mark, a marker) at distance d ≤ 2, as in `meetsZ`. -/
def Close (t : GS) : Prop := ∃ d, meetsOf t.g t.msR = [d] ∧ d ≤ 2

/-- The contact `swap0` with the end marker is a close, at distance 0. -/
theorem swap0_end_close (g : Nat) : meetsOf g [⟨.M, g + 3⟩] = [0] := by
  simp [meetsOf]

/-- When the gap meets only one more mark, the gap phase is stuck only at a close (the d = 0 swap with a mark
touching the gap from the left) or at a block touching the gap. -/
theorem gapContact_last {msL : List Mark} {g : Nat} {m : Mark} (h : GapContact msL g [m]) :
    (m = ⟨.M, g + 3⟩ ∧ touchesL g msL ∧ meetsOf g [m] = [0]) ∨ m = ⟨.B, g + 3⟩ := by
  cases h with
  | swap0 _ ht => exact Or.inl ⟨rfl, ht, swap0_end_close g⟩
  | blockAtGap => exact Or.inr rfl

/-- The gap-phase contacts away from the last mark: the gap is followed by at least two marks, and the contact is
`swap0` or `blockAtGap` at the nearest one or two marks touching further right. -/
theorem gapContact_cases {msL : List Mark} {g : Nat} {msR : List Mark} (h : GapContact msL g msR) :
    (∃ r, msR = ⟨.M, g + 3⟩ :: r ∧ touchesL g msL) ∨ (∃ r, msR = ⟨.B, g + 3⟩ :: r) ∨
    (∃ m₁ m₂ r, msR = m₁ :: m₂ :: r ∧ (m₁.t = .W ∨ m₁.t = .B) ∧ touches m₂ r) := by
  cases h with
  | swap0 _ ht => exact Or.inl ⟨_, rfl, ht⟩
  | blockAtGap => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | shift m₁ m₂ r h₁ h => exact Or.inr (Or.inr ⟨m₁, m₂, r, rfl, h₁, h⟩)

/-- **A halt needs a close**, given that the model meets no other contact: if every stuck configuration the model
reaches from a well-formed start (no block on the left, no sleeping gap on the right) is a close, then a halt of
the machine from that start needs a close in the model's run.  The hypothesis is exactly what is not proved: that
the interior contacts (every `Stuck` other than a close) are not reached. -/
theorem halt_needs_close (s : GS) (hwf : s.wf) (hB : noB s.msL) (hG : noG s.msR)
    (hint : ∀ t, Reach s t → t.wf → Stuck t → Close t) (T : Nat) (hT : steps T s.cfg = none) :
    ∃ t, Reach s t ∧ Close t := by
  obtain ⟨t, hr, hw, hs⟩ := halt_needs_contact T s hwf hB hG hT
  exact ⟨t, hr, hint t hr hw hs⟩

/-- The same from blank tape. -/
theorem blank_halt_needs_close (hint : ∀ t, Reach ⟨[], 1, [], 5⟩ t → t.wf → Stuck t → Close t) (T : Nat)
    (hT : steps T ⟨blank, blank, .A⟩ = none) : ∃ t, Reach ⟨[], 1, [], 5⟩ t ∧ Close t := by
  obtain ⟨t, hr, hw, hs⟩ := blank_halt_needs_contact T hT
  exact ⟨t, hr, hint t hr hw hs⟩

end BB6
