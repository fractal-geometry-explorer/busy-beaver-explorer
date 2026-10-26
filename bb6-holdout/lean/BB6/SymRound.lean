import BB6.SymForm

/-!
# The zipper model on symbolic positions

`symPktLand`, `symPktBack`, `symPktFrom`, `symGapEvent` and `symRoundZ` mirror `pktLand`, `pktBack`, `pktFrom`,
`gapEvent` and `roundZ` branch for branch, with positions `YForm`s and every test decided on the cone (`ltDec`,
`eqDec`) or by residues (`modDec`, `half?`); `none` means a test was not decided.  The soundness theorems say: at any
point `y` of the cone, a concrete state that agrees with the symbolic one (same mark types, positions equal to the
forms' values) has a concrete outcome that agrees with the symbolic outcome.
-/

namespace BB6.Sym
open BB6

structure SMark where
  t : MarkT
  p : YForm
  deriving Repr

/-- Agreement of a natural number with a form at `y`. -/
def agN (y : List Int) (f : YForm) (n : Nat) : Prop := (n : Int) = f.eval y

def agM (y : List Int) (s : SMark) (m : Mark) : Prop := s.t = m.t ∧ agN y s.p m.p

def agL (y : List Int) : List SMark → List Mark → Prop
  | [], [] => True
  | s :: ss, m :: ms => agM y s m ∧ agL y ss ms
  | _, _ => False

theorem agN_addc {y : List Int} {f : YForm} {n : Nat} (h : agN y f n) (k : Nat) : agN y (f.addc k) (n + k) := by
  unfold agN at *; simp only [eval_addc]; omega

theorem agN_subc {y : List Int} {f : YForm} {n : Nat} (h : agN y f n) (k : Nat) (hk : k ≤ n) :
    agN y (f.addc (-(k : Int))) (n - k) := by
  unfold agN at *; simp only [eval_addc]; omega

theorem agN_const (y : List Int) (n : Nat) : agN y (YForm.const n) n := by simp [agN]

theorem agN_nonneg {y : List Int} {f : YForm} {n : Nat} (h : agN y f n) : 0 ≤ f.eval y := by
  unfold agN at h; omega

/-- Translating decided order tests into facts about the agreeing naturals. -/
theorem lt_of_ltDec {ts : List YForm} {Γ : Int} {y : List Int} (hy : inCone ts Γ y) {a b : YForm} {n m : Nat}
    (ha : agN y a n) (hb : agN y b m) {r : Bool} (h : ltDec a b ts Γ = some r) : (n < m ↔ r = true) := by
  have := ltDec_sound a b ts Γ y hy r h
  unfold agN at ha hb
  constructor
  · intro hnm; exact this.mp (by omega)
  · intro hr; have := this.mpr hr; omega

theorem eq_of_eqDec {ts : List YForm} {Γ : Int} {y : List Int} (hy : inCone ts Γ y) {a b : YForm} {n m : Nat}
    (ha : agN y a n) (hb : agN y b m) {r : Bool} (h : eqDec a b ts Γ = some r) : (n = m ↔ r = true) := by
  have := eqDec_sound a b ts Γ y hy r h
  unfold agN at ha hb
  constructor
  · intro hnm; exact this.mp (by omega)
  · intro hr; have := this.mpr hr; omega

def sShift (s : Nat) (ms : List SMark) : List SMark := ms.map (fun m => ⟨m.t, m.p.addc s⟩)

theorem agL_shift {y : List Int} {ss : List SMark} {ms : List Mark} (h : agL y ss ms) (s : Nat) :
    agL y (sShift s ss) (shiftMarks s ms) := by
  induction ss generalizing ms with
  | nil => cases ms with
    | nil => trivial
    | cons _ _ => exact absurd h id
  | cons a ss ih =>
    cases ms with
    | nil => exact absurd h id
    | cons m ms =>
      obtain ⟨⟨ht, hp⟩, hr⟩ := h
      exact ⟨⟨ht, agN_addc hp s⟩, ih hr⟩

/-! ## Outcomes -/

inductive SPR where
  | gap (msL : List SMark) (g : YForm) (msR : List SMark) (W : YForm)
  | newRound (ms : List SMark) (W : YForm)
  | halt
  | uncovered

def agPR (y : List Int) : SPR → PR' → Prop
  | .gap sL sg sR sW, .gap msL g msR W => agL y sL msL ∧ agN y sg g ∧ agL y sR msR ∧ agN y sW W
  | .newRound ss sW, .newRound ms W => agL y ss ms ∧ agN y sW W
  | .halt, .halt => True
  | .uncovered, .uncovered => True
  | _, _ => False

/-! ## The packet phase -/

section
variable (ts : List YForm) (Γ : Int)

def symWallFreeB (w : YForm) : List SMark → Option Bool
  | [] => ltDec (YForm.const 0) w ts Γ
  | m :: _ => ltDec (m.p.addc (mlen m.t)) w ts Γ

theorem symWallFreeB_sound {y : List Int} (hy : inCone ts Γ y) {w : YForm} {wn : Nat} (hw : agN y w wn)
    {sL : List SMark} {msL : List Mark} (hL : agL y sL msL) {r : Bool} (h : symWallFreeB ts Γ w sL = some r) :
    wallFreeB wn msL = r := by
  cases sL with
  | nil =>
    cases msL with
    | nil =>
      have := lt_of_ltDec hy (agN_const y 0) hw h
      simp only [wallFreeB]
      cases r <;> simp_all <;> omega
    | cons _ _ => exact absurd hL id
  | cons s sL =>
    cases msL with
    | nil => exact absurd hL id
    | cons m msL =>
      obtain ⟨⟨ht, hp⟩, -⟩ := hL
      have hp' : agN y (s.p.addc (mlen s.t)) (m.p + mlen m.t) := by rw [ht]; exact agN_addc hp _
      have := lt_of_ltDec hy hp' hw h
      simp only [wallFreeB]
      cases r <;> simp_all

def symPktLand : List SMark → YForm → List SMark → YForm → Option SPR
  | [], y, sR, W =>
    match eqDec y (YForm.const 0) ts Γ with
    | some true => some (.newRound (⟨.W, YForm.const 5⟩ :: sShift 4 sR) (W.addc 4))
    | some false => some (.newRound (sShift 2 (⟨.M, y⟩ :: sR)) (W.addc 2))
    | none => none
  | m :: sL, y, sR, W =>
    match m.t with
    | .M =>
      match ltDec y (m.p.addc 3) ts Γ with
      | some false => symPktLand sL m.p (⟨.M, y⟩ :: sR) W
      | some true => some .uncovered
      | none => none
    | .G =>
      match ltDec (m.p.addc 3) y ts Γ with
      | some true => some (.gap sL (m.p.addc 2) (⟨.M, y⟩ :: sR) W)
      | some false => some .uncovered
      | none => none
    | .W =>
      match ltDec (m.p.addc 2) y ts Γ with
      | some true =>
        match symWallFreeB ts Γ m.p sL with
        | some true => some (.gap (⟨.M, m.p.addc (-1)⟩ :: sL) (m.p.addc 1) (⟨.M, y⟩ :: sR) W)
        | some false => some .uncovered
        | none => none
      | some false => some .uncovered
      | none => none
    | .B => some .halt

theorem wallFreeB_pos {w : Nat} {msL : List Mark} (h : wallFreeB w msL = true) : 1 ≤ w := by
  cases msL <;> simp [wallFreeB] at h <;> omega

theorem symPktLand_sound {y : List Int} (hy : inCone ts Γ y) (sL : List SMark) :
    ∀ (msL : List Mark) (sy : YForm) (yn : Nat) (sR : List SMark) (msR : List Mark) (sW : YForm) (Wn : Nat)
      (r : SPR), agL y sL msL → agN y sy yn → agL y sR msR → agN y sW Wn →
      symPktLand ts Γ sL sy sR sW = some r → agPR y r (pktLand msL yn msR Wn) := by
  induction sL with
  | nil =>
    intro msL sy yn sR msR sW Wn r hL hy' hR hW h
    cases msL with
    | cons _ _ => exact absurd hL id
    | nil =>
      simp only [symPktLand] at h
      cases he : eqDec sy (YForm.const 0) ts Γ with
      | none => rw [he] at h; cases h
      | some b =>
        rw [he] at h
        have hb := eq_of_eqDec hy hy' (agN_const y 0) he
        cases b with
        | true =>
          cases h
          have : yn = 0 := hb.mpr rfl
          subst this
          simp only [pktLand, agPR]
          exact ⟨⟨⟨rfl, agN_const y 5⟩, agL_shift hR 4⟩, agN_addc hW 4⟩
        | false =>
          cases h
          have hne : yn ≠ 0 := fun h0 => by simpa using hb.mp h0
          obtain ⟨k, rfl⟩ : ∃ k, yn = k + 1 := ⟨yn - 1, by omega⟩
          simp only [pktLand, agPR]
          exact ⟨agL_shift (show agL y (⟨.M, sy⟩ :: sR) (⟨.M, k + 1⟩ :: msR) from ⟨⟨rfl, hy'⟩, hR⟩) 2, agN_addc hW 2⟩
  | cons s sL ih =>
    intro msL sy yn sR msR sW Wn r hL hy' hR hW h
    cases msL with
    | nil => exact absurd hL id
    | cons m msL =>
      obtain ⟨⟨ht, hp⟩, hL'⟩ := hL
      obtain ⟨t, p⟩ := m
      simp only at ht hp
      subst ht
      cases hst : s.t with
      | M =>
        simp only [symPktLand, hst] at h
        cases hd : ltDec sy (s.p.addc 3) ts Γ with
        | none => rw [hd] at h; cases h
        | some b =>
          rw [hd] at h
          have hb := lt_of_ltDec hy hy' (agN_addc hp 3) hd
          cases b with
          | true => cases h; simp only [pktLand, hst]; rw [if_neg (by have := hb.mpr rfl; omega)]; trivial
          | false =>
            have hn : ¬ yn < p + 3 := fun h' => by simpa using hb.mp h'
            simp only [pktLand, hst]
            rw [if_pos (by omega)]
            exact ih msL s.p p (⟨.M, sy⟩ :: sR) (⟨.M, yn⟩ :: msR) sW Wn r hL' hp ⟨⟨rfl, hy'⟩, hR⟩ hW h
      | G =>
        simp only [symPktLand, hst] at h
        cases hd : ltDec (s.p.addc 3) sy ts Γ with
        | none => rw [hd] at h; cases h
        | some b =>
          rw [hd] at h
          have hb := lt_of_ltDec hy (agN_addc hp 3) hy' hd
          cases b with
          | true =>
            cases h; simp only [pktLand, hst]; rw [if_pos (hb.mpr rfl)]
            exact ⟨hL', agN_addc hp 2, ⟨⟨rfl, hy'⟩, hR⟩, hW⟩
          | false =>
            cases h; simp only [pktLand, hst]; rw [if_neg (fun h' => by simpa using hb.mp h')]; trivial
      | W =>
        simp only [symPktLand, hst] at h
        cases hd : ltDec (s.p.addc 2) sy ts Γ with
        | none => rw [hd] at h; cases h
        | some b =>
          rw [hd] at h
          have hb := lt_of_ltDec hy (agN_addc hp 2) hy' hd
          cases b with
          | false =>
            cases h; simp only [pktLand, hst]
            rw [if_neg (fun h' => by simpa using hb.mp h'.1)]; trivial
          | true =>
            cases hwf : symWallFreeB ts Γ s.p sL with
            | none => rw [hwf] at h; cases h
            | some c =>
              rw [hwf] at h
              have hc := symWallFreeB_sound ts Γ hy hp hL' hwf
              cases c with
              | true =>
                cases h; simp only [pktLand, hst]
                rw [if_pos ⟨hb.mpr rfl, hc⟩]
                have hp1 := wallFreeB_pos hc
                exact ⟨⟨⟨rfl, by simpa using agN_subc hp 1 hp1⟩, hL'⟩, agN_addc hp 1, ⟨⟨rfl, hy'⟩, hR⟩, hW⟩
              | false =>
                cases h; simp only [pktLand, hst]
                rw [if_neg (fun h' => by rw [hc] at h'; exact absurd h'.2 (by decide))]; trivial
      | B =>
        simp only [symPktLand, hst] at h
        cases h; simp only [pktLand, hst]; trivial

def symPktBack : List SMark → YForm → List SMark → YForm → Option SPR
  | [], _, sR, W => some (.newRound (sShift 2 sR) (W.addc 2))
  | m :: sL, _, sR, W =>
    match m.t with
    | .M => symPktLand ts Γ sL m.p sR W
    | .G => some (.gap sL (m.p.addc 2) sR W)
    | .W =>
      match symWallFreeB ts Γ m.p sL with
      | some true => some (.gap (⟨.M, m.p.addc (-1)⟩ :: sL) (m.p.addc 1) sR W)
      | some false => some .uncovered
      | none => none
    | .B => some .halt

theorem symPktBack_sound {y : List Int} (hy : inCone ts Γ y) (sL : List SMark) (msL : List Mark) (sx : YForm)
    (xn : Nat) (sR : List SMark) (msR : List Mark) (sW : YForm) (Wn : Nat) (r : SPR) (hL : agL y sL msL)
    (hR : agL y sR msR) (hW : agN y sW Wn) (h : symPktBack ts Γ sL sx sR sW = some r) :
    agPR y r (pktBack msL xn msR Wn) := by
  cases sL with
  | nil =>
    cases msL with
    | cons _ _ => exact absurd hL id
    | nil => cases h; exact ⟨agL_shift hR 2, agN_addc hW 2⟩
  | cons s sL =>
    cases msL with
    | nil => exact absurd hL id
    | cons m msL =>
      obtain ⟨⟨ht, hp⟩, hL'⟩ := hL
      obtain ⟨t, p⟩ := m
      simp only at ht hp
      subst ht
      cases hst : s.t with
      | M =>
        simp only [symPktBack, hst] at h
        simp only [pktBack, hst]
        exact symPktLand_sound ts Γ hy sL msL s.p p sR msR sW Wn r hL' hp hR hW h
      | G =>
        simp only [symPktBack, hst] at h; cases h
        simp only [pktBack, hst]; exact ⟨hL', agN_addc hp 2, hR, hW⟩
      | W =>
        simp only [symPktBack, hst] at h
        cases hwf : symWallFreeB ts Γ s.p sL with
        | none => rw [hwf] at h; cases h
        | some c =>
          rw [hwf] at h
          have hc := symWallFreeB_sound ts Γ hy hp hL' hwf
          cases c with
          | true =>
            cases h; simp only [pktBack, hst, hc, if_true]
            have hp1 := wallFreeB_pos hc
            exact ⟨⟨⟨rfl, by simpa using agN_subc hp 1 hp1⟩, hL'⟩, agN_addc hp 1, hR, hW⟩
          | false => cases h; simp only [pktBack, hst, hc]; trivial
      | B =>
        simp only [symPktBack, hst] at h; cases h; simp only [pktBack, hst]; trivial

end

/-! ## The gap phase -/

inductive SGR where
  | gap (msL : List SMark) (g : YForm) (msR : List SMark) (W : YForm)
  | pkt (msL : List SMark) (x : YForm) (msR : List SMark) (W : YForm)
  | pktM (msL : List SMark) (y : YForm) (msR : List SMark) (W : YForm)
  | halt
  | uncovered

def agGR (y : List Int) : SGR → GR → Prop
  | .gap sL sg sR sW, .gap msL g msR W => agL y sL msL ∧ agN y sg g ∧ agL y sR msR ∧ agN y sW W
  | .pkt sL sx sR sW, .pkt msL x msR W => agL y sL msL ∧ agN y sx x ∧ agL y sR msR ∧ agN y sW W
  | .pktM sL sx sR sW, .pktM msL x msR W => agL y sL msL ∧ agN y sx x ∧ agL y sR msR ∧ agN y sW W
  | .halt, .halt => True
  | .uncovered, .uncovered => True
  | _, _ => False

theorem mod_of_modDec {y : List Int} {f : YForm} {n : Nat} (h : agN y f n) {m r : Int} (hm : f.modDec m = some r) :
    (n : Int) % m = r := by
  have := eval_mod f m r hm y; unfold agN at h; rw [h]; exact this

theorem half_of_half {y : List Int} {f g : YForm} {n : Nat} (h : agN y f n) (hh : f.half? = some g) :
    (n : Int) = 2 * g.eval y := by
  have := eval_half f g hh y; unfold agN at h; rw [h]; exact this

section
variable (ts : List YForm) (Γ : Int)

def symStrictAfterB (q W : YForm) : List SMark → Option Bool
  | [] => ltDec q W ts Γ
  | m :: _ => ltDec q m.p ts Γ

def symFreeAtB (q W : YForm) : List SMark → Option Bool
  | [] => (ltDec W q ts Γ).map (!·)
  | m :: _ => ltDec q m.p ts Γ

theorem symStrictAfterB_sound {y : List Int} (hy : inCone ts Γ y) {q W : YForm} {qn Wn : Nat} (hq : agN y q qn)
    (hW : agN y W Wn) {sR : List SMark} {msR : List Mark} (hR : agL y sR msR) {r : Bool}
    (h : symStrictAfterB ts Γ q W sR = some r) : strictAfterB qn Wn msR = r := by
  cases sR with
  | nil =>
    cases msR with
    | cons _ _ => exact absurd hR id
    | nil => have := lt_of_ltDec hy hq hW h; simp only [strictAfterB]; cases r <;> simp_all
  | cons s sR =>
    cases msR with
    | nil => exact absurd hR id
    | cons m msR =>
      have := lt_of_ltDec hy hq hR.1.2 h; simp only [strictAfterB]; cases r <;> simp_all

theorem symFreeAtB_sound {y : List Int} (hy : inCone ts Γ y) {q W : YForm} {qn Wn : Nat} (hq : agN y q qn)
    (hW : agN y W Wn) {sR : List SMark} {msR : List Mark} (hR : agL y sR msR) {r : Bool}
    (h : symFreeAtB ts Γ q W sR = some r) : freeAtB qn Wn msR = r := by
  cases sR with
  | nil =>
    cases msR with
    | cons _ _ => exact absurd hR id
    | nil =>
      simp only [symFreeAtB] at h
      cases hd : ltDec W q ts Γ with
      | none => rw [hd] at h; cases h
      | some b =>
        rw [hd] at h; cases h
        have := lt_of_ltDec hy hW hq hd; simp only [freeAtB]; cases b <;> simp_all <;> omega
  | cons s sR =>
    cases msR with
    | nil => exact absurd hR id
    | cons m msR =>
      have := lt_of_ltDec hy hq hR.1.2 h; simp only [freeAtB]; cases r <;> simp_all

def symPktFrom (sL : List SMark) (sg : YForm) (sR : List SMark) (sW : YForm) : Option SGR :=
  match symWallFreeB ts Γ sg sL with
  | some true => some (.pkt sL (sg.addc (-1)) sR sW)
  | some false =>
    match sL with
    | s :: sL' => match s.t with
      | .M => some (.pktM sL' s.p sR sW)
      | .B => some .halt
      | _ => some .uncovered
    | [] => some .uncovered
  | none => none

theorem symPktFrom_sound {y : List Int} (hy : inCone ts Γ y) {sL : List SMark} {msL : List Mark} {sg : YForm}
    {g : Nat} {sR : List SMark} {msR : List Mark} {sW : YForm} {Wn : Nat} {r : SGR} (hL : agL y sL msL)
    (hg : agN y sg g) (hR : agL y sR msR) (hW : agN y sW Wn) (h : symPktFrom ts Γ sL sg sR sW = some r) :
    agGR y r (pktFrom msL g msR Wn) := by
  unfold symPktFrom at h
  cases hwf : symWallFreeB ts Γ sg sL with
  | none => rw [hwf] at h; cases h
  | some c =>
    rw [hwf] at h
    have hc := symWallFreeB_sound ts Γ hy hg hL hwf
    cases c with
    | true =>
      cases h; simp only [pktFrom, hc, if_true, agGR]
      exact ⟨hL, by simpa using agN_subc hg 1 (wallFreeB_pos hc), hR, hW⟩
    | false =>
      simp only at h
      simp only [pktFrom, hc, Bool.false_eq_true, if_false]
      cases sL with
      | nil => cases msL with
        | nil => cases h; trivial
        | cons _ _ => exact absurd hL id
      | cons s sL' =>
        cases msL with
        | nil => exact absurd hL id
        | cons m msL' =>
          obtain ⟨⟨ht, hp⟩, hL'⟩ := hL
          obtain ⟨t, p⟩ := m
          simp only at ht hp
          subst ht
          cases hst : s.t with
          | M => simp only [hst] at h; cases h; simp only [hst]; exact ⟨hL', hp, hR, hW⟩
          | B => simp only [hst] at h; cases h; simp only [hst]; trivial
          | G => simp only [hst] at h; cases h; simp only [hst]; trivial
          | W => simp only [hst] at h; cases h; simp only [hst]; trivial

end

section
variable (ts : List YForm) (Γ : Int)

/-- The gap meets nothing. -/
def symGapNil (sL : List SMark) (sg sW : YForm) : Option SGR :=
  match eqDec sW (sg.addc 2) ts Γ with
  | some true => symPktFrom ts Γ sL sg [⟨.M, sg.addc 3⟩] (sg.addc 5)
  | some false =>
    match ltDec sW (YForm.const 3) ts Γ with
    | some false => some (.pkt sL (sW.addc (-3)) [⟨.M, sW.addc 1⟩] (sW.addc 3))
    | _ => none
  | none => none

theorem symGapNil_sound {y : List Int} (hy : inCone ts Γ y) {sL : List SMark} {msL : List Mark} {sg : YForm}
    {g : Nat} {sW : YForm} {Wn : Nat} {r : SGR} (hL : agL y sL msL) (hg : agN y sg g) (hW : agN y sW Wn)
    (h : symGapNil ts Γ sL sg sW = some r) : agGR y r (gapEvent msL g [] Wn) := by
  unfold symGapNil at h
  cases he : eqDec sW (sg.addc 2) ts Γ with
  | none => rw [he] at h; cases h
  | some b =>
    rw [he] at h
    have hb := eq_of_eqDec hy hW (agN_addc hg 2) he
    cases b with
    | true =>
      simp only at h
      simp only [gapEvent, if_pos (hb.mpr rfl)]
      exact symPktFrom_sound ts Γ hy hL hg (show agL y [⟨.M, sg.addc 3⟩] [⟨.M, g + 3⟩] from ⟨⟨rfl, agN_addc hg 3⟩, trivial⟩) (agN_addc hg 5) h
    | false =>
      simp only at h
      have hne : Wn ≠ g + 2 := fun h' => by simpa using hb.mp h'
      cases hl : ltDec sW (YForm.const 3) ts Γ with
      | none => rw [hl] at h; cases h
      | some c =>
        rw [hl] at h
        cases c with
        | true => cases h
        | false =>
          cases h
          have h3 := lt_of_ltDec hy hW (agN_const y 3) hl
          have h3n : ¬ Wn < 3 := fun h' => by simpa using h3.mp h'
          have h3' : 3 ≤ Wn := by omega
          simp only [gapEvent, if_neg hne, agGR]
          exact ⟨hL, by simpa using agN_subc hW 3 h3', ⟨⟨rfl, agN_addc hW 1⟩, trivial⟩, agN_addc hW 3⟩

/-- The gap meets a marker. -/
def symGapM (sL : List SMark) (sg : YForm) (mp : YForm) (sR' : List SMark) (sW : YForm) : Option SGR :=
  match ltDec mp (sg.addc 3) ts Γ with
  | some true => some .uncovered
  | some false =>
    let d := mp.sub (sg.addc 3)
    match d.modDec 2 with
    | some 1 => some .uncovered
    | some 0 =>
      match d.half? with
      | none => none
      | some hf =>
      match d.modDec 4 with
      | some 0 =>
        match eqDec d (YForm.const 0) ts Γ with
        | some false => some (.gap (⟨.M, (sg.add hf).addc (-1)⟩ :: sL) ((sg.add hf).addc 1) sR' sW)
        | some true =>
          match symWallFreeB ts Γ sg sL with
          | some false => some .uncovered
          | some true => some (.gap (⟨.M, (sg.add hf).addc (-1)⟩ :: sL) ((sg.add hf).addc 1) sR' sW)
          | none => none
        | none => none
      | some 2 =>
        match eqDec d (YForm.const 2) ts Γ with
        | some true => symPktFrom ts Γ sL sg (⟨.W, sg.addc 4⟩ :: sR') sW
        | some false => some (.pkt sL ((sg.add hf).addc (-2)) (⟨.W, (sg.add hf).addc 3⟩ :: sR') sW)
        | none => none
      | _ => none
    | _ => none
  | none => none

theorem symGapM_sound {y : List Int} (hy : inCone ts Γ y) {sL : List SMark} {msL : List Mark} {sg : YForm}
    {g : Nat} {mp : YForm} {p : Nat} {sR' : List SMark} {msR' : List Mark} {sW : YForm} {Wn : Nat} {r : SGR}
    (hL : agL y sL msL) (hg : agN y sg g) (hp : agN y mp p) (hR : agL y sR' msR') (hW : agN y sW Wn)
    (h : symGapM ts Γ sL sg mp sR' sW = some r) : agGR y r (gapEvent msL g (⟨.M, p⟩ :: msR') Wn) := by
  unfold symGapM at h
  cases hlt : ltDec mp (sg.addc 3) ts Γ with
  | none => rw [hlt] at h; cases h
  | some b =>
    rw [hlt] at h
    have hb := lt_of_ltDec hy hp (agN_addc hg 3) hlt
    cases b with
    | true => cases h; simp only [gapEvent, if_pos (hb.mpr rfl)]; trivial
    | false =>
      have hge : ¬ p < g + 3 := fun h' => by simpa using hb.mp h'
      simp only at h
      have hd : agN y (mp.sub (sg.addc 3)) (p - (g + 3)) := by
        unfold agN at hp hg ⊢; simp only [eval_sub, eval_addc]; omega
      simp only [gapEvent, if_neg hge]
      cases hm2 : (mp.sub (sg.addc 3)).modDec 2 with
      | none => rw [hm2] at h; cases h
      | some r2 =>
        rw [hm2] at h
        have e2 := mod_of_modDec hd hm2
        by_cases h1 : r2 = 1
        · subst h1; cases h; rw [if_pos (by omega)]; trivial
        by_cases h0 : r2 = 0
        · subst h0
          simp only at h
          rw [if_neg (by omega)]
          cases hh : (mp.sub (sg.addc 3)).half? with
          | none => rw [hh] at h; cases h
          | some hf =>
            rw [hh] at h
            simp only at h
            cases hm4 : (mp.sub (sg.addc 3)).modDec 4 with
            | none => rw [hm4] at h; cases h
            | some r4 =>
              have e4 := mod_of_modDec hd hm4
              have eh := half_of_half hd hh
              have hgd : agN y (sg.add hf) (g + (p - (g + 3)) / 2) := by
                unfold agN at hg ⊢; simp only [eval_add]; omega
              rw [hm4] at h
              by_cases h40 : r4 = 0
              · subst h40
                simp only at h
                rw [if_pos (by omega)]
                cases hz : eqDec (mp.sub (sg.addc 3)) (YForm.const 0) ts Γ with
                | none => rw [hz] at h; cases h
                | some z =>
                  rw [hz] at h
                  have hz' := eq_of_eqDec hy hd (agN_const y 0) hz
                  cases z with
                  | false =>
                    cases h
                    have hd0 : p - (g + 3) ≠ 0 := fun h' => by simpa using hz'.mp h'
                    rw [if_neg (fun h' => hd0 h'.1)]
                    refine ⟨⟨⟨rfl, ?_⟩, hL⟩, agN_addc hgd 1, hR, hW⟩
                    simpa using agN_subc hgd 1 (by omega)
                  | true =>
                    have hd0 : p - (g + 3) = 0 := hz'.mpr rfl
                    simp only at h
                    cases hwf : symWallFreeB ts Γ sg sL with
                    | none => rw [hwf] at h; cases h
                    | some c =>
                      rw [hwf] at h
                      have hc := symWallFreeB_sound ts Γ hy hg hL hwf
                      cases c with
                      | false => cases h; rw [if_pos ⟨hd0, hc⟩]; trivial
                      | true =>
                        cases h
                        rw [if_neg (fun h' => by rw [hc] at h'; exact absurd h'.2 (by decide))]
                        have hg1 := wallFreeB_pos hc
                        refine ⟨⟨⟨rfl, ?_⟩, hL⟩, agN_addc hgd 1, hR, hW⟩
                        simpa using agN_subc hgd 1 (by omega)
              by_cases h42 : r4 = 2
              · subst h42
                simp only at h
                rw [if_neg (by omega)]
                cases hz : eqDec (mp.sub (sg.addc 3)) (YForm.const 2) ts Γ with
                | none => rw [hz] at h; cases h
                | some z =>
                  rw [hz] at h
                  have hz' := eq_of_eqDec hy hd (agN_const y 2) hz
                  cases z with
                  | true =>
                    simp only at h
                    rw [if_pos (hz'.mpr rfl)]
                    exact symPktFrom_sound ts Γ hy hL hg (show agL y (⟨.W, sg.addc 4⟩ :: sR') (⟨.W, g + 4⟩ :: msR') from ⟨⟨rfl, agN_addc hg 4⟩, hR⟩) hW h
                  | false =>
                    cases h
                    have hd2 : p - (g + 3) ≠ 2 := fun h' => by simpa using hz'.mp h'
                    rw [if_neg hd2]
                    refine ⟨hL, ?_, ⟨⟨rfl, agN_addc hgd 3⟩, hR⟩, hW⟩
                    simpa using agN_subc hgd 2 (by omega)
              · exfalso; omega
        · exfalso; omega

end

section
variable (ts : List YForm) (Γ : Int)

/-- A packet starting three cells left of a wall at `mp` (guarded: `mp ≥ 3`). -/
def pktW (sL : List SMark) (mp : YForm) (sR : List SMark) (sW : YForm) : Option SGR :=
  match ltDec mp (YForm.const 3) ts Γ with
  | some false => some (.pkt sL (mp.addc (-3)) sR sW)
  | _ => none

theorem pktW_sound {y : List Int} (hy : inCone ts Γ y) {sL : List SMark} {msL : List Mark} {mp : YForm} {p : Nat}
    {sR : List SMark} {msR : List Mark} {sW : YForm} {Wn : Nat} {r : SGR} (hL : agL y sL msL) (hp : agN y mp p)
    (hR : agL y sR msR) (hW : agN y sW Wn) (h : pktW ts Γ sL mp sR sW = some r) :
    agGR y r (.pkt msL (p - 3) msR Wn) := by
  unfold pktW at h
  cases hl : ltDec mp (YForm.const 3) ts Γ with
  | none => rw [hl] at h; cases h
  | some c =>
    rw [hl] at h
    cases c with
    | true => cases h
    | false =>
      cases h
      have h3 := lt_of_ltDec hy hp (agN_const y 3) hl
      have h3n : ¬ p < 3 := fun h' => by simpa using h3.mp h'
      exact ⟨hL, by simpa using agN_subc hp 3 (by omega), hR, hW⟩

/-- Whether the block at `m2p` ends the tape: nothing after it, and `W = m2p + 3`. -/
def endCase (m2p sW : YForm) : List SMark → Option Bool
  | [] => eqDec sW (m2p.addc 3) ts Γ
  | _ :: _ => some false

theorem endCase_sound {y : List Int} (hy : inCone ts Γ y) {m2p sW : YForm} {p2 Wn : Nat} (hp : agN y m2p p2)
    (hW : agN y sW Wn) {sR : List SMark} {msR : List Mark} (hR : agL y sR msR) {r : Bool}
    (h : endCase ts Γ m2p sW sR = some r) : (msR.isEmpty = true ∧ Wn = p2 + 3) ↔ r = true := by
  cases sR with
  | nil =>
    cases msR with
    | cons _ _ => exact absurd hR id
    | nil =>
      have := eq_of_eqDec hy hW (agN_addc hp 3) h
      simp only [List.isEmpty_nil, true_and]; exact this
  | cons s sR =>
    cases msR with
    | nil => exact absurd hR id
    | cons m msR => simp only [endCase] at h; cases h; simp

/-- The gap meets a wall at `mp`. -/
def symGapW (sL : List SMark) (mp : YForm) (sR' : List SMark) (sW : YForm) : Option SGR :=
  match sR' with
  | [] => pktW ts Γ sL mp [⟨.M, sW⟩] (sW.addc 2)
  | m₂ :: sR'' =>
    match m₂.t with
    | .M =>
      match symFreeAtB ts Γ (m₂.p.addc 2) sW sR'' with
      | some true => some (.gap sL m₂.p sR'' sW)
      | some false => some .uncovered
      | none => none
    | .W =>
      match symStrictAfterB ts Γ (m₂.p.addc 2) sW sR'' with
      | some true => pktW ts Γ sL mp (⟨.B, m₂.p⟩ :: sR'') sW
      | some false => some .uncovered
      | none => none
    | .B =>
      match endCase ts Γ m₂.p sW sR'' with
      | some true => pktW ts Γ sL mp [] (m₂.p.addc 2)
      | some false =>
        match symStrictAfterB ts Γ (m₂.p.addc 3) sW sR'' with
        | some true => pktW ts Γ sL mp (⟨.W, m₂.p.addc 2⟩ :: sR'') sW
        | some false => some .uncovered
        | none => none
      | none => none
    | .G => some .uncovered

theorem symGapW_sound {y : List Int} (hy : inCone ts Γ y) {sL : List SMark} {msL : List Mark} {g : Nat}
    {mp : YForm} {p : Nat} {sR' : List SMark} {msR' : List Mark} {sW : YForm} {Wn : Nat} {r : SGR}
    (hL : agL y sL msL) (hp : agN y mp p) (hR : agL y sR' msR') (hW : agN y sW Wn)
    (h : symGapW ts Γ sL mp sR' sW = some r) : agGR y r (gapEvent msL g (⟨.W, p⟩ :: msR') Wn) := by
  cases sR' with
  | nil =>
    cases msR' with
    | cons _ _ => exact absurd hR id
    | nil =>
      simp only [symGapW] at h
      simp only [gapEvent]
      exact pktW_sound ts Γ hy hL hp (show agL y [⟨.M, sW⟩] [⟨.M, Wn⟩] from ⟨⟨rfl, hW⟩, trivial⟩) (agN_addc hW 2) h
  | cons s₂ sR'' =>
    cases msR' with
    | nil => exact absurd hR id
    | cons m₂ msR'' =>
      obtain ⟨⟨ht, hp2⟩, hR''⟩ := hR
      obtain ⟨t₂, p₂⟩ := m₂
      simp only at ht hp2
      subst ht
      cases hst : s₂.t with
      | M =>
        simp only [symGapW, hst] at h
        simp only [gapEvent, hst]
        cases hf : symFreeAtB ts Γ (s₂.p.addc 2) sW sR'' with
        | none => rw [hf] at h; cases h
        | some c =>
          rw [hf] at h
          have hc := symFreeAtB_sound ts Γ hy (agN_addc hp2 2) hW hR'' hf
          cases c with
          | true => cases h; rw [if_pos hc]; exact ⟨hL, hp2, hR'', hW⟩
          | false => cases h; rw [if_neg (by rw [hc]; decide)]; trivial
      | W =>
        simp only [symGapW, hst] at h
        simp only [gapEvent, hst]
        cases hf : symStrictAfterB ts Γ (s₂.p.addc 2) sW sR'' with
        | none => rw [hf] at h; cases h
        | some c =>
          rw [hf] at h
          have hc := symStrictAfterB_sound ts Γ hy (agN_addc hp2 2) hW hR'' hf
          cases c with
          | true =>
            rw [if_pos hc]
            exact pktW_sound ts Γ hy hL hp (show agL y (⟨.B, s₂.p⟩ :: sR'') (⟨.B, p₂⟩ :: msR'') from ⟨⟨rfl, hp2⟩, hR''⟩) hW h
          | false => cases h; rw [if_neg (by rw [hc]; decide)]; trivial
      | B =>
        simp only [symGapW, hst] at h
        simp only [gapEvent, hst]
        cases he : endCase ts Γ s₂.p sW sR'' with
        | none => rw [he] at h; cases h
        | some e =>
          rw [he] at h
          have hec := endCase_sound ts Γ hy hp2 hW hR'' he
          cases e with
          | true =>
            rw [if_pos (hec.mpr rfl)]
            exact pktW_sound ts Γ hy hL hp (show agL y [] [] from trivial) (agN_addc hp2 2) h
          | false =>
            rw [if_neg (fun h' => by simpa using hec.mp h')]
            simp only at h
            cases hf : symStrictAfterB ts Γ (s₂.p.addc 3) sW sR'' with
            | none => rw [hf] at h; cases h
            | some c =>
              rw [hf] at h
              have hc := symStrictAfterB_sound ts Γ hy (agN_addc hp2 3) hW hR'' hf
              cases c with
              | true =>
                rw [if_pos hc]
                exact pktW_sound ts Γ hy hL hp (show agL y (⟨.W, s₂.p.addc 2⟩ :: sR'') (⟨.W, p₂ + 2⟩ :: msR'') from ⟨⟨rfl, agN_addc hp2 2⟩, hR''⟩) hW h
              | false => cases h; rw [if_neg (by rw [hc]; decide)]; trivial
      | G =>
        simp only [symGapW, hst] at h; cases h
        simp only [gapEvent, hst]; trivial

/-- The gap meets a block at `mp`. -/
def symGapB (sL : List SMark) (sg mp : YForm) (sR' : List SMark) (sW : YForm) : Option SGR :=
  match ltDec mp (sg.addc 5) ts Γ with
  | some true => some .uncovered
  | some false =>
    match sR' with
    | [] => some (.gap (⟨.M, mp.addc (-2)⟩ :: ⟨.G, sg⟩ :: sL) mp [⟨.M, sW⟩] (sW.addc 2))
    | m₂ :: sR'' =>
      match m₂.t with
      | .M =>
        match symFreeAtB ts Γ (m₂.p.addc 2) sW sR'' with
        | some true => some (.gap (⟨.W, mp.addc (-1)⟩ :: ⟨.G, sg⟩ :: sL) m₂.p sR'' sW)
        | some false => some .uncovered
        | none => none
      | .W =>
        match symStrictAfterB ts Γ (m₂.p.addc 2) sW sR'' with
        | some true => some (.gap (⟨.M, mp.addc (-2)⟩ :: ⟨.G, sg⟩ :: sL) mp (⟨.B, m₂.p⟩ :: sR'') sW)
        | some false => some .uncovered
        | none => none
      | .B =>
        match endCase ts Γ m₂.p sW sR'' with
        | some true => some (.gap (⟨.M, mp.addc (-2)⟩ :: ⟨.G, sg⟩ :: sL) mp [] (m₂.p.addc 2))
        | some false =>
          match symStrictAfterB ts Γ (m₂.p.addc 3) sW sR'' with
          | some true => some (.gap (⟨.M, mp.addc (-2)⟩ :: ⟨.G, sg⟩ :: sL) mp (⟨.W, m₂.p.addc 2⟩ :: sR'') sW)
          | some false => some .uncovered
          | none => none
        | none => none
      | .G => some .uncovered
  | none => none

theorem symGapB_sound {y : List Int} (hy : inCone ts Γ y) {sL : List SMark} {msL : List Mark} {sg : YForm} {g : Nat}
    {mp : YForm} {p : Nat} {sR' : List SMark} {msR' : List Mark} {sW : YForm} {Wn : Nat} {r : SGR}
    (hL : agL y sL msL) (hg : agN y sg g) (hp : agN y mp p) (hR : agL y sR' msR') (hW : agN y sW Wn)
    (h : symGapB ts Γ sL sg mp sR' sW = some r) : agGR y r (gapEvent msL g (⟨.B, p⟩ :: msR') Wn) := by
  unfold symGapB at h
  cases hlt : ltDec mp (sg.addc 5) ts Γ with
  | none => rw [hlt] at h; cases h
  | some b =>
    rw [hlt] at h
    have hb := lt_of_ltDec hy hp (agN_addc hg 5) hlt
    cases b with
    | true => cases h; simp only [gapEvent, if_pos (hb.mpr rfl)]; trivial
    | false =>
      have hge : ¬ p < g + 5 := fun h' => by simpa using hb.mp h'
      simp only at h
      simp only [gapEvent, if_neg hge]
      have hM2 : agN y (mp.addc (-2)) (p - 2) := by simpa using agN_subc hp 2 (by omega)
      have hM1 : agN y (mp.addc (-1)) (p - 1) := by simpa using agN_subc hp 1 (by omega)
      cases sR' with
      | nil =>
        cases msR' with
        | cons _ _ => exact absurd hR id
        | nil =>
          cases h
          exact ⟨⟨⟨rfl, hM2⟩, ⟨rfl, hg⟩, hL⟩, hp, ⟨⟨rfl, hW⟩, trivial⟩, agN_addc hW 2⟩
      | cons s₂ sR'' =>
        cases msR' with
        | nil => exact absurd hR id
        | cons m₂ msR'' =>
          obtain ⟨⟨ht, hp2⟩, hR''⟩ := hR
          obtain ⟨t₂, p₂⟩ := m₂
          simp only at ht hp2
          subst ht
          cases hst : s₂.t with
          | M =>
            simp only [hst] at h
            simp only [hst]
            cases hf : symFreeAtB ts Γ (s₂.p.addc 2) sW sR'' with
            | none => rw [hf] at h; cases h
            | some c =>
              rw [hf] at h
              have hc := symFreeAtB_sound ts Γ hy (agN_addc hp2 2) hW hR'' hf
              cases c with
              | true => cases h; rw [if_pos hc]; exact ⟨⟨⟨rfl, hM1⟩, ⟨rfl, hg⟩, hL⟩, hp2, hR'', hW⟩
              | false => cases h; rw [if_neg (by rw [hc]; decide)]; trivial
          | W =>
            simp only [hst] at h
            simp only [hst]
            cases hf : symStrictAfterB ts Γ (s₂.p.addc 2) sW sR'' with
            | none => rw [hf] at h; cases h
            | some c =>
              rw [hf] at h
              have hc := symStrictAfterB_sound ts Γ hy (agN_addc hp2 2) hW hR'' hf
              cases c with
              | true => cases h; rw [if_pos hc]; exact ⟨⟨⟨rfl, hM2⟩, ⟨rfl, hg⟩, hL⟩, hp, ⟨⟨rfl, hp2⟩, hR''⟩, hW⟩
              | false => cases h; rw [if_neg (by rw [hc]; decide)]; trivial
          | B =>
            simp only [hst] at h
            simp only [hst]
            cases he : endCase ts Γ s₂.p sW sR'' with
            | none => rw [he] at h; cases h
            | some e =>
              rw [he] at h
              have hec := endCase_sound ts Γ hy hp2 hW hR'' he
              cases e with
              | true =>
                cases h; rw [if_pos (hec.mpr rfl)]
                exact ⟨⟨⟨rfl, hM2⟩, ⟨rfl, hg⟩, hL⟩, hp, trivial, agN_addc hp2 2⟩
              | false =>
                rw [if_neg (fun h' => by simpa using hec.mp h')]
                simp only at h
                cases hf : symStrictAfterB ts Γ (s₂.p.addc 3) sW sR'' with
                | none => rw [hf] at h; cases h
                | some c =>
                  rw [hf] at h
                  have hc := symStrictAfterB_sound ts Γ hy (agN_addc hp2 3) hW hR'' hf
                  cases c with
                  | true =>
                    cases h; rw [if_pos hc]
                    exact ⟨⟨⟨rfl, hM2⟩, ⟨rfl, hg⟩, hL⟩, hp, ⟨⟨rfl, agN_addc hp2 2⟩, hR''⟩, hW⟩
                  | false => cases h; rw [if_neg (by rw [hc]; decide)]; trivial
          | G => simp only [hst] at h; cases h; simp only [hst]; trivial

/-- One event of the gap phase, on symbolic positions. -/
def symGapEvent (sL : List SMark) (sg : YForm) (sR : List SMark) (sW : YForm) : Option SGR :=
  match sR with
  | [] => symGapNil ts Γ sL sg sW
  | m :: sR' =>
    match m.t with
    | .M => symGapM ts Γ sL sg m.p sR' sW
    | .W => symGapW ts Γ sL m.p sR' sW
    | .B => symGapB ts Γ sL sg m.p sR' sW
    | .G => some .uncovered

theorem symGapEvent_sound {y : List Int} (hy : inCone ts Γ y) {sL : List SMark} {msL : List Mark} {sg : YForm}
    {g : Nat} {sR : List SMark} {msR : List Mark} {sW : YForm} {Wn : Nat} {r : SGR} (hL : agL y sL msL)
    (hg : agN y sg g) (hR : agL y sR msR) (hW : agN y sW Wn) (h : symGapEvent ts Γ sL sg sR sW = some r) :
    agGR y r (gapEvent msL g msR Wn) := by
  cases sR with
  | nil =>
    cases msR with
    | cons _ _ => exact absurd hR id
    | nil => exact symGapNil_sound ts Γ hy hL hg hW h
  | cons s sR' =>
    cases msR with
    | nil => exact absurd hR id
    | cons m msR' =>
      obtain ⟨⟨ht, hp⟩, hR'⟩ := hR
      obtain ⟨t, p⟩ := m
      simp only at ht hp
      subst ht
      cases hst : s.t with
      | M => simp only [symGapEvent, hst] at h; exact symGapM_sound ts Γ hy hL hg hp hR' hW h
      | W => simp only [symGapEvent, hst] at h; exact symGapW_sound ts Γ hy hL hp hR' hW h
      | B => simp only [symGapEvent, hst] at h; exact symGapB_sound ts Γ hy hL hg hp hR' hW h
      | G => simp only [symGapEvent, hst] at h; cases h; simp only [gapEvent]; trivial

end

section
variable (ts : List YForm) (Γ : Int)

def SPR.cont (k : List SMark → YForm → List SMark → YForm → Option SPR) : SPR → Option SPR
  | .gap sL g sR W => k sL g sR W
  | r => some r

/-- The round on symbolic positions. -/
def symRoundZ : Nat → List SMark → YForm → List SMark → YForm → Option SPR
  | 0, _, _, _, _ => some .uncovered
  | fuel + 1, sL, sg, sR, sW =>
    match symGapEvent ts Γ sL sg sR sW with
    | none => none
    | some (.gap sL' sg' sR' sW') => symRoundZ fuel sL' sg' sR' sW'
    | some (.pkt sL' sx sR' sW') =>
      match symPktBack ts Γ sL' sx sR' sW' with
      | none => none
      | some r => r.cont (symRoundZ fuel)
    | some (.pktM sL' sx sR' sW') =>
      match symPktLand ts Γ sL' sx sR' sW' with
      | none => none
      | some r => r.cont (symRoundZ fuel)
    | some .halt => some .halt
    | some .uncovered => some .uncovered

theorem cont_sound {y : List Int} {k : List SMark → YForm → List SMark → YForm → Option SPR}
    {kc : List Mark → Nat → List Mark → Nat → PR'}
    (hk : ∀ sL msL sg g sR msR sW W r, agL y sL msL → agN y sg g → agL y sR msR → agN y sW W → k sL sg sR sW = some r →
      agPR y r (kc msL g msR W))
    {sr : SPR} {cr : PR'} (hr : agPR y sr cr) {r : SPR} (h : sr.cont k = some r) : agPR y r (cr.cont kc) := by
  cases sr with
  | gap sL sg sR sW =>
    cases cr with
    | gap msL g msR W => exact hk _ _ _ _ _ _ _ _ _ hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 h
    | _ => exact absurd hr id
  | newRound ss sW => cases cr with
    | newRound ms W => cases h; exact hr
    | _ => exact absurd hr id
  | halt => cases cr with
    | halt => cases h; exact hr
    | _ => exact absurd hr id
  | uncovered => cases cr with
    | uncovered => cases h; exact hr
    | _ => exact absurd hr id

theorem symRoundZ_sound {y : List Int} (hy : inCone ts Γ y) (fuel : Nat) :
    ∀ sL msL sg g sR msR sW W r, agL y sL msL → agN y sg g → agL y sR msR → agN y sW W →
      symRoundZ ts Γ fuel sL sg sR sW = some r → agPR y r (roundZ fuel msL g msR W) := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ r _ _ _ _ h; cases h; trivial
  | succ fuel ih =>
    intro sL msL sg g sR msR sW W r hL hg hR hW h
    simp only [symRoundZ] at h
    simp only [roundZ]
    cases he : symGapEvent ts Γ sL sg sR sW with
    | none => rw [he] at h; cases h
    | some ev =>
      rw [he] at h
      have hag := symGapEvent_sound ts Γ hy hL hg hR hW he
      cases ev with
      | gap sL' sg' sR' sW' =>
        simp only at h
        generalize gapEvent msL g msR W = cev at hag ⊢
        cases cev with
        | gap msL' g' msR' W' => exact ih _ _ _ _ _ _ _ _ _ hag.1 hag.2.1 hag.2.2.1 hag.2.2.2 h
        | _ => exact absurd hag id
      | pkt sL' sx sR' sW' =>
        simp only at h
        generalize gapEvent msL g msR W = cev at hag ⊢
        cases cev with
        | pkt msL' x msR' W' =>
          cases hb : symPktBack ts Γ sL' sx sR' sW' with
          | none => rw [hb] at h; cases h
          | some pr =>
            rw [hb] at h
            have hpr := symPktBack_sound ts Γ hy sL' msL' sx x sR' msR' sW' W' pr hag.1 hag.2.2.1 hag.2.2.2 hb
            exact cont_sound (fun _ _ _ _ _ _ _ _ _ a b c d e => ih _ _ _ _ _ _ _ _ _ a b c d e) hpr h
        | _ => exact absurd hag id
      | pktM sL' sx sR' sW' =>
        simp only at h
        generalize gapEvent msL g msR W = cev at hag ⊢
        cases cev with
        | pktM msL' x msR' W' =>
          cases hb : symPktLand ts Γ sL' sx sR' sW' with
          | none => rw [hb] at h; cases h
          | some pr =>
            rw [hb] at h
            have hpr := symPktLand_sound ts Γ hy sL' msL' sx x sR' msR' sW' W' pr hag.1 hag.2.1 hag.2.2.1 hag.2.2.2 hb
            exact cont_sound (fun _ _ _ _ _ _ _ _ _ a b c d e => ih _ _ _ _ _ _ _ _ _ a b c d e) hpr h
        | _ => exact absurd hag id
      | halt =>
        simp only at h; cases h
        generalize gapEvent msL g msR W = cev at hag ⊢
        cases cev with
        | halt => trivial
        | _ => exact absurd hag id
      | uncovered =>
        simp only at h; cases h
        generalize gapEvent msL g msR W = cev at hag ⊢
        cases cev with
        | uncovered => trivial
        | _ => exact absurd hag id

/-- Several rounds from a round start (the gap at 1), on symbolic positions. -/
def symRoundsZ (fuel : Nat) : Nat → List SMark → YForm → Option SPR
  | 0, ss, sW => some (.newRound ss sW)
  | n + 1, ss, sW =>
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => symRoundsZ fuel n ss' sW'
    | r => r

theorem symRoundsZ_sound {y : List Int} (hy : inCone ts Γ y) (fuel n : Nat) :
    ∀ ss ms sW W r, agL y ss ms → agN y sW W → symRoundsZ ts Γ fuel n ss sW = some r → agPR y r (roundsZ fuel n ms W) := by
  induction n with
  | zero => intro ss ms sW W r hs hW h; cases h; exact ⟨hs, hW⟩
  | succ n ih =>
    intro ss ms sW W r hs hW h
    simp only [symRoundsZ] at h
    simp only [roundsZ]
    cases hr : symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | none => rw [hr] at h; cases h
    | some sr =>
      rw [hr] at h
      have hag := symRoundZ_sound ts Γ hy fuel [] [] (YForm.const 1) 1 ss ms sW W sr trivial (agN_const y 1) hs hW hr
      generalize roundZ fuel [] 1 ms W = cr at hag ⊢
      cases sr with
      | newRound ss' sW' =>
        cases cr with
        | newRound ms' W' => exact ih _ _ _ _ _ hag.1 hag.2 h
        | _ => exact absurd hag id
      | gap _ _ _ _ => cases cr with
        | gap _ _ _ _ => cases h; exact hag
        | _ => exact absurd hag id
      | halt => cases cr with
        | halt => cases h; exact hag
        | _ => exact absurd hag id
      | uncovered => cases cr with
        | uncovered => cases h; exact hag
        | _ => exact absurd hag id

end

section
variable (ts : List YForm) (Γ : Int)

/-! ## Well-formedness of a symbolic round start, and the leaf theorem -/

def parityOf (b : Bool) : Int := if b then 1 else 0

/-- `rightOK` decided on the cone and by residues. -/
def symRightOK (q : YForm) (u : Bool) (W : YForm) : List SMark → Bool
  | [] => ltDec W q ts Γ == some false && (W.sub q).modDec 2 == some (parityOf (u == false))
  | s :: ss => ltDec s.p q ts Γ == some false && (s.p.sub q).modDec 2 == some (parityOf (u == mval s.t)) &&
      symRightOK (s.p.addc (mlen s.t)) (mval s.t) W ss

theorem symRightOK_sound {y : List Int} (hy : inCone ts Γ y) (ss : List SMark) :
    ∀ (q : YForm) (qn : Nat) (u : Bool) (W : YForm) (Wn : Nat) (ms : List Mark), agN y q qn → agN y W Wn →
      agL y ss ms → symRightOK ts Γ q u W ss = true → rightOK qn u Wn ms := by
  induction ss with
  | nil =>
    intro q qn u W Wn ms hq hW hs h
    cases ms with
    | cons _ _ => exact absurd hs id
    | nil =>
      simp only [symRightOK, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨h1, h2⟩ := h
      have hl := lt_of_ltDec hy hW hq h1
      have hd : agN y (W.sub q) (Wn - qn) := by
        have : ¬ Wn < qn := fun h' => by simpa using hl.mp h'
        unfold agN at hq hW ⊢; simp only [eval_sub]; omega
      have hm := mod_of_modDec hd h2
      have hnl : ¬ Wn < qn := fun h' => by simpa using hl.mp h'
      refine ⟨by omega, ?_⟩
      cases u <;> simp [parityOf] at hm ⊢ <;> omega
  | cons s ss ih =>
    intro q qn u W Wn ms hq hW hs h
    cases ms with
    | nil => exact absurd hs id
    | cons m ms =>
      obtain ⟨⟨ht, hp⟩, hs'⟩ := hs
      simp only [symRightOK, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have hl := lt_of_ltDec hy hp hq h1
      have hge : ¬ m.p < qn := fun h' => by simpa using hl.mp h'
      have hd : agN y (s.p.sub q) (m.p - qn) := by unfold agN at hq hp ⊢; simp only [eval_sub]; omega
      have hm := mod_of_modDec hd h2
      refine ⟨by omega, ?_, ?_⟩
      · rw [← ht]
        generalize mval s.t = v at hm ⊢
        cases u <;> cases v <;> simp [parityOf] at hm ⊢ <;> omega
      · rw [← ht]; exact ih _ _ _ _ _ _ (by rw [ht]; exact agN_addc hp _) hW hs' h3

/-- **A checked leaf, for the machine.**  If the symbolic run of `n` rounds from a round start decides every test
and ends at a round start, and the start is well formed on the cone, then at every point of the cone the machine,
started from the round start the leaf describes, reaches the round start the symbolic run computes — in particular
it does not halt on the way. -/
theorem leaf_run (fuel n : Nat) (ss : List SMark) (sW : YForm) (ss' : List SMark) (sW' : YForm)
    (hrun : symRoundsZ ts Γ fuel n ss sW = some (.newRound ss' sW'))
    (hwf : symRightOK ts Γ (YForm.const 4) false sW ss = true)
    (y : List Int) (hy : inCone ts Γ y) (ms : List Mark) (Wn : Nat) (hs : agL y ss ms) (hW : agN y sW Wn) :
    ∃ k ms' Wn', steps k (roundStart ms Wn) = some (roundStart ms' Wn') ∧ agL y ss' ms' ∧ agN y sW' Wn' := by
  have hag := symRoundsZ_sound ts Γ hy fuel n ss ms sW Wn _ hs hW hrun
  have hrwf : roundWF ms Wn := symRightOK_sound ts Γ hy ss _ 4 false sW Wn ms (agN_const y 4) hW hs hwf
  generalize hr : roundsZ fuel n ms Wn = cr at hag
  cases cr with
  | newRound ms' Wn' =>
    obtain ⟨k, hk, -⟩ := rounds_run fuel n ms Wn hrwf (by rw [hr]; intro h; cases h)
    rw [hr] at hk
    exact ⟨k, ms', Wn', hk, hag.1, hag.2⟩
  | _ => exact absurd hag id

end

end BB6.Sym
