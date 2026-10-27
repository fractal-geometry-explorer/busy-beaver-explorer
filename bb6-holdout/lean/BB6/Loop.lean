import BB6.Meets

/-!
# The loop's passes, with the right end free

A *phase-0 pass start* is a round start with three walls, `G 1, W a, W b, W c`, width `E`, a odd, b even, E even
(`isP0`); its right end is `R = E − c − 1` and its left countdown `L₁ = 147 b + 280 E − 392 c − 578`.  `Tree.okLoop`
checks a tree of splits as `Tree.okNC` does (no halt, no end meeting at distance ≤ 2) and in addition classifies the
round start each leaf ends at: either it is decidedly *not* a phase-0 pass start (`notP0Check`), or it is one whose
gaps are again at least 448 and whose right end is smaller (`passCheck`: 176 < R′ < R, R′ even, and R′ = R/16 with
L₁′ = L₁/64, or R′ = R/2).  `Tree.soundLoop` is the statement for the machine; the induction over passes that it
makes possible is in `thm/LoopTheorem.lean`.
-/

namespace BB6
open BB6

/-- The three positions of a round start with exactly three walls. -/
def wwwOf : List Mark → Option (Nat × Nat × Nat)
  | [m1, m2, m3] => if m1.t = .W ∧ m2.t = .W ∧ m3.t = .W then some (m1.p, m2.p, m3.p) else none
  | _ => none

/-- A phase-0 pass start: walls at a, b, c, width W, with a odd, b even, W even. -/
def isP0 (ms : List Mark) (W : Nat) : Prop :=
  ∃ a b c, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] ∧ a % 2 = 1 ∧ b % 2 = 0 ∧ W % 2 = 0

/-- The left countdown of a pass start (walls b, c, width E). -/
def loopL1 (b c E : Nat) : Int := 147 * (b : Int) + 280 * (E : Int) - 392 * (c : Int) - 578

/-- What a leaf of the loop tree ends at, from a pass start with right end `R` and left countdown `L`: a round start
that is not a phase-0 pass start, or a phase-0 pass start with gaps ≥ 448 and a smaller even right end R′ > 176,
with R′ = R/16 and L₁′ = L/64 (a full pass) or R′ = R/2. -/
def LoopOut (R : Nat) (L : Int) (ms : List Mark) (W : Nat) : Prop :=
  ¬ isP0 ms W ∨
  ∃ a b R', ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R' - 1⟩] ∧ a % 2 = 1 ∧ b % 2 = 0 ∧ W % 2 = 0 ∧ R' % 2 = 0 ∧
    448 ≤ a ∧ a + 448 ≤ b ∧ b + 448 + R' + 1 ≤ W ∧ 176 < R' ∧ R' < R ∧
    ((16 * R' = R ∧ 64 * loopL1 b (W - R' - 1) W = L) ∨ 2 * R' = R)

end BB6

namespace BB6.Sym
open BB6

def swwwOf : List SMark → Option (YForm × YForm × YForm)
  | [m1, m2, m3] => if m1.t = .W ∧ m2.t = .W ∧ m3.t = .W then some (m1.p, m2.p, m3.p) else none
  | _ => none

theorem agL_length {y : List Int} : ∀ {ss : List SMark} {ms : List Mark}, agL y ss ms → ss.length = ms.length
  | [], [], _ => rfl
  | _ :: ss, _ :: ms, h => by simp [agL_length (ss := ss) (ms := ms) h.2]
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id

theorem len3 {α : Type} : ∀ {l : List α}, l.length = 3 → ∃ a b c, l = [a, b, c]
  | [a, b, c], _ => ⟨a, b, c, rfl⟩
  | [], h | [_], h | [_, _], h | _ :: _ :: _ :: _ :: _, h => by simp at h

theorem wwwOf_ne3 : ∀ {ms : List Mark}, ms.length ≠ 3 → wwwOf ms = none
  | [_, _, _], h => by simp at h
  | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _ :: _, _ => rfl

theorem swwwOf_ne3 : ∀ {ss : List SMark}, ss.length ≠ 3 → swwwOf ss = none
  | [_, _, _], h => by simp at h
  | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _ :: _, _ => rfl

theorem wwwOf_agree {y : List Int} {ss : List SMark} {ms : List Mark} (h : agL y ss ms) :
    (swwwOf ss = none → wwwOf ms = none) ∧
    (∀ fa fb fc, swwwOf ss = some (fa, fb, fc) →
      ∃ a b c, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] ∧ agN y fa a ∧ agN y fb b ∧ agN y fc c) := by
  have hl := agL_length h
  by_cases h3 : ms.length = 3
  · obtain ⟨m1, m2, m3, rfl⟩ := len3 h3
    obtain ⟨s1, s2, s3, rfl⟩ := len3 (hl.trans h3)
    obtain ⟨⟨h1t, h1p⟩, ⟨h2t, h2p⟩, ⟨h3t, h3p⟩, -⟩ := h
    obtain ⟨t1, p1⟩ := m1
    obtain ⟨t2, p2⟩ := m2
    obtain ⟨t3, p3⟩ := m3
    obtain ⟨u1, q1⟩ := s1
    obtain ⟨u2, q2⟩ := s2
    obtain ⟨u3, q3⟩ := s3
    simp only at h1t h2t h3t h1p h2p h3p
    subst h1t h2t h3t
    refine ⟨fun hn => ?_, fun fa fb fc hs => ?_⟩
    · simp only [swwwOf] at hn
      simp only [wwwOf]
      split at hn
      · cases hn
      · rename_i hc; simp only [hc, ite_false]
    · simp only [swwwOf] at hs
      split at hs
      · rename_i hc
        obtain ⟨e1, e2, e3⟩ := hc
        cases hs
        subst e1 e2 e3
        exact ⟨p1, p2, p3, rfl, h1p, h2p, h3p⟩
      · cases hs
  · refine ⟨fun _ => wwwOf_ne3 h3, fun fa fb fc hs => ?_⟩
    rw [swwwOf_ne3 (by omega)] at hs
    cases hs

section
variable (ts : List YForm) (Γ : Int)

def sameForm (f g : YForm) : Bool := f.k == g.k && coeffEq f.c g.c

theorem sameForm_sound {f g : YForm} (h : sameForm f g = true) (y : List Int) : f.eval y = g.eval y := by
  simp only [sameForm, Bool.and_eq_true, beq_iff_eq] at h
  simp only [YForm.eval, h.1, dot_coeffEq _ _ y h.2]

def L1Form (b c E : YForm) : YForm := (((b.smul 147).add (E.smul 280)).sub (c.smul 392)).addc (-578)

theorem eval_L1Form (b c E : YForm) (y : List Int) :
    (L1Form b c E).eval y = 147 * b.eval y + 280 * E.eval y - 392 * c.eval y - 578 := by
  simp only [L1Form, eval_addc, eval_sub, eval_add, eval_smul]; omega

/-- The end of a leaf is decidedly not a phase-0 pass start. -/
def notP0Check (ss : List SMark) (sW : YForm) : Bool :=
  match swwwOf ss with
  | none => true
  | some (a, b, _) => a.modDec 2 == some 0 || b.modDec 2 == some 1 || sW.modDec 2 == some 1

/-- The end of a leaf is a phase-0 pass start with gaps ≥ 448 and a smaller right end (`sR`, `sL`: the right end
and the left countdown of the leaf's start). -/
def passCheck (sR sL : YForm) (ss : List SMark) (sW : YForm) : Bool :=
  match swwwOf ss with
  | none => false
  | some (a, b, c) =>
    let R' := (sW.sub c).addc (-1)
    a.modDec 2 == some 1 && b.modDec 2 == some 0 && sW.modDec 2 == some 0 && R'.modDec 2 == some 0 &&
    ltDec (YForm.const 447) a ts Γ == some true && ltDec (a.addc 447) b ts Γ == some true &&
    ltDec (b.addc 447) c ts Γ == some true && ltDec (YForm.const 176) R' ts Γ == some true &&
    ltDec R' sR ts Γ == some true &&
    ((sameForm (R'.smul 16) sR && sameForm ((L1Form b c sW).smul 64) sL) || sameForm (R'.smul 2) sR)

theorem modDec_nat {y : List Int} {f : YForm} {n : Nat} (h : agN y f n) {m : Nat} {r : Int}
    (hm : f.modDec m = some r) : ((n % m : Nat) : Int) = r := by
  have := eval_mod f m r hm y
  unfold agN at h
  rw [← h] at this
  omega

theorem lt_true {y : List Int} (hy : inCone ts Γ y) {a b : YForm} {n m : Nat} (ha : agN y a n) (hb : agN y b m)
    (h : ltDec a b ts Γ = some true) : n < m := by
  have := ltDec_sound a b ts Γ y hy true h
  unfold agN at ha hb
  have h2 := this.mpr rfl
  omega

theorem notP0Check_sound {y : List Int} {ss : List SMark} {sW : YForm} {ms : List Mark} {W : Nat}
    (hs : agL y ss ms) (hW : agN y sW W) (h : notP0Check ss sW = true) : ¬ isP0 ms W := by
  rintro ⟨a, b, c, rfl, ha, hb, hWp⟩
  have hag := wwwOf_agree hs
  unfold notP0Check at h
  cases hsw : swwwOf ss with
  | none => have := hag.1 hsw; simp [wwwOf] at this
  | some f =>
    obtain ⟨fa, fb, fc⟩ := f
    rw [hsw] at h
    obtain ⟨a', b', c', he, h1, h2, -⟩ := hag.2 fa fb fc hsw
    simp only [List.cons.injEq, Mark.mk.injEq, and_true, true_and] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (h | h) | h
    · have := modDec_nat h1 (m := 2) h; omega
    · have := modDec_nat h2 (m := 2) h; omega
    · have := modDec_nat hW (m := 2) h; omega

theorem passCheck_sound {y : List Int} (hy : inCone ts Γ y) {sR sL : YForm} {R : Nat} {L : Int}
    (hR : agN y sR R) (hL : L = sL.eval y) {ss : List SMark} {sW : YForm} {ms : List Mark} {W : Nat}
    (hs : agL y ss ms) (hW : agN y sW W) (h : passCheck ts Γ sR sL ss sW = true) : LoopOut R L ms W := by
  right
  have hag := wwwOf_agree hs
  unfold passCheck at h
  cases hsw : swwwOf ss with
  | none => rw [hsw] at h; cases h
  | some f =>
    obtain ⟨fa, fb, fc⟩ := f
    rw [hsw] at h
    obtain ⟨a, b, c, rfl, h1, h2, h3⟩ := hag.2 fa fb fc hsw
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨pa, pb⟩, pW⟩, pR⟩, ga⟩, gb⟩, gc⟩, g176⟩, gR⟩, hmap⟩ := h
    have ma := modDec_nat h1 (m := 2) pa
    have mb := modDec_nat h2 (m := 2) pb
    have mW := modDec_nat hW (m := 2) pW
    have la := lt_true ts Γ hy (agN_const y 447) h1 ga
    have lb := lt_true ts Γ hy (agN_addc h1 447) h2 gb
    have lc := lt_true ts Γ hy (agN_addc h2 447) h3 gc
    -- the new right end
    have hcW : c + 1 ≤ W := by
      have := lt_true ts Γ hy (agN_const y 176) (n := 176) (m := W - c - 1) (b := (sW.sub fc).addc (-1)) ?_ g176
      · omega
      · have : ¬ W < c + 1 := by
          intro hlt
          have h0 := ltDec_sound (YForm.const 176) ((sW.sub fc).addc (-1)) ts Γ y hy true g176
          have h0' := h0.mpr rfl
          unfold agN at hW h3
          simp only [eval_const, eval_addc, eval_sub] at h0'
          omega
        unfold agN at hW h3 ⊢
        simp only [eval_addc, eval_sub]
        omega
    have hR' : agN y ((sW.sub fc).addc (-1)) (W - c - 1) := by
      unfold agN at hW h3 ⊢; simp only [eval_addc, eval_sub]; omega
    have mR := modDec_nat hR' (m := 2) pR
    have l176 := lt_true ts Γ hy (agN_const y 176) hR' g176
    have lR := lt_true ts Γ hy hR' hR gR
    refine ⟨a, b, W - c - 1, ?_, by omega, by omega, by omega, by omega, by omega, by omega, by omega, l176, lR, ?_⟩
    · have : W - (W - c - 1) - 1 = c := by omega
      rw [this]
    · have e : W - (W - c - 1) - 1 = c := by omega
      rw [e]
      rcases hmap with ⟨e16, e64⟩ | e2
      · left
        have q1 := sameForm_sound e16 y
        have q2 := sameForm_sound e64 y
        simp only [eval_smul, eval_L1Form] at q1 q2
        unfold agN at hR hR' h2 h3 hW
        rw [← hR', ← hR] at q1
        refine ⟨by omega, ?_⟩
        rw [hL, ← q2, ← h2, ← h3, ← hW]
        simp only [loopL1]
      · right
        have q := sameForm_sound e2 y
        simp only [eval_smul] at q
        unfold agN at hR hR'
        rw [← hR', ← hR] at q
        omega

/-- The leaf's end, classified. -/
def endCheck (sR sL : YForm) (ss : List SMark) (sW : YForm) : Bool :=
  notP0Check ss sW || passCheck ts Γ sR sL ss sW

theorem endCheck_sound {y : List Int} (hy : inCone ts Γ y) {sR sL : YForm} {R : Nat} {L : Int}
    (hR : agN y sR R) (hL : L = sL.eval y) {ss : List SMark} {sW : YForm} {ms : List Mark} {W : Nat}
    (hs : agL y ss ms) (hW : agN y sW W) (h : endCheck ts Γ sR sL ss sW = true) : LoopOut R L ms W := by
  unfold endCheck at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (notP0Check_sound hs hW h)
  · exact passCheck_sound ts Γ hy hR hL hs hW h

end

/-! ## Trees that classify where each leaf ends -/

variable (Γ : Int) (fuel : Nat)

/-- As `Tree.okNC`, and each leaf's end passes `endCheck` (`sR`, `sL`: the root's right end and left countdown,
substituted along with the start). -/
def Tree.okLoop (k : Nat) : Tree → Bool → List SMark → YForm → List YForm → YForm → YForm → Bool
  | .leaf n, wf, ss, sW, ts, sR, sL =>
    (wf || symRightOK ts Γ (YForm.const 4) false sW ss) &&
    (match symRoundsZ ts Γ fuel n ss sW with
     | some (.newRound ss' sW') => endCheck ts Γ sR sL ss' sW'
     | _ => false) &&
    (match symMeetsRounds ts Γ fuel n ss sW with
     | some ds => allGe3 ts Γ ds
     | none => false)
  | .adv n t, wf, ss, sW, ts, sR, sL =>
    (wf || symRightOK ts Γ (YForm.const 4) false sW ss) &&
    (match symMeetsRounds ts Γ fuel n ss sW with
     | some ds => allGe3 ts Γ ds
     | none => false) &&
    (match symRoundsZ ts Γ fuel n ss sW with
     | some (.newRound ss' sW') => t.okLoop k true ss' sW' ts sR sL
     | _ => false)
  | .node i t0 t1, wf, ss, sW, ts, sR, sL =>
    decide (i < k) &&
      t0.okLoop k wf (substL ss i 0) (sW.subst i 0) (substT ts i 0) (sR.subst i 0) (sL.subst i 0) &&
      t1.okLoop k wf (substL ss i 1) (sW.subst i 1) (substT ts i 1) (sR.subst i 1) (sL.subst i 1)
  | .skew i j s t, wf, ss, sW, ts, sR, sL =>
    decide (i < k) && decide (j < k) && decide (i ≠ j) &&
      t.okLoop k wf (skewL ss i j s) (sW.skew i j s) (skewT ts i j s) (sR.skew i j s) (sL.skew i j s)

/-- The loop check's state: start state, right end and left countdown (substituted along with the start). -/
abbrev LState := SState × YForm × YForm

def lsSplit (ls : LState) (i : Nat) (ε : Int) : LState := (stSplit ls.1 i ε, ls.2.1.subst i ε, ls.2.2.subst i ε)
def lsSkew (ls : LState) (i j : Nat) (s : Int) : LState := (stSkew ls.1 i j s, ls.2.1.skew i j s, ls.2.2.skew i j s)

variable {Γ fuel} in
theorem Tree.okLoop_node {k i : Nat} {wf : Bool} {t0 t1 : Tree} {ls : LState} (hi : i < k)
    (h0 : t0.okLoop Γ fuel k wf (lsSplit ls i 0).1.1 (lsSplit ls i 0).1.2.1 (lsSplit ls i 0).1.2.2 (lsSplit ls i 0).2.1
      (lsSplit ls i 0).2.2 = true)
    (h1 : t1.okLoop Γ fuel k wf (lsSplit ls i 1).1.1 (lsSplit ls i 1).1.2.1 (lsSplit ls i 1).1.2.2 (lsSplit ls i 1).2.1
      (lsSplit ls i 1).2.2 = true) :
    (Tree.node i t0 t1).okLoop Γ fuel k wf ls.1.1 ls.1.2.1 ls.1.2.2 ls.2.1 ls.2.2 = true := by
  simp only [Tree.okLoop, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hi, h0⟩, h1⟩

variable {Γ fuel} in
theorem Tree.okLoop_skew {k i j : Nat} {wf : Bool} {s : Int} {t : Tree} {ls : LState} (hi : i < k) (hj : j < k)
    (hij : i ≠ j) (h : t.okLoop Γ fuel k wf (lsSkew ls i j s).1.1 (lsSkew ls i j s).1.2.1 (lsSkew ls i j s).1.2.2 (lsSkew ls i j s).2.1
      (lsSkew ls i j s).2.2 = true) :
    (Tree.skew i j s t).okLoop Γ fuel k wf ls.1.1 ls.1.2.1 ls.1.2.2 ls.2.1 ls.2.2 = true := by
  simp only [Tree.okLoop, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨⟨hi, hj⟩, hij⟩, h⟩

/-- **A checked loop tree, for the machine.**  At every point of the root class inside the cone, the machine runs
from the root's round start for the rounds recorded on the way to the leaf without halting and without a close, and
the round start it reaches is not a phase-0 pass start, or is one with gaps ≥ 448 and a smaller right end
(`LoopOut`). -/
theorem Tree.soundLoop (k : Nat) (t : Tree) : ∀ (wf : Bool) (ss : List SMark) (sW : YForm) (ts : List YForm)
    (sR sL : YForm), t.okLoop Γ fuel k wf ss sW ts sR sL = true → ∀ (y : List Int), y.length = k → inCone ts Γ y →
    ∀ (ms : List Mark) (Wn R : Nat) (L : Int), agL y ss ms → agN y sW Wn → agN y sR R → L = sL.eval y →
    (wf = true → roundWF ms Wn) →
    ∃ n kk ms' Wn', steps kk (roundStart ms Wn) = some (roundStart ms' Wn') ∧
      roundsZ fuel n ms Wn = .newRound ms' Wn' ∧ (∀ d ∈ meetsRounds fuel n ms Wn, 3 ≤ d) ∧ LoopOut R L ms' Wn' := by
  induction t with
  | leaf n =>
    intro wf ss sW ts sR sL h y _ hy ms Wn R L hs hW hR hL hwf
    simp only [Tree.okLoop, Bool.and_eq_true] at h
    obtain ⟨⟨hwf', hrun⟩, hmt⟩ := h
    have hrwf := wf_of_check Γ hy hs hW hwf hwf'
    cases hr : symRoundsZ ts Γ fuel n ss sW with
    | none => rw [hr] at hrun; cases hrun
    | some r =>
      rw [hr] at hrun
      cases r with
      | newRound ss' sW' =>
        cases hmr : symMeetsRounds ts Γ fuel n ss sW with
        | none => rw [hmr] at hmt; cases hmt
        | some ds =>
          rw [hmr] at hmt
          have hds := symMeetsRounds_sound ts Γ hy fuel n ss ms sW Wn ds hs hW hmr
          have hge := allGe3_sound ts Γ hy hds hmt
          have hag := symRoundsZ_sound ts Γ hy fuel n ss ms sW Wn _ hs hW hr
          generalize hcr : roundsZ fuel n ms Wn = cr at hag
          cases cr with
          | newRound ms' Wn' =>
            obtain ⟨kk, hk, -⟩ := rounds_run fuel n ms Wn hrwf (by rw [hcr]; intro h; cases h)
            rw [hcr] at hk
            exact ⟨n, kk, ms', Wn', hk, hcr, hge, endCheck_sound ts Γ hy hR hL hag.1 hag.2 hrun⟩
          | _ => exact absurd hag id
      | _ => simp at hrun
  | adv n t ih =>
    intro wf ss sW ts sR sL h y hlen hy ms Wn R L hs hW hR hL hwf
    simp only [Tree.okLoop, Bool.and_eq_true] at h
    obtain ⟨⟨hwf', hmt⟩, hrun⟩ := h
    have hrwf := wf_of_check Γ hy hs hW hwf hwf'
    cases hr : symRoundsZ ts Γ fuel n ss sW with
    | none => rw [hr] at hrun; cases hrun
    | some r =>
      rw [hr] at hrun
      cases r with
      | newRound ss' sW' =>
        cases hmr : symMeetsRounds ts Γ fuel n ss sW with
        | none => rw [hmr] at hmt; cases hmt
        | some ds =>
          rw [hmr] at hmt
          have hds := symMeetsRounds_sound ts Γ hy fuel n ss ms sW Wn ds hs hW hmr
          have hge := allGe3_sound ts Γ hy hds hmt
          have hag := symRoundsZ_sound ts Γ hy fuel n ss ms sW Wn _ hs hW hr
          generalize hcr : roundsZ fuel n ms Wn = cr at hag
          cases cr with
          | newRound ms' Wn' =>
            obtain ⟨kk, hk, hw'⟩ := rounds_run fuel n ms Wn hrwf (by rw [hcr]; intro h; cases h)
            rw [hcr] at hk hw'
            obtain ⟨n₂, kk₂, ms'', Wn'', hk₂, hr₂, hge₂, hout⟩ :=
              ih true ss' sW' ts sR sL hrun y hlen hy ms' Wn' R L hag.1 hag.2 hR hL (fun _ => hw')
            refine ⟨n + n₂, kk + kk₂, ms'', Wn'', steps_seq hk hk₂, ?_, ?_, hout⟩
            · rw [roundsZ_add fuel n n₂ ms Wn ms' Wn' hcr]; exact hr₂
            · rw [meetsRounds_append fuel n n₂ ms Wn ms' Wn' hcr]
              intro d hd
              rcases List.mem_append.mp hd with hd | hd
              · exact hge d hd
              · exact hge₂ d hd
          | _ => exact absurd hag id
      | _ => simp at hrun
  | node i t0 t1 ih0 ih1 =>
    intro wf ss sW ts sR sL h y hlen hy ms Wn R L hs hW hR hL hwf
    simp only [Tree.okLoop, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h0⟩, h1⟩ := h
    obtain ⟨ε, z, hε, hzl, rfl⟩ := cover_split y i (by omega)
    have hiz : i < z.length := by omega
    rcases hε with rfl | rfl
    · exact ih0 _ _ _ _ _ _ h0 z (by rw [hzl]; exact hlen) (inCone_subst hiz hy) ms Wn R L (agL_subst hiz hs)
        (agN_subst hiz hW) (agN_subst hiz hR) (by rw [hL, eval_subst sL i 0 z hiz]) hwf
    · exact ih1 _ _ _ _ _ _ h1 z (by rw [hzl]; exact hlen) (inCone_subst hiz hy) ms Wn R L (agL_subst hiz hs)
        (agN_subst hiz hW) (agN_subst hiz hR) (by rw [hL, eval_subst sL i 1 z hiz]) hwf
  | skew i j s t ih =>
    intro wf ss sW ts sR sL h y hlen hy ms Wn R L hs hW hR hL hwf
    simp only [Tree.okLoop, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, hij⟩, ht⟩ := h
    obtain ⟨z, hzl, rfl⟩ := cover_skew y i j s hij (by omega)
    have hiz : i < z.length := by omega
    have hjz : j < z.length := by omega
    exact ih _ _ _ _ _ _ ht z (by rw [hzl]; exact hlen) (inCone_skew hiz hjz hy) ms Wn R L (agL_skew hiz hjz hs)
      (agN_skew hiz hjz hW) (agN_skew hiz hjz hR) (by rw [hL, eval_skew sL i j s z hiz hjz]) hwf

end BB6.Sym
