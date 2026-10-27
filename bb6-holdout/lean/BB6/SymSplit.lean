import BB6.SymRound

/-!
# Splitting a class, with coverage by construction

A class of starts is a set of coordinate vectors y (the start's positions are forms in y).  Splitting on coordinate
`i` substitutes `yᵢ = 2 zᵢ + ε` (ε = 0 or 1) in every form: the two children together contain every y
(`cover_split`), so a tree of splits whose leaves all check covers the whole class, and nothing about lattices or
partitions has to be verified separately.  `Tree` is such a tree, `Tree.ok` says every leaf passed the proved check
(a decided symbolic run of its number of rounds from a well-formed start), and `Tree.sound` is the statement for the
machine at every point of the root class inside the cone.
-/

namespace BB6.Sym
open BB6

/-- Substitute `yᵢ = 2 zᵢ + ε` in a coefficient list: the constant gains `ε cᵢ`, the coefficient doubles. -/
def substC (c : List Int) (i : Nat) : List Int := c.set i (2 * c.getD i 0)

def YForm.subst (f : YForm) (i : Nat) (ε : Int) : YForm := ⟨f.k + ε * f.c.getD i 0, substC f.c i⟩

/-- The point `z` with coordinate `i` replaced by `2 zᵢ + ε`. -/
def lift (z : List Int) (i : Nat) (ε : Int) : List Int := z.set i (2 * z.getD i 0 + ε)

theorem dot_subst (c z : List Int) (i : Nat) (ε : Int) (hi : i < z.length) :
    dot (substC c i) z + ε * c.getD i 0 = dot c (lift z i ε) := by
  induction c generalizing z i with
  | nil => simp [substC, lift]
  | cons a as ih =>
    cases z with
    | nil => simp at hi
    | cons w ws =>
      cases i with
      | zero =>
        simp only [substC, lift, List.set, List.getD, List.getElem?_cons_zero, Option.getD_some, dot]
        rw [Int.mul_add, Int.mul_comm 2 a, Int.mul_assoc, Int.mul_comm ε a]; omega
      | succ j =>
        simp only [substC, lift, List.set, List.getD, List.getElem?_cons_succ, dot]
        have := ih ws j (by simpa using hi)
        simp only [substC, lift, List.getD] at this
        omega

theorem eval_subst (f : YForm) (i : Nat) (ε : Int) (z : List Int) (hi : i < z.length) :
    (f.subst i ε).eval z = f.eval (lift z i ε) := by
  simp only [YForm.subst, YForm.eval]
  have := dot_subst f.c z i ε hi
  omega

def SMark.subst (m : SMark) (i : Nat) (ε : Int) : SMark := ⟨m.t, m.p.subst i ε⟩
def substL (ss : List SMark) (i : Nat) (ε : Int) : List SMark := ss.map (·.subst i ε)
def substT (ts : List YForm) (i : Nat) (ε : Int) : List YForm := ts.map (·.subst i ε)

theorem length_lift (z : List Int) (i : Nat) (ε : Int) : (lift z i ε).length = z.length := by simp [lift]

/-- Agreement transported along a substitution. -/
theorem agN_subst {f : YForm} {i : Nat} {ε : Int} {z : List Int} (hi : i < z.length) {n : Nat}
    (h : agN (lift z i ε) f n) : agN z (f.subst i ε) n := by
  unfold agN at *; rw [eval_subst f i ε z hi]; exact h

theorem agL_subst {i : Nat} {ε : Int} {z : List Int} (hi : i < z.length) :
    ∀ {ss : List SMark} {ms : List Mark}, agL (lift z i ε) ss ms → agL z (substL ss i ε) ms
  | [], [], _ => trivial
  | s :: ss, m :: ms, h => ⟨⟨h.1.1, agN_subst hi h.1.2⟩, agL_subst hi h.2⟩
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id

theorem inCone_subst {ts : List YForm} {Γ : Int} {i : Nat} {ε : Int} {z : List Int} (hi : i < z.length)
    (h : inCone ts Γ (lift z i ε)) : inCone (substT ts i ε) Γ z := by
  intro t ht
  simp only [substT, List.mem_map] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  rw [eval_subst t' i ε z hi]
  exact h t' ht'

/-- Every point is the lift of a point of one of the two children. -/
theorem cover_split (y : List Int) (i : Nat) (hi : i < y.length) :
    ∃ ε z, (ε = 0 ∨ ε = 1) ∧ z.length = y.length ∧ y = lift z i ε := by
  refine ⟨y.getD i 0 % 2, y.set i (y.getD i 0 / 2), ?_, by simp, ?_⟩
  · have h1 := Int.emod_nonneg (y.getD i 0) (by decide : (2:Int) ≠ 0)
    have h2 := Int.emod_lt_of_pos (y.getD i 0) (by decide : (0:Int) < 2)
    omega
  · simp only [lift]
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      simp only [List.getElem_set]
      split
      · rename_i hn
        subst hn
        have hg : y.getD i 0 = y[i] := by simp [List.getD, List.getElem?_eq_getElem h1]
        have hs : (y.set i (y.getD i 0 / 2)).getD i 0 = y.getD i 0 / 2 := by
          simp [List.getD, List.getElem?_set_self (by omega : i < y.length)]
        rw [hs, ← hg]
        omega
      · rfl

/-! ## Skews

A skew `yᵢ = zᵢ + s·zⱼ` (i ≠ j) is a bijection of ℤᵏ, so it changes coordinates without losing a point
(`cover_skew`).  Skews followed by a split on `zᵢ` split a class on the parity of any form with an odd coefficient
`cᵢ` (each other odd coefficient `cⱼ` is first made even by the skew with s = 1), where coordinate splits alone would
have to split every coordinate with an odd coefficient. -/

/-- Skew `yᵢ = zᵢ + s·zⱼ` in a coefficient list: `cⱼ` gains `s·cᵢ`. -/
def skewC (c : List Int) (i j : Nat) (s : Int) : List Int := addL c (unitL j (s * c.getD i 0))

def YForm.skew (f : YForm) (i j : Nat) (s : Int) : YForm := ⟨f.k, skewC f.c i j s⟩

/-- The point `z` with coordinate `i` replaced by `zᵢ + s·zⱼ`. -/
def skewLift (z : List Int) (i j : Nat) (s : Int) : List Int := z.set i (z.getD i 0 + s * z.getD j 0)

theorem dot_set (c z : List Int) (i : Nat) (v : Int) (hi : i < z.length) :
    dot c (z.set i v) = dot c z + c.getD i 0 * (v - z.getD i 0) := by
  induction c generalizing z i with
  | nil => simp
  | cons a as ih =>
    cases z with
    | nil => simp at hi
    | cons w ws =>
      cases i with
      | zero =>
        simp only [List.set, dot, List.getD_cons_zero]
        rw [Int.mul_sub]; omega
      | succ j =>
        simp only [List.set, dot, List.getD_cons_succ]
        rw [ih ws j (by simpa using hi)]; omega

theorem eval_skew (f : YForm) (i j : Nat) (s : Int) (z : List Int) (hi : i < z.length) (_hj : j < z.length) :
    (f.skew i j s).eval z = f.eval (skewLift z i j s) := by
  simp only [YForm.skew, YForm.eval, skewC, skewLift, dot_addL, dot_unitL j _ z, dot_set f.c z i _ hi]
  rw [show z.getD i 0 + s * z.getD j 0 - z.getD i 0 = s * z.getD j 0 by omega, Int.mul_left_comm, ← Int.mul_assoc]

def SMark.skew (m : SMark) (i j : Nat) (s : Int) : SMark := ⟨m.t, m.p.skew i j s⟩
def skewL (ss : List SMark) (i j : Nat) (s : Int) : List SMark := ss.map (·.skew i j s)
def skewT (ts : List YForm) (i j : Nat) (s : Int) : List YForm := ts.map (·.skew i j s)

theorem agN_skew {f : YForm} {i j : Nat} {s : Int} {z : List Int} (hi : i < z.length) (hj : j < z.length) {n : Nat}
    (h : agN (skewLift z i j s) f n) : agN z (f.skew i j s) n := by
  unfold agN at *; rw [eval_skew f i j s z hi hj]; exact h

theorem agL_skew {i j : Nat} {s : Int} {z : List Int} (hi : i < z.length) (hj : j < z.length) :
    ∀ {ss : List SMark} {ms : List Mark}, agL (skewLift z i j s) ss ms → agL z (skewL ss i j s) ms
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨⟨h.1.1, agN_skew hi hj h.1.2⟩, agL_skew hi hj h.2⟩
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id

theorem inCone_skew {ts : List YForm} {Γ : Int} {i j : Nat} {s : Int} {z : List Int} (hi : i < z.length)
    (hj : j < z.length) (h : inCone ts Γ (skewLift z i j s)) : inCone (skewT ts i j s) Γ z := by
  intro t ht
  simp only [skewT, List.mem_map] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  rw [eval_skew t' i j s z hi hj]
  exact h t' ht'

/-- Every point is the skew of a point. -/
theorem cover_skew (y : List Int) (i j : Nat) (s : Int) (hij : i ≠ j) (hi : i < y.length) :
    ∃ z, z.length = y.length ∧ y = skewLift z i j s := by
  refine ⟨y.set i (y.getD i 0 - s * y.getD j 0), by simp, ?_⟩
  have hzj : (y.set i (y.getD i 0 - s * y.getD j 0)).getD j 0 = y.getD j 0 := by
    simp [List.getD, List.getElem?_set_ne hij]
  have hzi : (y.set i (y.getD i 0 - s * y.getD j 0)).getD i 0 = y.getD i 0 - s * y.getD j 0 := by
    simp [List.getD, List.getElem?_set_self hi]
  simp only [skewLift, hzj, hzi, List.set_set]
  rw [show y.getD i 0 - s * y.getD j 0 + s * y.getD j 0 = y.getD i 0 by omega]
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_set]
    split
    · rename_i hn
      subst hn
      simp [List.getD, List.getElem?_eq_getElem h1]
    · rfl

/-! ## Several rounds compose -/

theorem roundsZ_add (fuel : Nat) : ∀ (n₁ n₂ : Nat) (ms : List Mark) (W : Nat) (ms' : List Mark) (W' : Nat),
    roundsZ fuel n₁ ms W = .newRound ms' W' → roundsZ fuel (n₁ + n₂) ms W = roundsZ fuel n₂ ms' W'
  | 0, n₂, ms, W, ms', W', h => by simp only [roundsZ] at h; cases h; simp
  | n₁ + 1, n₂, ms, W, ms', W', h => by
    rw [show n₁ + 1 + n₂ = (n₁ + n₂) + 1 by omega]
    simp only [roundsZ] at h ⊢
    generalize roundZ fuel [] 1 ms W = r at h ⊢
    cases r with
    | newRound a b => exact roundsZ_add fuel n₁ n₂ a b ms' W' h
    | gap _ _ _ _ => cases h
    | halt => cases h
    | uncovered => cases h

/-! ## Trees of splits -/

/-- A leaf records the number of rounds its symbolic run is checked for; `node i` splits on coordinate i,
`skew i j s` changes coordinates by yᵢ = zᵢ + s·zⱼ, and `adv n` runs n rounds on the whole class before going on, so
that rounds before a split are checked once for all the leaves below it. -/
inductive Tree where
  | leaf (rounds : Nat)
  | node (i : Nat) (t0 t1 : Tree)
  | skew (i j : Nat) (s : Int) (t : Tree)
  | adv (rounds : Nat) (t : Tree)
  deriving Repr

variable (Γ : Int) (fuel : Nat)

/-- Every leaf's symbolic run is decided for its number of rounds and ends at a round start, from a well-formed
start; `k` is the number of coordinates, and `wf` records that the start is already known to be well formed (it is
the end of a run). -/
def Tree.ok (k : Nat) : Tree → Bool → List SMark → YForm → List YForm → Bool
  | .leaf n, wf, ss, sW, ts =>
    (wf || symRightOK ts Γ (YForm.const 4) false sW ss) &&
    (match symRoundsZ ts Γ fuel n ss sW with
     | some (.newRound _ _) => true
     | _ => false)
  | .adv n t, wf, ss, sW, ts =>
    (wf || symRightOK ts Γ (YForm.const 4) false sW ss) &&
    (match symRoundsZ ts Γ fuel n ss sW with
     | some (.newRound ss' sW') => t.ok k true ss' sW' ts
     | _ => false)
  | .node i t0 t1, wf, ss, sW, ts =>
    decide (i < k) && t0.ok k wf (substL ss i 0) (sW.subst i 0) (substT ts i 0) &&
      t1.ok k wf (substL ss i 1) (sW.subst i 1) (substT ts i 1)
  | .skew i j s t, wf, ss, sW, ts =>
    decide (i < k) && decide (j < k) && decide (i ≠ j) && t.ok k wf (skewL ss i j s) (sW.skew i j s) (skewT ts i j s)

/-! ### A tree's check from its subtrees' checks

`stSplit` and `stSkew` are the states the check passes to a node's children, so a large tree can be checked one
subtree at a time (each subtree's check its own `decide +kernel` theorem) and assembled with `Tree.ok_node` and
`Tree.ok_skew`. -/

/-- A start state: marks, width, gap forms. -/
abbrev SState := List SMark × YForm × List YForm

def stSplit (st : SState) (i : Nat) (ε : Int) : SState := (substL st.1 i ε, st.2.1.subst i ε, substT st.2.2 i ε)
def stSkew (st : SState) (i j : Nat) (s : Int) : SState := (skewL st.1 i j s, st.2.1.skew i j s, skewT st.2.2 i j s)

variable {Γ fuel} in
theorem Tree.ok_node {k i : Nat} {wf : Bool} {t0 t1 : Tree} {st : SState} (hi : i < k)
    (h0 : t0.ok Γ fuel k wf (stSplit st i 0).1 (stSplit st i 0).2.1 (stSplit st i 0).2.2 = true)
    (h1 : t1.ok Γ fuel k wf (stSplit st i 1).1 (stSplit st i 1).2.1 (stSplit st i 1).2.2 = true) :
    (Tree.node i t0 t1).ok Γ fuel k wf st.1 st.2.1 st.2.2 = true := by
  simp only [Tree.ok, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hi, h0⟩, h1⟩

variable {Γ fuel} in
theorem Tree.ok_skew {k i j : Nat} {wf : Bool} {s : Int} {t : Tree} {st : SState} (hi : i < k) (hj : j < k)
    (hij : i ≠ j) (h : t.ok Γ fuel k wf (stSkew st i j s).1 (stSkew st i j s).2.1 (stSkew st i j s).2.2 = true) :
    (Tree.skew i j s t).ok Γ fuel k wf st.1 st.2.1 st.2.2 = true := by
  simp only [Tree.ok, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨⟨hi, hj⟩, hij⟩, h⟩

/-- The start's well-formedness, from the flag or from the check. -/
theorem wf_of_check {wf : Bool} {ts : List YForm} {y : List Int} (hy : inCone ts Γ y) {ss : List SMark}
    {ms : List Mark} {sW : YForm} {Wn : Nat} (hs : agL y ss ms) (hW : agN y sW Wn) (hwf : wf = true → roundWF ms Wn)
    (h : (wf || symRightOK ts Γ (YForm.const 4) false sW ss) = true) : roundWF ms Wn := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact hwf h
  · exact symRightOK_sound ts Γ hy ss _ 4 false sW Wn ms (agN_const y 4) hW hs h

/-- **A checked tree, for the machine.**  At every point `y` of the root class inside the cone, the machine runs
from the round start the root describes for some number of rounds — the rounds recorded on the way to the leaf that
contains `y` — and reaches a round start: it does not halt on the way. -/
theorem Tree.sound (k : Nat) (t : Tree) : ∀ (wf : Bool) (ss : List SMark) (sW : YForm) (ts : List YForm),
    t.ok Γ fuel k wf ss sW ts = true → ∀ (y : List Int), y.length = k → inCone ts Γ y →
    ∀ (ms : List Mark) (Wn : Nat), agL y ss ms → agN y sW Wn → (wf = true → roundWF ms Wn) →
    ∃ n kk ms' Wn', steps kk (roundStart ms Wn) = some (roundStart ms' Wn') ∧ roundsZ fuel n ms Wn = .newRound ms' Wn' := by
  induction t with
  | leaf n =>
    intro wf ss sW ts h y _ hy ms Wn hs hW hwf
    simp only [Tree.ok, Bool.and_eq_true] at h
    obtain ⟨hwf', hrun⟩ := h
    have hrwf := wf_of_check Γ hy hs hW hwf hwf'
    cases hr : symRoundsZ ts Γ fuel n ss sW with
    | none => rw [hr] at hrun; cases hrun
    | some r =>
      rw [hr] at hrun
      cases r with
      | newRound ss' sW' =>
        have hag := symRoundsZ_sound ts Γ hy fuel n ss ms sW Wn _ hs hW hr
        generalize hcr : roundsZ fuel n ms Wn = cr at hag
        cases cr with
        | newRound ms' Wn' =>
          obtain ⟨kk, hk, -⟩ := rounds_run fuel n ms Wn hrwf (by rw [hcr]; intro h; cases h)
          rw [hcr] at hk
          exact ⟨n, kk, ms', Wn', hk, hcr⟩
        | _ => exact absurd hag id
      | _ => simp at hrun
  | adv n t ih =>
    intro wf ss sW ts h y hlen hy ms Wn hs hW hwf
    simp only [Tree.ok, Bool.and_eq_true] at h
    obtain ⟨hwf', hrun⟩ := h
    have hrwf := wf_of_check Γ hy hs hW hwf hwf'
    cases hr : symRoundsZ ts Γ fuel n ss sW with
    | none => rw [hr] at hrun; cases hrun
    | some r =>
      rw [hr] at hrun
      cases r with
      | newRound ss' sW' =>
        have hag := symRoundsZ_sound ts Γ hy fuel n ss ms sW Wn _ hs hW hr
        generalize hcr : roundsZ fuel n ms Wn = cr at hag
        cases cr with
        | newRound ms' Wn' =>
          obtain ⟨kk, hk, hw'⟩ := rounds_run fuel n ms Wn hrwf (by rw [hcr]; intro h; cases h)
          rw [hcr] at hk hw'
          obtain ⟨n₂, kk₂, ms'', Wn'', hk₂, hr₂⟩ := ih true ss' sW' ts hrun y hlen hy ms' Wn' hag.1 hag.2 (fun _ => hw')
          refine ⟨n + n₂, kk + kk₂, ms'', Wn'', steps_seq hk hk₂, ?_⟩
          rw [roundsZ_add fuel n n₂ ms Wn ms' Wn' hcr]; exact hr₂
        | _ => exact absurd hag id
      | _ => simp at hrun
  | node i t0 t1 ih0 ih1 =>
    intro wf ss sW ts h y hlen hy ms Wn hs hW hwf
    simp only [Tree.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h0⟩, h1⟩ := h
    obtain ⟨ε, z, hε, hzl, rfl⟩ := cover_split y i (by omega)
    have hiz : i < z.length := by omega
    rcases hε with rfl | rfl
    · exact ih0 _ _ _ _ h0 z (by rw [hzl]; exact hlen) (inCone_subst hiz hy) ms Wn (agL_subst hiz hs)
        (agN_subst hiz hW) hwf
    · exact ih1 _ _ _ _ h1 z (by rw [hzl]; exact hlen) (inCone_subst hiz hy) ms Wn (agL_subst hiz hs)
        (agN_subst hiz hW) hwf
  | skew i j s t ih =>
    intro wf ss sW ts h y hlen hy ms Wn hs hW hwf
    simp only [Tree.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, hij⟩, ht⟩ := h
    obtain ⟨z, hzl, rfl⟩ := cover_skew y i j s hij (by omega)
    have hiz : i < z.length := by omega
    have hjz : j < z.length := by omega
    exact ih _ _ _ _ ht z (by rw [hzl]; exact hlen) (inCone_skew hiz hjz hy) ms Wn (agL_skew hiz hjz hs)
      (agN_skew hiz hjz hW) hwf

/-- Two forms with the same constant and coefficients (shared by `Loop` and `RouteTree`, which can be imported
together). -/
def sameForm (f g : YForm) : Bool := f.k == g.k && coeffEq f.c g.c

theorem sameForm_eval {f g : YForm} (h : sameForm f g = true) (y : List Int) : f.eval y = g.eval y := by
  simp only [sameForm, Bool.and_eq_true, beq_iff_eq] at h
  simp only [YForm.eval, h.1, dot_coeffEq _ _ y h.2]

theorem sameForm_sound {f g : YForm} (h : sameForm f g = true) (y : List Int) : f.eval y = g.eval y :=
  sameForm_eval h y

end BB6.Sym
