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

/-! ## Trees of splits -/

/-- A leaf records the number of rounds its symbolic run is checked for. -/
inductive Tree where
  | leaf (rounds : Nat)
  | node (i : Nat) (t0 t1 : Tree)
  deriving Repr

variable (Γ : Int) (fuel : Nat)

/-- Every leaf's symbolic run is decided for its number of rounds and ends at a round start, from a well-formed
start; `k` is the number of coordinates. -/
def Tree.ok (k : Nat) : Tree → List SMark → YForm → List YForm → Bool
  | .leaf n, ss, sW, ts =>
    symRightOK ts Γ (YForm.const 4) false sW ss &&
    (match symRoundsZ ts Γ fuel n ss sW with
     | some (.newRound _ _) => true
     | _ => false)
  | .node i t0 t1, ss, sW, ts =>
    decide (i < k) && t0.ok k (substL ss i 0) (sW.subst i 0) (substT ts i 0) &&
      t1.ok k (substL ss i 1) (sW.subst i 1) (substT ts i 1)

/-- **A checked tree, for the machine.**  At every point `y` of the root class inside the cone, the machine runs
from the round start the root describes for at least two... for some positive number of rounds — the number recorded
at the leaf that contains `y` — and reaches a round start: it does not halt on the way. -/
theorem Tree.sound (k : Nat) (t : Tree) : ∀ (ss : List SMark) (sW : YForm) (ts : List YForm),
    t.ok Γ fuel k ss sW ts = true → ∀ (y : List Int), y.length = k → inCone ts Γ y →
    ∀ (ms : List Mark) (Wn : Nat), agL y ss ms → agN y sW Wn →
    ∃ n kk ms' Wn', steps kk (roundStart ms Wn) = some (roundStart ms' Wn') ∧ roundsZ fuel n ms Wn = .newRound ms' Wn' := by
  induction t with
  | leaf n =>
    intro ss sW ts h y _ hy ms Wn hs hW
    simp only [Tree.ok, Bool.and_eq_true] at h
    obtain ⟨hwf, hrun⟩ := h
    cases hr : symRoundsZ ts Γ fuel n ss sW with
    | none => rw [hr] at hrun; cases hrun
    | some r =>
      rw [hr] at hrun
      cases r with
      | newRound ss' sW' =>
        have hag := symRoundsZ_sound ts Γ hy fuel n ss ms sW Wn _ hs hW hr
        have hrwf : roundWF ms Wn := symRightOK_sound ts Γ hy ss _ 4 false sW Wn ms (agN_const y 4) hW hs hwf
        generalize hcr : roundsZ fuel n ms Wn = cr at hag
        cases cr with
        | newRound ms' Wn' =>
          obtain ⟨kk, hk, -⟩ := rounds_run fuel n ms Wn hrwf (by rw [hcr]; intro h; cases h)
          rw [hcr] at hk
          exact ⟨n, kk, ms', Wn', hk, hcr⟩
        | _ => exact absurd hag id
      | _ => simp at hrun
  | node i t0 t1 ih0 ih1 =>
    intro ss sW ts h y hlen hy ms Wn hs hW
    simp only [Tree.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h0⟩, h1⟩ := h
    obtain ⟨ε, z, hε, hzl, rfl⟩ := cover_split y i (by omega)
    have hiz : i < z.length := by omega
    rcases hε with rfl | rfl
    · exact ih0 _ _ _ h0 z (by rw [hzl]; exact hlen) (inCone_subst hiz hy) ms Wn (agL_subst hiz hs) (agN_subst hiz hW)
    · exact ih1 _ _ _ h1 z (by rw [hzl]; exact hlen) (inCone_subst hiz hy) ms Wn (agL_subst hiz hs) (agN_subst hiz hW)

/-- Two forms with the same constant and coefficients (shared by `Loop` and `RouteTree`, which can be imported
together). -/
def sameForm (f g : YForm) : Bool := f.k == g.k && coeffEq f.c g.c

theorem sameForm_eval {f g : YForm} (h : sameForm f g = true) (y : List Int) : f.eval y = g.eval y := by
  simp only [sameForm, Bool.and_eq_true, beq_iff_eq] at h
  simp only [YForm.eval, h.1, dot_coeffEq _ _ y h.2]

theorem sameForm_sound {f g : YForm} (h : sameForm f g = true) (y : List Int) : f.eval y = g.eval y :=
  sameForm_eval h y

end BB6.Sym
