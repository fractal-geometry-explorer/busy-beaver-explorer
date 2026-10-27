import BB6.PassTree
import BB6.CloseHalt

/-!
# Halting trees: classes of pass starts proved to halt

A halting tree (`HTree`) splits a class of round starts like a pass-start tree (coordinate splits, skews, cleaves),
and claims at each `halt` leaf that every member halts: the close run on symbolic positions (`symCloseRun`) reaches
the close `EndClose0` on the leaf's class, from the root's round start.  `HTree.sound` is the statement for the
machine.  `HTree.ofPTree` reads a halting tree off a pass-start tree: the same splits, with a `halt` leaf wherever a
`close` or `cut` leaf's class passes the close run, so its check holds by construction (`HTree.ofPTree_ok`) and
nothing is evaluated.  `HTree.haltMass` is the measure of the `halt` leaves.
-/

namespace BB6.Sym
open BB6

/-- A halting tree. -/
inductive HTree where
  /-- no claim -/
  | open
  /-- every member of the class halts -/
  | halt
  /-- split on coordinate `i`: yᵢ = 2 zᵢ + ε -/
  | split (i : Nat) (t0 t1 : HTree)
  /-- change coordinates: yᵢ = zᵢ + s·zⱼ -/
  | skew (i j : Nat) (s : Int) (t : HTree)
  /-- cleave on coordinate `i` at `c`, as in `PTree.cleave` -/
  | cleave (i : Nat) (c σ : Int) (j0 j1 : Nat) (t0 t1 : HTree)
  deriving Repr, Inhabited

variable (Γ : Int) (fuel : Nat)

/-- The check, on the root's round start (`ss`, `sW`) under the class's substitutions and cone `ts`. -/
def HTree.ok (k : Nat) : HTree → List SMark → YForm → List YForm → Bool
  | .open, _, _, _ => true
  | .halt, ss, sW, ts => symCloseRun ts Γ fuel [] (YForm.const 1) ss sW
  | .split i t0 t1, ss, sW, ts =>
    decide (i < k) && t0.ok k (substL ss i 0) (sW.subst i 0) (substT ts i 0) &&
      t1.ok k (substL ss i 1) (sW.subst i 1) (substT ts i 1)
  | .skew i j s t, ss, sW, ts =>
    decide (i < k) && decide (j < k) && decide (i ≠ j) && t.ok k (skewL ss i j s) (sW.skew i j s) (skewT ts i j s)
  | .cleave i c σ j0 j1 t0 t1, ss, sW, ts =>
    decide (i < k) && σ != 0 && ltDec (cleaveBnd i c σ) (YForm.const 0) ts Γ == some false &&
      t0.ok k (pinL ss i c) (sW.pin i c) ((pinT ts i c).eraseIdx j0) &&
      t1.ok k ss sW (ts.set j1 ((cleaveBnd i c σ).addc (Γ - 1)))

/-- Follow a point down the tree: `true` when it ends in a `halt` leaf. -/
def HTree.haltMem : HTree → List Int → Bool
  | .open, _ => false
  | .halt, _ => true
  | .split i t0 t1, y =>
    if y.getD i 0 % 2 = 0 then t0.haltMem (y.set i (y.getD i 0 / 2)) else t1.haltMem (y.set i (y.getD i 0 / 2))
  | .skew i j s t, y => t.haltMem (y.set i (y.getD i 0 - s * y.getD j 0))
  | .cleave i c _ _ _ t0 t1, y => if y.getD i 0 = c then t0.haltMem y else t1.haltMem y

/-- The measure of the `halt` leaves, as a numerator over 2^D (the slice of a cleave has measure 0). -/
def HTree.haltMass : Nat → HTree → Nat
  | D, .halt => 2 ^ D
  | _, .open => 0
  | D, .split _ t0 t1 => t0.haltMass (D - 1) + t1.haltMass (D - 1)
  | D, .skew _ _ _ t => t.haltMass D
  | D, .cleave _ _ _ _ _ _ t1 => t1.haltMass D

/-- **A checked halting tree, for the machine.**  At every point `y` of the root class inside the cone whose leaf
is a `halt` leaf, from a well-formed round start without sleeping gaps that agrees with the root, the machine
halts. -/
theorem HTree.sound (k : Nat) (t : HTree) :
    ∀ (ss : List SMark) (sW : YForm) (ts : List YForm), t.ok Γ fuel k ss sW ts = true →
    ∀ (y : List Int), y.length = k → inCone ts Γ y → ∀ (ms : List Mark) (Wn : Nat), agL y ss ms → agN y sW Wn →
    roundWF ms Wn → noG ms → t.haltMem y = true → ∃ T, steps T (roundStart ms Wn) = none := by
  induction t with
  | «open» => intro _ _ _ _ _ _ _ _ _ _ _ _ _ hm; cases hm
  | halt =>
    intro ss sW ts h y _ hy ms Wn hs hW hwf hG _
    exact symCloseRun_halt ts Γ fuel h hy hs hW hwf hG
  | split i t0 t1 ih0 ih1 =>
    intro ss sW ts h y hlen hy ms Wn hs hW hwf hG hm
    simp only [HTree.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h0⟩, h1⟩ := h
    have hiy : i < y.length := by omega
    have hy' := pt_lift_half y i hiy
    have hzl : (y.set i (y.getD i 0 / 2)).length = k := by simp [hlen]
    have hiz : i < (y.set i (y.getD i 0 / 2)).length := by simp; omega
    simp only [HTree.haltMem] at hm
    rcases pt_mod_two (y.getD i 0) with he | he
    · simp only [he, ↓reduceIte] at hm
      rw [he] at hy'
      rw [hy'] at hy hs hW
      exact ih0 _ _ _ h0 _ hzl (inCone_subst hiz hy) ms Wn (agL_subst hiz hs) (agN_subst hiz hW) hwf hG hm
    · simp only [he, Int.reduceEq, ↓reduceIte] at hm
      rw [he] at hy'
      rw [hy'] at hy hs hW
      exact ih1 _ _ _ h1 _ hzl (inCone_subst hiz hy) ms Wn (agL_subst hiz hs) (agN_subst hiz hW) hwf hG hm
  | skew i j s t ih =>
    intro ss sW ts h y hlen hy ms Wn hs hW hwf hG hm
    simp only [HTree.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, hij⟩, ht⟩ := h
    have hy' := pt_skew_down y i j s hij (by omega)
    have hzl : (y.set i (y.getD i 0 - s * y.getD j 0)).length = k := by simp [hlen]
    have hiz : i < (y.set i (y.getD i 0 - s * y.getD j 0)).length := by simp; omega
    have hjz : j < (y.set i (y.getD i 0 - s * y.getD j 0)).length := by simp; omega
    simp only [HTree.haltMem] at hm
    rw [hy'] at hy hs hW
    exact ih _ _ _ ht _ hzl (inCone_skew hiz hjz hy) ms Wn (agL_skew hiz hjz hs) (agN_skew hiz hjz hW) hwf hG hm
  | cleave i c σ j0 j1 t0 t1 ih0 ih1 =>
    intro ss sW ts h y hlen hy ms Wn hs hW hwf hG hm
    simp only [HTree.ok, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨_, hσ⟩, hb⟩, h0⟩, h1⟩ := h
    have hb' : 0 ≤ σ * (y.getD i 0 - c) := by
      have := ltDec_sound _ _ ts Γ y hy false hb
      rw [eval_cleaveBnd, eval_const] at this
      simp only [Bool.false_eq_true, iff_false] at this
      omega
    simp only [HTree.haltMem] at hm
    by_cases hc : y.getD i 0 = c
    · simp only [hc, ↓reduceIte] at hm
      exact ih0 _ _ _ h0 y hlen (inCone_pin hc j0 hy) ms Wn (agL_pin hc hs) (agN_pin hc hW) hwf hG hm
    · simp only [hc, ↓reduceIte] at hm
      have hne : σ * (y.getD i 0 - c) ≠ 0 := Int.mul_ne_zero hσ (by omega)
      exact ih1 _ _ _ h1 y hlen (inCone_set hy j1 (by rw [eval_addc, eval_cleaveBnd]; omega)) ms Wn hs hW hwf hG hm

/-- A halting tree read off a pass-start tree: the same splits, skews and cleaves (rounds run along the way are
dropped, since the close run starts from the root's round start), and at a `close` or `cut` leaf a `halt` leaf where
the close run reaches the close on the leaf's class. -/
def HTree.ofPTree (k : Nat) : PTree → List SMark → YForm → List YForm → HTree
  | .cut, ss, sW, ts => if symCloseRun ts Γ fuel [] (YForm.const 1) ss sW then .halt else .open
  | .close, ss, sW, ts => if symCloseRun ts Γ fuel [] (YForm.const 1) ss sW then .halt else .open
  | .land, _, _, _ => .open
  | .clean, _, _, _ => .open
  | .adv t, ss, sW, ts => HTree.ofPTree k t ss sW ts
  | .split i t0 t1, ss, sW, ts =>
    if i < k then
      .split i (HTree.ofPTree k t0 (substL ss i 0) (sW.subst i 0) (substT ts i 0))
        (HTree.ofPTree k t1 (substL ss i 1) (sW.subst i 1) (substT ts i 1))
    else .open
  | .skew i j s t, ss, sW, ts =>
    if i < k ∧ j < k ∧ i ≠ j then .skew i j s (HTree.ofPTree k t (skewL ss i j s) (sW.skew i j s) (skewT ts i j s))
    else .open
  | .cleave i c σ j0 j1 t0 t1, ss, sW, ts =>
    if (decide (i < k) && σ != 0 && ltDec (cleaveBnd i c σ) (YForm.const 0) ts Γ == some false) = true then
      .cleave i c σ j0 j1 (HTree.ofPTree k t0 (pinL ss i c) (sW.pin i c) ((pinT ts i c).eraseIdx j0))
        (HTree.ofPTree k t1 ss sW (ts.set j1 ((cleaveBnd i c σ).addc (Γ - 1))))
    else .open

/-- **Every halting tree read off a pass-start tree passes the check.** -/
theorem HTree.ofPTree_ok (k : Nat) (t : PTree) : ∀ (ss : List SMark) (sW : YForm) (ts : List YForm),
    (HTree.ofPTree Γ fuel k t ss sW ts).ok Γ fuel k ss sW ts = true := by
  induction t with
  | cut =>
    intro ss sW ts
    simp only [HTree.ofPTree]
    split
    · rename_i h; exact h
    · rfl
  | close =>
    intro ss sW ts
    simp only [HTree.ofPTree]
    split
    · rename_i h; exact h
    · rfl
  | land => intro _ _ _; rfl
  | clean => intro _ _ _; rfl
  | adv t ih => intro ss sW ts; exact ih ss sW ts
  | split i t0 t1 ih0 ih1 =>
    intro ss sW ts
    simp only [HTree.ofPTree]
    split
    · rename_i hi
      simp only [HTree.ok, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hi, ih0 _ _ _⟩, ih1 _ _ _⟩
    · rfl
  | skew i j s t ih =>
    intro ss sW ts
    simp only [HTree.ofPTree]
    split
    · rename_i hc
      obtain ⟨hi, hj, hij⟩ := hc
      simp only [HTree.ok, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨hi, hj⟩, hij⟩, ih _ _ _⟩
    · rfl
  | cleave i c σ j0 j1 t0 t1 ih0 ih1 =>
    intro ss sW ts
    simp only [HTree.ofPTree]
    split
    · rename_i hc
      simp only [HTree.ok, Bool.and_eq_true] at hc ⊢
      exact ⟨⟨hc, ih0 _ _ _⟩, ih1 _ _ _⟩
    · rfl

end BB6.Sym
