import BB6.RouteExplore

/-!
# Clean tapes run one by one

`clean_tree_step` makes no claim for the clean tapes in the cut classes.  Below a bound on the width, a cut class has
few members, and each can be run directly: from the clean tape of width W, rounds of the mark model until a
one-marker clean tape wider than W (`toWider`, `directOK`).  `RTree.cuts1` lists the cut classes of a tree that splits
only on the first coordinate as residues, `rangeOK` runs every member of every cut class in a range of widths, and
`rangeOK_sound` turns it into: every clean tape in the range that the tree leaves open reaches a wider clean tape.
This is how the exhaustive check (`../csearch/nrefdfs2.c`) covers the small members of its open classes.
-/

namespace BB6.Sym
open BB6

/-! ## Direct runs (`toWider`, `BB6/CleanTree.lean`) -/

/-- From the clean tape of width `W`, the model reaches a wider one-marker clean tape within 10,000 rounds. -/
def directOK (W : Nat) : Bool := toWider 1000 W 10000 [⟨.M, W - 2⟩] W

theorem directOK_sound {W : Nat} (h6 : 6 ≤ W) (hW : W % 2 = 0) (h : directOK W = true) :
    ∃ n k W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound [⟨.M, W' - 2⟩] W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧ 0 < n ∧ W < W' := by
  obtain ⟨n, W', hn, hr, hlt⟩ := toWider_sound 1000 W 10000 _ _ h
  obtain ⟨k, hk, -⟩ := rounds_run 1000 n _ _ (roundWF_one.mpr ⟨h6, hW⟩) (by rw [hr]; intro h; cases h)
  rw [hr] at hk
  exact ⟨n, k, W', hr, hk, hn, hlt⟩

/-! ## The cut classes of a one-variable tree -/

/-- The cut classes of a tree that splits only on coordinate 0 and has no shears, as pairs (r, k): the class
y₀ ≡ r (mod 2^k).  The arguments are the residue and the depth of the node; `none` for any other tree. -/
def RTree.cuts1 : RTree → Nat → Nat → Option (List (Nat × Nat))
  | .cut, r, k => some [(r, k)]
  | .clean, _, _ => some []
  | .adv _ t, r, k => t.cuts1 r k
  | .split i t0 t1, r, k =>
    if i = 0 then
      match t0.cuts1 r (k + 1), t1.cuts1 (r + 2 ^ k) (k + 1) with
      | some a, some b => some (a ++ b)
      | _, _ => none
    else none
  | .shear _ _ _, _, _ => none
  | .drop _ t, r, k => t.cuts1 r k

theorem RTree.cuts1_sound (t : RTree) : ∀ (r k : Nat) (L : List (Nat × Nat)), t.cuts1 r k = some L → r < 2 ^ k →
    ∀ (a : Nat), t.cutMem [(a : Int), 0] = true → ∃ p ∈ L, (r + 2 ^ k * a) % 2 ^ p.2 = p.1 := by
  induction t with
  | cut =>
    intro r k L h hr a _
    simp only [RTree.cuts1, Option.some.injEq] at h
    subst h
    refine ⟨(r, k), List.mem_singleton.mpr rfl, ?_⟩
    simp only
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  | clean =>
    intro r k L _ _ a hc
    simp [RTree.cutMem] at hc
  | adv n t ih =>
    intro r k L h hr a hc
    simp only [RTree.cuts1] at h
    simp only [RTree.cutMem] at hc
    exact ih r k L h hr a hc
  | split i t0 t1 ih0 ih1 =>
    intro r k L h hr a hc
    simp only [RTree.cuts1] at h
    split at h
    · next hi =>
      subst hi
      split at h
      · next la lb h0 h1 =>
        simp only [Option.some.injEq] at h
        subst h
        simp only [RTree.cutMem, List.getD_cons_zero, List.set_cons_zero] at hc
        have hdiv : (a : Int) / 2 = ((a / 2 : Nat) : Int) := by omega
        rw [hdiv] at hc
        by_cases he : a % 2 = 0
        · rw [ite_eq_left (by omega)] at hc
          obtain ⟨p, hp, hpe⟩ := ih0 r (k + 1) la h0 (by omega) (a / 2) hc
          refine ⟨p, List.mem_append_left _ hp, ?_⟩
          have : 2 ^ (k + 1) * (a / 2) = 2 ^ k * a := by
            rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero he)]
          rw [this] at hpe
          exact hpe
        · rw [ite_eq_right (by omega)] at hc
          obtain ⟨p, hp, hpe⟩ := ih1 (r + 2 ^ k) (k + 1) lb h1 (by omega) (a / 2) hc
          refine ⟨p, List.mem_append_right _ hp, ?_⟩
          have : r + 2 ^ k + 2 ^ (k + 1) * (a / 2) = r + 2 ^ k * a := by
            have ha : a = 2 * (a / 2) + 1 := by omega
            conv => rhs; rw [ha]
            rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_add, Nat.mul_one]
            omega
          rw [this] at hpe
          exact hpe
      · cases h
    · cases h
  | shear i s t ih =>
    intro r k L h
    simp [RTree.cuts1] at h
  | drop z t ih =>
    intro r k L h hr a hc
    simp only [RTree.cuts1] at h
    simp only [RTree.cutMem, List.getD_cons_zero] at hc
    split at hc
    · cases hc
    · exact ih r k L h hr a hc

/-! ## Running every member of every cut class in a range -/

/-- Every member y = r + 2^k·j of the class (r, k) with lo ≤ 2y < hi passes `directOK (2y)`. -/
def classOK (lo hi r k : Nat) : Bool :=
  (List.range (hi / 2 ^ (k + 1) + 1)).all fun j =>
    let W := 2 * (r + 2 ^ k * j)
    !(decide (lo ≤ W) && decide (W < hi)) || directOK W

theorem classOK_sound {lo hi r k : Nat} (h : classOK lo hi r k = true) (y : Nat) (hy : y % 2 ^ k = r)
    (h1 : lo ≤ 2 * y) (h2 : 2 * y < hi) : directOK (2 * y) = true := by
  unfold classOK at h
  rw [List.all_eq_true] at h
  have hy' : r + 2 ^ k * (y / 2 ^ k) = y := by rw [← hy]; exact Nat.mod_add_div y (2 ^ k)
  have hj : y / 2 ^ k < hi / 2 ^ (k + 1) + 1 := by
    have hle : 2 ^ k * (y / 2 ^ k) ≤ y := Nat.mul_div_le y (2 ^ k)
    have : y / 2 ^ k ≤ hi / 2 ^ (k + 1) := by
      rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos (k + 1)), Nat.pow_succ, ← Nat.mul_assoc,
        Nat.mul_comm (y / 2 ^ k) (2 ^ k), Nat.mul_comm _ 2]
      omega
    omega
  have := h (y / 2 ^ k) (List.mem_range.mpr hj)
  simp only [hy', Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
  rcases this with (h3 | h3) | h3
  · exact absurd h1 h3
  · exact absurd h2 h3
  · exact h3

/-- Every clean tape of width in [lo, hi) that the tree leaves open runs directly to a wider one. -/
def rangeOK (lo hi : Nat) (t : RTree) : Bool :=
  match t.cuts1 0 0 with
  | some L => L.all fun p => classOK lo hi p.1 p.2
  | none => false

theorem rangeOK_sound {lo hi : Nat} {t : RTree} (h : rangeOK lo hi t = true) (W : Nat) (hW : W % 2 = 0)
    (h1 : lo ≤ W) (h2 : W < hi) (hc : t.cutMem [(W : Int) / 2, 0] = true) : directOK W = true := by
  unfold rangeOK at h
  split at h
  · next L hL =>
    have hdiv : (W : Int) / 2 = ((W / 2 : Nat) : Int) := by omega
    rw [hdiv] at hc
    obtain ⟨p, hp, hpe⟩ := RTree.cuts1_sound t 0 0 L hL (by decide) (W / 2) hc
    simp only [Nat.pow_zero, Nat.one_mul, Nat.zero_add] at hpe
    rw [List.all_eq_true] at h
    have := classOK_sound (h p hp) (W / 2) hpe (by omega) (by omega)
    rwa [show 2 * (W / 2) = W by omega] at this
  · cases h

end BB6.Sym
