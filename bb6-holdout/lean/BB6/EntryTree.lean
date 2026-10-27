import BB6.RouteExplore

/-!
# Route trees with entry leaves

A route tree (`BB6/RouteTree.lean`) follows the run from a two-marker state to the next clean tape.  On the way the
run may reach a pass start of the loop, and the tree then follows the loop's passes round by round, splitting on the
digits of the right end that each pass divides by 16, until the depth runs out.  This file lets a tree stop there
instead, at a leaf `entry`: a round start that passes a given test `chk` on the whole class (for the route trees of
`thm/RouteEntryTheorem.lean`, `entryOK`: a pass start from which the loop cannot close, `BB6/RouteEntry.lean`).

`RTree.okE` is the check `RTree.ok` with `entry` leaves checked by `chk`, and `RTree.soundE` the statement for the
machine: the run reaches a clean tape, or the start lies in a cut class, or the run reaches a round start of which
`chk` certifies a property `P` (`hchk`).  `RTree.exploreE` is the explorer `RTree.explore` that also stops a path at
the first round start that passes `chk`, and `exploreE_okE` proves that every tree it builds passes `RTree.okE`, so
`RTree.soundE` holds for it at every depth with nothing evaluated.  `exploreMassE` computes the measures and leaf counts
of the same exploration without building the tree (`exploreMassE_eq`).
-/

namespace BB6.Sym
open BB6

/-- The number of `entry` leaves. -/
def RTree.entries : RTree → Nat
  | .cut => 0
  | .clean => 0
  | .entry => 1
  | .adv _ t => t.entries
  | .split _ t0 t1 => t0.entries + t1.entries
  | .shear _ _ t => t.entries
  | .drop _ t => t.entries

/-- The measure of the `entry` leaves, as a numerator over 2^D (each split halves). -/
def RTree.entryMass : Nat → RTree → Nat
  | _, .cut => 0
  | _, .clean => 0
  | D, .entry => 2 ^ D
  | D, .adv _ t => t.entryMass D
  | D, .split _ t0 t1 => t0.entryMass (D - 1) + t1.entryMass (D - 1)
  | D, .shear _ _ t => t.entryMass D
  | D, .drop _ t => t.entryMass D

variable (Γ : Int) (fuel : Nat) (chk : List YForm → List SMark → YForm → Bool)

/-- The check: as `RTree.ok`, and an `entry` leaf is a round start that passes `chk` (on the class, with its cone). -/
def RTree.okE : RTree → Bool → List SMark → YForm → List YForm → Bool
  | .cut, _, _, _, _ => true
  | .clean, moved, ss, sW, _ => moved && symClean ss sW
  | .entry, _, ss, sW, ts => chk ts ss sW
  | .adv n t, moved, ss, sW, ts =>
    match symRoundsZ ts Γ fuel n ss sW with
    | some (.newRound ss' sW') => t.okE (moved || decide (0 < n)) ss' sW' ts
    | _ => false
  | .split i t0 t1, moved, ss, sW, ts =>
    decide (i < 2) && t0.okE moved (substL ss i 0) (sW.subst i 0) (substT ts i 0) &&
      t1.okE moved (substL ss i 1) (sW.subst i 1) (substT ts i 1)
  | .shear i s t, moved, ss, sW, ts => t.okE moved (shearL ss i s) (sW.shear i s) (shearT ts i s)
  | .drop _ _, _, _, _, _ => false

/-- **A checked route tree with entry leaves, for the machine.**  If `chk` certifies `P` (every round start that
agrees with a class passing `chk`, at a point of its cone, satisfies `P`), then at every point `y` of the root class
inside the cone, from a well-formed round start that agrees with the root, the machine runs `n` rounds of the mark
model to a round start without halting, and either that round start is a clean tape reached after at least one round,
or it satisfies `P`, or `y` lies in a `cut` leaf. -/
theorem RTree.soundE (P : List Mark → Nat → Prop)
    (hchk : ∀ (ts : List YForm) (ss : List SMark) (sW : YForm) (y : List Int) (ms : List Mark) (Wn : Nat),
      chk ts ss sW = true → y.length = 2 → inCone ts Γ y → agL y ss ms → agN y sW Wn → P ms Wn)
    (t : RTree) : ∀ (moved : Bool) (ss : List SMark) (sW : YForm) (ts : List YForm),
    t.okE Γ fuel chk moved ss sW ts = true → ∀ (y : List Int), y.length = 2 → inCone ts Γ y →
    ∀ (ms : List Mark) (Wn : Nat), agL y ss ms → agN y sW Wn → roundWF ms Wn →
    ∃ n k ms' Wn', roundsZ fuel n ms Wn = .newRound ms' Wn' ∧ steps k (roundStart ms Wn) = some (roundStart ms' Wn') ∧
      (t.cutMem y = true ∨ ((moved = true ∨ 0 < n) ∧ cleanTape ms' Wn') ∨ P ms' Wn') := by
  induction t with
  | cut =>
    intro moved ss sW ts _ y _ _ ms Wn _ _ _
    exact ⟨0, 0, ms, Wn, rfl, rfl, Or.inl rfl⟩
  | clean =>
    intro moved ss sW ts h y _ _ ms Wn hs hW _
    simp only [RTree.okE, Bool.and_eq_true] at h
    exact ⟨0, 0, ms, Wn, rfl, rfl, Or.inr (Or.inl ⟨Or.inl h.1, symClean_sound hs hW h.2⟩)⟩
  | entry =>
    intro moved ss sW ts h y hlen hy ms Wn hs hW _
    simp only [RTree.okE] at h
    exact ⟨0, 0, ms, Wn, rfl, rfl, Or.inr (Or.inr (hchk ts ss sW y ms Wn h hlen hy hs hW))⟩
  | adv n t ih =>
    intro moved ss sW ts h y hlen hy ms Wn hs hW hwf
    simp only [RTree.okE] at h
    cases hr : symRoundsZ ts Γ fuel n ss sW with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h
      cases r with
      | newRound ss' sW' =>
        simp only at h
        have hag := symRoundsZ_sound ts Γ hy fuel n ss ms sW Wn _ hs hW hr
        generalize hcr : roundsZ fuel n ms Wn = cr at hag
        cases cr with
        | newRound ms₁ W₁ =>
          obtain ⟨k₁, hk₁, hwf₁⟩ := rounds_run fuel n ms Wn hwf (by rw [hcr]; intro h; cases h)
          rw [hcr] at hk₁ hwf₁
          obtain ⟨n₂, k₂, ms', Wn', hr₂, hk₂, hc⟩ := ih _ _ _ _ h y hlen hy ms₁ W₁ hag.1 hag.2 hwf₁
          refine ⟨n + n₂, k₁ + k₂, ms', Wn', ?_, steps_seq_any hk₁ hk₂, ?_⟩
          · rw [roundsZ_add fuel n n₂ ms Wn ms₁ W₁ hcr]; exact hr₂
          · simp only [RTree.cutMem]
            rcases hc with hc | ⟨hm, hcl⟩ | hp
            · exact Or.inl hc
            · refine Or.inr (Or.inl ⟨?_, hcl⟩)
              simp only [Bool.or_eq_true, decide_eq_true_eq] at hm
              rcases hm with (hm | hm) | hm
              · exact Or.inl hm
              · exact Or.inr (by omega)
              · exact Or.inr (by omega)
            · exact Or.inr (Or.inr hp)
        | _ => exact absurd hag id
      | _ => simp at h
  | split i t0 t1 ih0 ih1 =>
    intro moved ss sW ts h y hlen hy ms Wn hs hW hwf
    simp only [RTree.okE, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h0⟩, h1⟩ := h
    have hiy : i < y.length := by omega
    have hy' := lift_half y i hiy
    have hzl : (y.set i (y.getD i 0 / 2)).length = 2 := by simp [hlen]
    have hiz : i < (y.set i (y.getD i 0 / 2)).length := by omega
    simp only [RTree.cutMem]
    rcases mod_two_cases (y.getD i 0) with he | he
    · rw [he] at hy'
      rw [hy'] at hy hs hW
      obtain ⟨n, k, ms', Wn', h1', h2', h3'⟩ := ih0 _ _ _ _ h0 _ hzl (inCone_subst hiz hy) ms Wn
        (agL_subst hiz hs) (agN_subst hiz hW) hwf
      exact ⟨n, k, ms', Wn', h1', h2', by rw [if_pos he]; exact h3'⟩
    · rw [he] at hy'
      rw [hy'] at hy hs hW
      obtain ⟨n, k, ms', Wn', h1', h2', h3'⟩ := ih1 _ _ _ _ h1 _ hzl (inCone_subst hiz hy) ms Wn
        (agL_subst hiz hs) (agN_subst hiz hW) hwf
      exact ⟨n, k, ms', Wn', h1', h2', by rw [if_neg (by omega)]; exact h3'⟩
  | shear i s t ih =>
    intro moved ss sW ts h y hlen hy ms Wn hs hW hwf
    simp only [RTree.okE] at h
    simp only [RTree.cutMem]
    have hz := length_shearDown y i s
    match hzz : shearDown y i s, hz with
    | [a, b], _ =>
      have hl := shearLift_down y hlen i s
      rw [hzz] at hl
      rw [← hl] at hy hs hW
      exact ih _ _ _ _ h [a, b] rfl (inCone_shear hy) ms Wn (agL_shear hs) (agN_shear hW) hwf
  | drop z t _ =>
    intro moved ss sW ts h
    simp [RTree.okE] at h

/-- Build a route tree (`S` steps, `d` splits) as `RTree.explore` does, and also stop a path at the first round start
that passes `chk` (an `entry` leaf). -/
def RTree.exploreE : Nat → Nat → Bool → List SMark → YForm → List YForm → RTree
  | 0, _, _, _, _, _ => .cut
  | S + 1, d, moved, ss, sW, ts =>
    if (moved && symClean ss sW) = true then .clean else
    if chk ts ss sW = true then .entry else
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => .adv 1 (RTree.exploreE S d true ss' sW' ts)
    | some _ => .cut
    | none =>
      match d with
      | 0 => .cut
      | d + 1 =>
        match splitStep ts Γ ss sW with
        | none => .cut
        | some (none, i) =>
          if i < 2 then
            .split i (RTree.exploreE S d moved (substL ss i 0) (sW.subst i 0) (substT ts i 0))
              (RTree.exploreE S d moved (substL ss i 1) (sW.subst i 1) (substT ts i 1))
          else .cut
        | some (some (j, s), i) =>
          if i < 2 then
            .shear j s (.split i
              (RTree.exploreE S d moved (substL (shearL ss j s) i 0) ((sW.shear j s).subst i 0)
                (substT (shearT ts j s) i 0))
              (RTree.exploreE S d moved (substL (shearL ss j s) i 1) ((sW.shear j s).subst i 1)
                (substT (shearT ts j s) i 1)))
          else .cut

/-- **Every explored route tree with entry leaves passes the check.** -/
theorem RTree.exploreE_okE : ∀ (S d : Nat) (moved : Bool) (ss : List SMark) (sW : YForm) (ts : List YForm),
    (RTree.exploreE Γ fuel chk S d moved ss sW ts).okE Γ fuel chk moved ss sW ts = true := by
  intro S
  induction S with
  | zero => intro d moved ss sW ts; rfl
  | succ S ih =>
    intro d moved ss sW ts
    simp only [RTree.exploreE]
    split
    · next hc => simpa [RTree.okE] using hc
    · split
      · next he => simpa [RTree.okE] using he
      · split
        · next ss' sW' hr => simp [RTree.okE, symRoundsZ, hr, ih]
        · rfl
        · split
          · rfl
          · split
            · rfl
            · split
              · next hi => simp [RTree.okE, hi, ih]
              · rfl
            · split
              · next hi => simp [RTree.okE, hi, ih]
              · rfl

/-- The measures and leaf counts of a route tree with entry leaves. -/
structure ETally where
  /-- the measure of the cut leaves, over 2^D -/
  cutMass : Nat
  /-- the numbers of cut, clean and entry leaves -/
  cuts : Nat
  cleans : Nat
  entries : Nat
  /-- the measure of the entry leaves, over 2^D -/
  entryMass : Nat
  deriving DecidableEq, Repr

def ETally.add (a b : ETally) : ETally :=
  ⟨a.cutMass + b.cutMass, a.cuts + b.cuts, a.cleans + b.cleans, a.entries + b.entries, a.entryMass + b.entryMass⟩

/-- The measures and leaf counts of `RTree.exploreE`, without the tree. -/
def exploreMassE : Nat → Nat → Nat → Bool → List SMark → YForm → List YForm → ETally
  | 0, _, D, _, _, _, _ => ⟨2 ^ D, 1, 0, 0, 0⟩
  | S + 1, d, D, moved, ss, sW, ts =>
    if (moved && symClean ss sW) = true then ⟨0, 0, 1, 0, 0⟩ else
    if chk ts ss sW = true then ⟨0, 0, 0, 1, 2 ^ D⟩ else
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => exploreMassE S d D true ss' sW' ts
    | some _ => ⟨2 ^ D, 1, 0, 0, 0⟩
    | none =>
      match d with
      | 0 => ⟨2 ^ D, 1, 0, 0, 0⟩
      | d + 1 =>
        match splitStep ts Γ ss sW with
        | none => ⟨2 ^ D, 1, 0, 0, 0⟩
        | some (none, i) =>
          if i < 2 then
            (exploreMassE S d (D - 1) moved (substL ss i 0) (sW.subst i 0) (substT ts i 0)).add
              (exploreMassE S d (D - 1) moved (substL ss i 1) (sW.subst i 1) (substT ts i 1))
          else ⟨2 ^ D, 1, 0, 0, 0⟩
        | some (some (j, s), i) =>
          if i < 2 then
            (exploreMassE S d (D - 1) moved (substL (shearL ss j s) i 0) ((sW.shear j s).subst i 0)
                (substT (shearT ts j s) i 0)).add
              (exploreMassE S d (D - 1) moved (substL (shearL ss j s) i 1) ((sW.shear j s).subst i 1)
                (substT (shearT ts j s) i 1))
          else ⟨2 ^ D, 1, 0, 0, 0⟩

theorem exploreMassE_eq : ∀ (S d D : Nat) (moved : Bool) (ss : List SMark) (sW : YForm) (ts : List YForm),
    exploreMassE Γ fuel chk S d D moved ss sW ts =
      ⟨(RTree.exploreE Γ fuel chk S d moved ss sW ts).cutMass D,
        (RTree.exploreE Γ fuel chk S d moved ss sW ts).leaves.1,
        (RTree.exploreE Γ fuel chk S d moved ss sW ts).leaves.2,
        (RTree.exploreE Γ fuel chk S d moved ss sW ts).entries,
        (RTree.exploreE Γ fuel chk S d moved ss sW ts).entryMass D⟩ := by
  intro S
  induction S with
  | zero => intro d D moved ss sW ts; rfl
  | succ S ih =>
    intro d D moved ss sW ts
    simp only [exploreMassE, RTree.exploreE]
    split
    · rfl
    · split
      · rfl
      · split
        · simp only [RTree.cutMass, RTree.leaves, RTree.entries, RTree.entryMass]; exact ih _ _ _ _ _ _
        · rfl
        · split
          · rfl
          · split
            · rfl
            · split
              · simp only [RTree.cutMass, RTree.leaves, RTree.entries, RTree.entryMass, ih, ETally.add]
              · rfl
            · split
              · simp only [RTree.cutMass, RTree.leaves, RTree.entries, RTree.entryMass, ih, ETally.add]
              · rfl

end BB6.Sym
