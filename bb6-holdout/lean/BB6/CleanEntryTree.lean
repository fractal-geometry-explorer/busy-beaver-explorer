import BB6.EntryTree
import BB6.RouteEntry

/-!
# Clean-tape trees with entry leaves

A clean-tape tree (`BB6/CleanTree.lean`, `RTree.okW`) follows the run from a clean tape to a wider one.  On the way the
run may reach a pass start of the loop, and the tree then follows the loop's passes round by round, splitting on the
digits of W/2 that each pass consumes, until the depth runs out.  This file lets a clean-tape tree stop there instead,
at a leaf `entry`: a round start that passes a given test `chk` on the whole class (with the start's width `w0`, so
that the test can also decide that the entry is wider than the start).

`RTree.okWE` is the check `RTree.okW` with `entry` leaves checked by `chk`, and `RTree.soundWE` the statement for the
machine: the run reaches a wider clean tape, or the start lies in a cut class, or the run reaches a round start of
which `chk` certifies a property `P` (`hchk`).  `RTree.exploreWE` is the explorer `RTree.exploreW` that also stops a
path at the first round start that passes `chk`, and `exploreWE_okWE` proves that every tree it builds passes
`RTree.okWE`, so `RTree.soundWE` holds for it at every depth with nothing evaluated.  `exploreMassWE` computes the
measures and leaf counts of the same exploration without building the tree (`exploreMassWE_eq`).
-/

namespace BB6.Sym
open BB6

variable (Γ : Int) (fuel : Nat) (chk : List YForm → List SMark → YForm → YForm → Bool)

/-- The check: as `RTree.okW`, and an `entry` leaf is a round start that passes `chk` (on the class, with the start's
width and the cone). -/
def RTree.okWE : RTree → Bool → List SMark → YForm → YForm → List YForm → Bool
  | .cut, _, _, _, _, _ => true
  | .clean, moved, ss, sW, w0, ts => moved && symClean1 ss sW && widerB sW w0 ts Γ
  | .entry, _, ss, sW, w0, ts => chk ts ss sW w0
  | .adv n t, moved, ss, sW, w0, ts =>
    match symRoundsZ ts Γ fuel n ss sW with
    | some (.newRound ss' sW') => t.okWE (moved || decide (0 < n)) ss' sW' w0 ts
    | _ => false
  | .split i t0 t1, moved, ss, sW, w0, ts =>
    decide (i < 2) && t0.okWE moved (substL ss i 0) (sW.subst i 0) (w0.subst i 0) (substT ts i 0) &&
      t1.okWE moved (substL ss i 1) (sW.subst i 1) (w0.subst i 1) (substT ts i 1)
  | .shear i s t, moved, ss, sW, w0, ts => t.okWE moved (shearL ss i s) (sW.shear i s) (w0.shear i s) (shearT ts i s)
  | .drop z t, moved, ss, sW, w0, ts => dropOK Γ fuel z ss sW w0 ts && t.okWE moved ss sW w0 [dropCone Γ z]

/-- **A checked clean-tape tree with entry leaves, for the machine.**  If `chk` certifies `P` (every round start
that agrees with a class passing `chk`, at a point of its cone, satisfies `P` with the start's width), then at every
point `y` of the root class inside the cone, from a well-formed round start that agrees with the root (width `Wn`;
`W0` the value of `w0`), the machine runs `n` rounds of the mark model to a round start without halting, and either
that round start is a one-marker clean tape, reached after at least one round, of width larger than `W0`, or it
satisfies `P`, or `y` lies in a `cut` leaf. -/
theorem RTree.soundWE (P : List Mark → Nat → Nat → Prop)
    (hchk : ∀ (ts : List YForm) (ss : List SMark) (sW w0 : YForm) (y : List Int) (ms : List Mark) (Wn W0 : Nat),
      chk ts ss sW w0 = true → y.length = 2 → inCone ts Γ y → agL y ss ms → agN y sW Wn → agN y w0 W0 →
      P ms Wn W0)
    (t : RTree) : ∀ (moved : Bool) (ss : List SMark) (sW w0 : YForm) (ts : List YForm),
    t.okWE Γ fuel chk moved ss sW w0 ts = true → ∀ (y : List Int), y.length = 2 → inCone ts Γ y →
    ∀ (ms : List Mark) (Wn W0 : Nat), agL y ss ms → agN y sW Wn → agN y w0 W0 → roundWF ms Wn →
    ∃ n k ms' Wn', roundsZ fuel n ms Wn = .newRound ms' Wn' ∧ steps k (roundStart ms Wn) = some (roundStart ms' Wn') ∧
      (t.cutMem y = true ∨ ((moved = true ∨ 0 < n) ∧ ms' = [⟨.M, Wn' - 2⟩] ∧ W0 < Wn') ∨ P ms' Wn' W0) := by
  induction t with
  | cut =>
    intro moved ss sW w0 ts _ y _ _ ms Wn W0 _ _ _ _
    exact ⟨0, 0, ms, Wn, rfl, rfl, Or.inl rfl⟩
  | clean =>
    intro moved ss sW w0 ts h y _ hy ms Wn W0 hs hW h0 _
    simp only [RTree.okWE, Bool.and_eq_true] at h
    obtain ⟨⟨hm, hc⟩, hw⟩ := h
    exact ⟨0, 0, ms, Wn, rfl, rfl,
      Or.inr (Or.inl ⟨Or.inl hm, (symClean1_sound hs hW hc).2, widerB_sound hy hW h0 hw⟩)⟩
  | entry =>
    intro moved ss sW w0 ts h y hlen hy ms Wn W0 hs hW h0 _
    simp only [RTree.okWE] at h
    exact ⟨0, 0, ms, Wn, rfl, rfl, Or.inr (Or.inr (hchk ts ss sW w0 y ms Wn W0 h hlen hy hs hW h0))⟩
  | adv n t ih =>
    intro moved ss sW w0 ts h y hlen hy ms Wn W0 hs hW h0 hwf
    simp only [RTree.okWE] at h
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
          obtain ⟨n₂, k₂, ms', Wn', hr₂, hk₂, hc⟩ := ih _ _ _ _ _ h y hlen hy ms₁ W₁ W0 hag.1 hag.2 h0 hwf₁
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
    intro moved ss sW w0 ts h y hlen hy ms Wn W0 hs hW h0 hwf
    simp only [RTree.okWE, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h0'⟩, h1⟩ := h
    have hiy : i < y.length := by omega
    have hy' := lift_half y i hiy
    have hzl : (y.set i (y.getD i 0 / 2)).length = 2 := by simp [hlen]
    have hiz : i < (y.set i (y.getD i 0 / 2)).length := by omega
    simp only [RTree.cutMem]
    rcases mod_two_cases (y.getD i 0) with he | he
    · rw [he] at hy'
      rw [hy'] at hy hs hW h0
      obtain ⟨n, k, ms', Wn', h1', h2', h3'⟩ := ih0 _ _ _ _ _ h0' _ hzl (inCone_subst hiz hy) ms Wn W0
        (agL_subst hiz hs) (agN_subst hiz hW) (agN_subst hiz h0) hwf
      exact ⟨n, k, ms', Wn', h1', h2', by rw [if_pos he]; exact h3'⟩
    · rw [he] at hy'
      rw [hy'] at hy hs hW h0
      obtain ⟨n, k, ms', Wn', h1', h2', h3'⟩ := ih1 _ _ _ _ _ h1 _ hzl (inCone_subst hiz hy) ms Wn W0
        (agL_subst hiz hs) (agN_subst hiz hW) (agN_subst hiz h0) hwf
      exact ⟨n, k, ms', Wn', h1', h2', by rw [if_neg (by omega)]; exact h3'⟩
  | shear i s t ih =>
    intro moved ss sW w0 ts h y hlen hy ms Wn W0 hs hW h0 hwf
    simp only [RTree.okWE] at h
    simp only [RTree.cutMem]
    have hz := length_shearDown y i s
    match hzz : shearDown y i s, hz with
    | [a, b], _ =>
      have hl := shearLift_down y hlen i s
      rw [hzz] at hl
      rw [← hl] at hy hs hW h0
      exact ih _ _ _ _ _ h [a, b] rfl (inCone_shear hy) ms Wn W0 (agL_shear hs) (agN_shear hW) (agN_shear h0) hwf
  | drop z t ih =>
    intro moved ss sW w0 ts h y hlen hy ms Wn W0 hs hW h0 hwf
    simp only [RTree.okWE, Bool.and_eq_true] at h
    obtain ⟨hd, ht⟩ := h
    obtain ⟨a, b, rfl⟩ := two_cases y hlen
    have hza : z ≤ a := coneFrom_sound (dropOK_cone hd) hy
    simp only [RTree.cutMem, List.getD_cons_zero]
    by_cases hz : a = z
    · subst hz
      obtain ⟨n, W', hn, hr, hlt⟩ := dropOK_sound hd hs hW h0
      obtain ⟨k, hk, -⟩ := rounds_run fuel n ms Wn hwf (by rw [hr]; intro h; cases h)
      rw [hr] at hk
      exact ⟨n, k, _, W', hr, hk, Or.inr (Or.inl ⟨Or.inr hn, rfl, hlt⟩)⟩
    · obtain ⟨n, k, ms', Wn', h1, h2, h3⟩ :=
        ih _ _ _ _ _ ht [a, b] rfl (inCone_dropCone (by omega)) ms Wn W0 hs hW h0 hwf
      exact ⟨n, k, ms', Wn', h1, h2, by rw [if_neg hz]; exact h3⟩

variable (B : Nat)

/-- Build a clean-tape tree as `RTree.exploreW` does (`S` steps, `d` splits, `nd` drops left in the class, `B` drops
for each split's children), and also stop a path at the first round start that passes `chk` (an `entry` leaf). -/
def RTree.exploreWE : Nat → Nat → Nat → Bool → List SMark → YForm → YForm → List YForm → RTree
  | 0, _, _, _, _, _, _, _ => .cut
  | S + 1, d, nd, moved, ss, sW, w0, ts =>
    if (moved && symClean1 ss sW && widerB sW w0 ts Γ) = true then .clean else
    if chk ts ss sW w0 = true then .entry else
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => .adv 1 (RTree.exploreWE S d nd true ss' sW' w0 ts)
    | some _ => .cut
    | none =>
      match splitStep ts Γ ss sW with
      | none =>
        match nd, coneMin ts Γ with
        | nd + 1, some z =>
          if dropOK Γ fuel z ss sW w0 ts = true then
            .drop z (RTree.exploreWE S d nd moved ss sW w0 [dropCone Γ z])
          else .cut
        | _, _ => .cut
      | some (none, i) =>
        match d with
        | 0 => .cut
        | d + 1 =>
          if i < 2 then
            .split i (RTree.exploreWE S d B moved (substL ss i 0) (sW.subst i 0) (w0.subst i 0) (substT ts i 0))
              (RTree.exploreWE S d B moved (substL ss i 1) (sW.subst i 1) (w0.subst i 1) (substT ts i 1))
          else .cut
      | some (some (j, s), i) =>
        match d with
        | 0 => .cut
        | d + 1 =>
          if i < 2 then
            .shear j s (.split i
              (RTree.exploreWE S d B moved (substL (shearL ss j s) i 0) ((sW.shear j s).subst i 0)
                ((w0.shear j s).subst i 0) (substT (shearT ts j s) i 0))
              (RTree.exploreWE S d B moved (substL (shearL ss j s) i 1) ((sW.shear j s).subst i 1)
                ((w0.shear j s).subst i 1) (substT (shearT ts j s) i 1)))
          else .cut

/-- **Every explored clean-tape tree with entry leaves passes the check.** -/
theorem RTree.exploreWE_okWE : ∀ (S d nd : Nat) (moved : Bool) (ss : List SMark) (sW w0 : YForm) (ts : List YForm),
    (RTree.exploreWE Γ fuel chk B S d nd moved ss sW w0 ts).okWE Γ fuel chk moved ss sW w0 ts = true := by
  intro S
  induction S with
  | zero => intro d nd moved ss sW w0 ts; rfl
  | succ S ih =>
    intro d nd moved ss sW w0 ts
    simp only [RTree.exploreWE]
    split
    · next hc => simpa [RTree.okWE] using hc
    · split
      · next he => simpa [RTree.okWE] using he
      · split
        · next ss' sW' hr => simp [RTree.okWE, symRoundsZ, hr, ih]
        · rfl
        · split
          · split
            · split
              · next hd => simp [RTree.okWE, hd, ih]
              · rfl
            · rfl
          · split
            · rfl
            · split
              · next hi => simp [RTree.okWE, hi, ih]
              · rfl
          · split
            · rfl
            · split
              · next hi => simp [RTree.okWE, hi, ih]
              · rfl

/-- The measures and leaf counts of `RTree.exploreWE`, without the tree. -/
def exploreMassWE : Nat → Nat → Nat → Nat → Bool → List SMark → YForm → YForm → List YForm → ETally
  | 0, _, _, D, _, _, _, _, _ => ⟨2 ^ D, 1, 0, 0, 0⟩
  | S + 1, d, nd, D, moved, ss, sW, w0, ts =>
    if (moved && symClean1 ss sW && widerB sW w0 ts Γ) = true then ⟨0, 0, 1, 0, 0⟩ else
    if chk ts ss sW w0 = true then ⟨0, 0, 0, 1, 2 ^ D⟩ else
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => exploreMassWE S d nd D true ss' sW' w0 ts
    | some _ => ⟨2 ^ D, 1, 0, 0, 0⟩
    | none =>
      match splitStep ts Γ ss sW with
      | none =>
        match nd, coneMin ts Γ with
        | nd + 1, some z =>
          if dropOK Γ fuel z ss sW w0 ts = true then
            exploreMassWE S d nd D moved ss sW w0 [dropCone Γ z]
          else ⟨2 ^ D, 1, 0, 0, 0⟩
        | _, _ => ⟨2 ^ D, 1, 0, 0, 0⟩
      | some (none, i) =>
        match d with
        | 0 => ⟨2 ^ D, 1, 0, 0, 0⟩
        | d + 1 =>
          if i < 2 then
            (exploreMassWE S d B (D - 1) moved (substL ss i 0) (sW.subst i 0) (w0.subst i 0)
                (substT ts i 0)).add
              (exploreMassWE S d B (D - 1) moved (substL ss i 1) (sW.subst i 1) (w0.subst i 1)
                (substT ts i 1))
          else ⟨2 ^ D, 1, 0, 0, 0⟩
      | some (some (j, s), i) =>
        match d with
        | 0 => ⟨2 ^ D, 1, 0, 0, 0⟩
        | d + 1 =>
          if i < 2 then
            (exploreMassWE S d B (D - 1) moved (substL (shearL ss j s) i 0) ((sW.shear j s).subst i 0)
                ((w0.shear j s).subst i 0) (substT (shearT ts j s) i 0)).add
              (exploreMassWE S d B (D - 1) moved (substL (shearL ss j s) i 1) ((sW.shear j s).subst i 1)
                ((w0.shear j s).subst i 1) (substT (shearT ts j s) i 1))
          else ⟨2 ^ D, 1, 0, 0, 0⟩

theorem exploreMassWE_eq : ∀ (S d nd D : Nat) (moved : Bool) (ss : List SMark) (sW w0 : YForm) (ts : List YForm),
    exploreMassWE Γ fuel chk B S d nd D moved ss sW w0 ts =
      ⟨(RTree.exploreWE Γ fuel chk B S d nd moved ss sW w0 ts).cutMass D,
        (RTree.exploreWE Γ fuel chk B S d nd moved ss sW w0 ts).leaves.1,
        (RTree.exploreWE Γ fuel chk B S d nd moved ss sW w0 ts).leaves.2,
        (RTree.exploreWE Γ fuel chk B S d nd moved ss sW w0 ts).entries,
        (RTree.exploreWE Γ fuel chk B S d nd moved ss sW w0 ts).entryMass D⟩ := by
  intro S
  induction S with
  | zero => intro d nd D moved ss sW w0 ts; rfl
  | succ S ih =>
    intro d nd D moved ss sW w0 ts
    simp only [exploreMassWE, RTree.exploreWE]
    split
    · rfl
    · split
      · rfl
      · split
        · simp only [RTree.cutMass, RTree.leaves, RTree.entries, RTree.entryMass]; exact ih _ _ _ _ _ _ _ _
        · rfl
        · split
          · split
            · split
              · simp only [RTree.cutMass, RTree.leaves, RTree.entries, RTree.entryMass]; exact ih _ _ _ _ _ _ _ _
              · rfl
            · rfl
          · split
            · rfl
            · split
              · simp only [RTree.cutMass, RTree.leaves, RTree.entries, RTree.entryMass, ih, ETally.add]
              · rfl
          · split
            · rfl
            · split
              · simp only [RTree.cutMass, RTree.leaves, RTree.entries, RTree.entryMass, ih, ETally.add]
              · rfl

/-! ## The loop entries of the clean-tape trees -/

/-- The entry check of the clean-tape trees: `entryOK` (a pass start from which the loop cannot close, decided on the
class), and the entry is decided to be wider than the start. -/
def cleanEntryOK (Γ : Int) (ts : List YForm) (ss : List SMark) (sW w0 : YForm) : Bool :=
  entryOK Γ ts ss sW && widerB sW w0 ts Γ

theorem cleanEntryOK_sound {Γ : Int} {ts : List YForm} {ss : List SMark} {sW w0 : YForm}
    (h : cleanEntryOK Γ ts ss sW w0 = true) {y : List Int} (hlen : y.length = 2) (hy : inCone ts Γ y)
    {ms : List Mark} {W W0 : Nat} (hs : agL y ss ms) (hW : agN y sW W) (h0 : agN y w0 W0) :
    EntryNoClose ms W ∧ W0 < W := by
  simp only [cleanEntryOK, Bool.and_eq_true] at h
  exact ⟨entryOK_sound h.1 hlen hy hs hW, widerB_sound hy hW h0 h.2⟩

end BB6.Sym
