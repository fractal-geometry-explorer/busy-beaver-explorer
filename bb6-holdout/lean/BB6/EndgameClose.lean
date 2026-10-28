import BB6.Ends

/-!
# Stretches from a pass start through an end meeting at distance 2

An end meeting at distance 2 is not a close by itself.  The end-meeting chain puts the next meeting at (2 − 2)/2 = 0,
the close; when the next meeting is anywhere else, the run has left the halving chain.  `Tree.okEndC` checks an
endgame tree as `Tree.okEnd` does, but it lets an end meeting be at distance 2, provided the leaf's run then ends where
it has left phase 0 or the halving chain at a round start that is not three walls.  Such a run does not end at a
landing of the loop's chain, where the chain would be followed on.  Close leaves still show the left countdown in a
class.  `Tree.soundEndC` is the statement for the machine (`EndEventC`): either the run ends at an end event with every
end meeting at distance at least 3, as in `Tree.soundEnd`, or every end meeting is at distance at least 2 and the run
has left phase 0 or the halving chain, at a round start that is not three walls.
-/

namespace BB6

/-- Where a stretch from a pass start of width E with right end R and left countdown L may end when end meetings at
distance 2 are passed, after n rounds with end meetings `ds`, at the round start `ms`, `W`: an end event with every
end meeting at distance at least 3 (no close), or, with every end meeting at distance at least 2, a round start that
is not three walls after the run left phase 0 or the halving chain. -/
def EndEventC (E R : Nat) (L : Int) (n : Nat) (ds : List Nat) (ms : List Mark) (W : Nat) : Prop :=
  ((∀ d ∈ ds, 3 ≤ d) ∧ EndEvent E R L n ds ms W) ∨ ((∀ d ∈ ds, 2 ≤ d) ∧ (LeftPhase0 n ms ∨ ChainBreak ds) ∧ NotWWW ms)

namespace EndEventC

variable {E R : Nat} {L : Int} {n : Nat} {ds : List Nat} {ms : List Mark} {W : Nat}

/-- Every end meeting is at distance at least 2. -/
theorem ge2 (h : EndEventC E R L n ds ms W) : ∀ d ∈ ds, 2 ≤ d := by
  rcases h with ⟨h3, -⟩ | ⟨h2, -⟩
  · exact fun d hd => Nat.le_trans (by decide) (h3 d hd)
  · exact h2

/-- It is an end event. -/
theorem endEvent (h : EndEventC E R L n ds ms W) : EndEvent E R L n ds ms W := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact h
  · exact Or.inl h

end EndEventC

end BB6

namespace BB6.Sym
open BB6

section
variable (ts : List YForm) (Γ : Int)

/-- Every distance is at least 2 on the cone. -/
def allGe2 (ds : List YForm) : Bool := ds.all (fun d => ltDec d (YForm.const 2) ts Γ == some false)

theorem allGe2_sound {y : List Int} (hy : inCone ts Γ y) :
    ∀ {ds : List YForm} {ns : List Nat}, agLN y ds ns → allGe2 ts Γ ds = true → ∀ n ∈ ns, 2 ≤ n
  | [], [], _, _, n, hn => by simp at hn
  | d :: ds, m :: ns, h, ha, n, hn => by
    simp only [allGe2, List.all_cons, Bool.and_eq_true, beq_iff_eq] at ha
    have hl := lt_of_ltDec hy h.1 (agN_const y 2) ha.1
    simp only [List.mem_cons] at hn
    rcases hn with rfl | hn
    · have : ¬ n < 2 := fun h' => by simpa using hl.mp h'
      omega
    · exact allGe2_sound hy h.2 (by simpa [allGe2] using ha.2) n hn
  | [], _ :: _, h, _, _, _ => absurd h id
  | _ :: _, [], h, _, _, _ => absurd h id

/-- The run has left phase 0 or the halving chain, after `n` rounds with the end meeting forms `ds` (the last one
before the leaf's subtree first), at the round start `ss`, which is not three walls. -/
def leaveCheck (n : Nat) (ds : List YForm) (ss : List SMark) : Bool :=
  (leftP0Check n ss || brkList ts Γ ds) && (swwwOf ss).isNone

theorem leaveCheck_sound {y : List Int} (hy : inCone ts Γ y) {n : Nat} {last : Option YForm} {prev : List Nat}
    (hl : LastAg y last prev) {ds : List YForm} {ns : List Nat} (hd : agLN y ds ns) {ss : List SMark}
    {ms : List Mark} (hs : agL y ss ms) (h : leaveCheck ts Γ n (last.toList ++ ds) ss = true) :
    (LeftPhase0 n ms ∨ ChainBreak (prev ++ ns)) ∧ NotWWW ms := by
  simp only [leaveCheck, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨h | h, hn⟩ := h
  · exact ⟨Or.inl (leftP0Check_sound hs h), notWWW_of_none hs (Option.isNone_iff_eq_none.mp hn)⟩
  · exact ⟨Or.inr (brkLast_sound hy hl hd h), notWWW_of_none hs (Option.isNone_iff_eq_none.mp hn)⟩

end

/-! ## Endgame trees whose end meetings may be at distance 2 -/

variable (Γ : Int) (fuel : Nat)

/-- As `Tree.okEnd` for the endgame's end events, but every end meeting need only be decidedly at distance at least
2.  `low` records an end meeting before this subtree that is not decidedly at distance at least 3; at a leaf whose run
has such a meeting (before the subtree or in the leaf's own rounds), the run must end where it has left phase 0 or the
halving chain, at a round start that is not three walls (`leaveCheck`); at any other leaf, at an end event
(`evCheck`).  A close leaf shows the left countdown `f.L` decidedly in the class `cls`, as before. -/
def Tree.okEndC (k : Nat) (cls : Option (Int × Int)) :
    Tree → Bool → List SMark → YForm → List YForm → SForms → Nat → Option YForm → Bool → Bool
  | .leaf n, wf, ss, sW, ts, f, r0, last, low =>
    clsCheck cls f.L ||
    ((wf || symRightOK ts Γ (YForm.const 4) false sW ss) &&
     (match symMeetsRounds ts Γ fuel n ss sW with
      | some ds => allGe2 ts Γ ds &&
        (match symRoundsZ ts Γ fuel n ss sW with
         | some (.newRound ss' sW') =>
           bif low || !allGe3 ts Γ ds then leaveCheck ts Γ (r0 + n) (last.toList ++ ds) ss'
           else evCheck ts Γ .endgame (r0 + n) (last.toList ++ ds) f ss' sW'
         | _ => false)
      | none => false))
  | .adv n t, wf, ss, sW, ts, f, r0, last, low =>
    (wf || symRightOK ts Γ (YForm.const 4) false sW ss) &&
    (match symMeetsRounds ts Γ fuel n ss sW with
     | some ds => allGe2 ts Γ ds &&
       (match symRoundsZ ts Γ fuel n ss sW with
        | some (.newRound ss' sW') =>
          t.okEndC k cls true ss' sW' ts f (r0 + n) (lastOf last ds) (low || !allGe3 ts Γ ds)
        | _ => false)
     | none => false)
  | .node i t0 t1, wf, ss, sW, ts, f, r0, last, low =>
    decide (i < k) &&
      t0.okEndC k cls wf (substL ss i 0) (sW.subst i 0) (substT ts i 0) (f.subst i 0) r0
        (last.map (·.subst i 0)) low &&
      t1.okEndC k cls wf (substL ss i 1) (sW.subst i 1) (substT ts i 1) (f.subst i 1) r0
        (last.map (·.subst i 1)) low
  | .skew i j s t, wf, ss, sW, ts, f, r0, last, low =>
    decide (i < k) && decide (j < k) && decide (i ≠ j) &&
      t.okEndC k cls wf (skewL ss i j s) (sW.skew i j s) (skewT ts i j s) (f.skew i j s) r0
        (last.map (·.skew i j s)) low

variable {Γ fuel} in
theorem Tree.okEndC_node {k i : Nat} {cls : Option (Int × Int)} {wf : Bool} {t0 t1 : Tree} {es : EState}
    (hi : i < k)
    (h0 : t0.okEndC Γ fuel k cls wf (esSplit es i 0).1.1 (esSplit es i 0).1.2.1 (esSplit es i 0).1.2.2
      (esSplit es i 0).2 0 none false = true)
    (h1 : t1.okEndC Γ fuel k cls wf (esSplit es i 1).1.1 (esSplit es i 1).1.2.1 (esSplit es i 1).1.2.2
      (esSplit es i 1).2 0 none false = true) :
    (Tree.node i t0 t1).okEndC Γ fuel k cls wf es.1.1 es.1.2.1 es.1.2.2 es.2 0 none false = true := by
  simp only [Tree.okEndC, Bool.and_eq_true, decide_eq_true_eq, Option.map_none]; exact ⟨⟨hi, h0⟩, h1⟩

variable {Γ fuel} in
theorem Tree.okEndC_skew {k i j : Nat} {cls : Option (Int × Int)} {wf : Bool} {s : Int} {t : Tree} {es : EState}
    (hi : i < k) (hj : j < k) (hij : i ≠ j)
    (h : t.okEndC Γ fuel k cls wf (esSkew es i j s).1.1 (esSkew es i j s).1.2.1 (esSkew es i j s).1.2.2
      (esSkew es i j s).2 0 none false = true) :
    (Tree.skew i j s t).okEndC Γ fuel k cls wf es.1.1 es.1.2.1 es.1.2.2 es.2 0 none false = true := by
  simp only [Tree.okEndC, Bool.and_eq_true, decide_eq_true_eq, Option.map_none]; exact ⟨⟨⟨hi, hj⟩, hij⟩, h⟩

/-- **A checked end tree with end meetings at distance 2, for the machine.**  At every point of the root class inside
the cone, where the start's forms `f` take the values E, R and L, either the left countdown L is in the class `cls` (a
close leaf), or the machine runs from the round start for the rounds recorded on the way to the leaf without halting,
reaching a round start, every end meeting on the way is at distance at least 2, and either no end meeting before this
subtree (`low = false`) nor on the way is below 3 and the run ends at an end event (`EndEvent`), or the run ends where
it has left phase 0 or the halving chain, at a round start that is not three walls (`r0` rounds and the end meetings
`prev` before this subtree). -/
theorem Tree.soundEndC (k : Nat) (cls : Option (Int × Int)) (t : Tree) :
    ∀ (wf : Bool) (ss : List SMark) (sW : YForm) (ts : List YForm) (f : SForms) (r0 : Nat) (last : Option YForm)
      (low : Bool),
    t.okEndC Γ fuel k cls wf ss sW ts f r0 last low = true → ∀ (y : List Int), y.length = k → inCone ts Γ y →
    ∀ (ms : List Mark) (Wn E R : Nat) (L : Int) (prev : List Nat), agL y ss ms → agN y sW Wn → f.Ag y E R L →
    (wf = true → roundWF ms Wn) → LastAg y last prev →
    (∃ m c, cls = some (m, c) ∧ L % m = c) ∨
    ∃ n kk ms' Wn', steps kk (roundStart ms Wn) = some (roundStart ms' Wn') ∧
      roundsZ fuel n ms Wn = .newRound ms' Wn' ∧ (∀ d ∈ meetsRounds fuel n ms Wn, 2 ≤ d) ∧
      ((low = false ∧ (∀ d ∈ meetsRounds fuel n ms Wn, 3 ≤ d) ∧
          EndEvent E R L (r0 + n) (prev ++ meetsRounds fuel n ms Wn) ms' Wn') ∨
        ((LeftPhase0 (r0 + n) ms' ∨ ChainBreak (prev ++ meetsRounds fuel n ms Wn)) ∧ NotWWW ms')) := by
  induction t with
  | leaf n =>
    intro wf ss sW ts f r0 last low h y _ hy ms Wn E R L prev hs hW hf hwf hlast
    simp only [Tree.okEndC] at h
    rcases (Bool.or_eq_true _ _).mp h with hc | h'
    · left
      unfold clsCheck at hc
      cases hcls : cls with
      | none => rw [hcls] at hc; cases hc
      | some p =>
        obtain ⟨m, c⟩ := p
        rw [hcls] at hc
        simp only [beq_iff_eq] at hc
        exact ⟨m, c, rfl, by rw [hf.2.2]; exact eval_mod f.L m c hc y⟩
    · right
      simp only [Bool.and_eq_true] at h'
      obtain ⟨hwf', hmt⟩ := h'
      have hrwf := wf_of_check Γ hy hs hW hwf hwf'
      cases hmr : symMeetsRounds ts Γ fuel n ss sW with
      | none => rw [hmr] at hmt; cases hmt
      | some ds =>
        rw [hmr] at hmt
        simp only [Bool.and_eq_true] at hmt
        obtain ⟨hge2, hrun⟩ := hmt
        have hds := symMeetsRounds_sound ts Γ hy fuel n ss ms sW Wn ds hs hW hmr
        have hge := allGe2_sound ts Γ hy hds hge2
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
              refine ⟨n, kk, ms', Wn', hk, hcr, hge, ?_⟩
              cases hlow : (low || !allGe3 ts Γ ds) with
              | true =>
                simp only [hlow, Bool.cond_true] at hrun
                exact Or.inr (leaveCheck_sound ts Γ hy hlast hds hag.1 hrun)
              | false =>
                simp only [hlow, Bool.cond_false] at hrun
                simp only [Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at hlow
                exact Or.inl ⟨hlow.1, allGe3_sound ts Γ hy hds hlow.2,
                  evCheck_sound ts Γ .endgame hy hf hlast hds hag.1 hag.2 hrun⟩
            | _ => exact absurd hag id
          | _ => simp at hrun
  | adv n t ih =>
    intro wf ss sW ts f r0 last low h y hlen hy ms Wn E R L prev hs hW hf hwf hlast
    simp only [Tree.okEndC, Bool.and_eq_true] at h
    obtain ⟨hwf', hmt⟩ := h
    have hrwf := wf_of_check Γ hy hs hW hwf hwf'
    cases hmr : symMeetsRounds ts Γ fuel n ss sW with
    | none => rw [hmr] at hmt; cases hmt
    | some ds =>
      rw [hmr] at hmt
      simp only [Bool.and_eq_true] at hmt
      obtain ⟨hge2, hrun⟩ := hmt
      have hds := symMeetsRounds_sound ts Γ hy fuel n ss ms sW Wn ds hs hW hmr
      have hge := allGe2_sound ts Γ hy hds hge2
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
            rcases ih true ss' sW' ts f (r0 + n) (lastOf last ds) (low || !allGe3 ts Γ ds) hrun y hlen hy ms'
                Wn' E R L (prev ++ meetsRounds fuel n ms Wn) hag.1 hag.2 hf (fun _ => hw')
                (lastOf_ag ds _ last prev hlast hds) with hc | ⟨n₂, kk₂, ms'', Wn'', hk₂, hr₂, hge₂, hev⟩
            · exact Or.inl hc
            · right
              have hmeets := meetsRounds_append fuel n n₂ ms Wn ms' Wn' hcr
              refine ⟨n + n₂, kk + kk₂, ms'', Wn'', steps_seq hk hk₂, ?_, ?_, ?_⟩
              · rw [roundsZ_add fuel n n₂ ms Wn ms' Wn' hcr]; exact hr₂
              · rw [hmeets]
                intro d hd
                rcases List.mem_append.mp hd with hd | hd
                · exact hge d hd
                · exact hge₂ d hd
              · rw [hmeets, ← List.append_assoc, ← Nat.add_assoc]
                rcases hev with ⟨hl0, h3, hev⟩ | hev
                · simp only [Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at hl0
                  refine Or.inl ⟨hl0.1, ?_, hev⟩
                  intro d hd
                  rcases List.mem_append.mp hd with hd | hd
                  · exact allGe3_sound ts Γ hy hds hl0.2 d hd
                  · exact h3 d hd
                · exact Or.inr hev
          | _ => exact absurd hag id
        | _ => simp at hrun
  | node i t0 t1 ih0 ih1 =>
    intro wf ss sW ts f r0 last low h y hlen hy ms Wn E R L prev hs hW hf hwf hlast
    simp only [Tree.okEndC, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h0⟩, h1⟩ := h
    obtain ⟨ε, z, hε, hzl, rfl⟩ := cover_split y i (by omega)
    have hiz : i < z.length := by omega
    rcases hε with rfl | rfl
    · exact ih0 _ _ _ _ _ _ _ _ h0 z (by rw [hzl]; exact hlen) (inCone_subst hiz hy) ms Wn E R L prev
        (agL_subst hiz hs) (agN_subst hiz hW) (SForms.ag_subst hiz hf) hwf (lastAg_subst hiz hlast)
    · exact ih1 _ _ _ _ _ _ _ _ h1 z (by rw [hzl]; exact hlen) (inCone_subst hiz hy) ms Wn E R L prev
        (agL_subst hiz hs) (agN_subst hiz hW) (SForms.ag_subst hiz hf) hwf (lastAg_subst hiz hlast)
  | skew i j s t ih =>
    intro wf ss sW ts f r0 last low h y hlen hy ms Wn E R L prev hs hW hf hwf hlast
    simp only [Tree.okEndC, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, hij⟩, ht⟩ := h
    obtain ⟨z, hzl, rfl⟩ := cover_skew y i j s hij (by omega)
    have hiz : i < z.length := by omega
    have hjz : j < z.length := by omega
    exact ih _ _ _ _ _ _ _ _ ht z (by rw [hzl]; exact hlen) (inCone_skew hiz hjz hy) ms Wn E R L prev
      (agL_skew hiz hjz hs) (agN_skew hiz hjz hW) (SForms.ag_skew hiz hjz hf) hwf (lastAg_skew hiz hjz hlast)

/-- **The root of a checked end tree with end meetings at distance 2.**  `Tree.soundEndC` from the start of the
stretch (no rounds or end meetings before it): either L is in the class `cls`, or the machine runs n rounds to a round
start, and the stretch ends there as `EndEventC` says. -/
theorem Tree.soundEndC_root {k : Nat} {cls : Option (Int × Int)} {t : Tree} {ss : List SMark} {sW : YForm}
    {ts : List YForm} {f : SForms} (h : t.okEndC Γ fuel k cls false ss sW ts f 0 none false = true) {y : List Int}
    (hlen : y.length = k) (hy : inCone ts Γ y) {ms : List Mark} {Wn E R : Nat} {L : Int} (hs : agL y ss ms)
    (hW : agN y sW Wn) (hf : f.Ag y E R L) :
    (∃ m c, cls = some (m, c) ∧ L % m = c) ∨
    ∃ n kk ms' Wn', steps kk (roundStart ms Wn) = some (roundStart ms' Wn') ∧
      roundsZ fuel n ms Wn = .newRound ms' Wn' ∧ EndEventC E R L n (meetsRounds fuel n ms Wn) ms' Wn' := by
  rcases Tree.soundEndC Γ fuel k cls t false ss sW ts f 0 none false h y hlen hy ms Wn E R L [] hs hW hf
      (fun h => by cases h) (fun _ h => by cases h) with hc | ⟨n, kk, ms', Wn', hk, hr, h2, hev⟩
  · exact Or.inl hc
  · simp only [List.nil_append, Nat.zero_add] at hev
    refine Or.inr ⟨n, kk, ms', Wn', hk, hr, ?_⟩
    rcases hev with ⟨-, h3, hev⟩ | hev
    · exact Or.inl ⟨h3, hev⟩
    · exact Or.inr ⟨h2, hev⟩

end BB6.Sym
