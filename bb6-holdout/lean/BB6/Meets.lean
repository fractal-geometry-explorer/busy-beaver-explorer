import BB6.SymSplit

/-!
# End meetings, concrete and symbolic

An *end meeting* is the gap meeting the last mark of the tape when that mark is a marker (the end marker); its
distance is `d = p − (g + 3)`.  A run *closes* when an end meeting has `d ≤ 2`: that is where a halt can begin.
`meetsZ` follows `roundZ` event by event and lists the distances of the end meetings of one round; `symMeetsZ` is
its mirror on symbolic positions, and `symMeetsZ_sound` says the two lists agree at every point of the cone.
-/

namespace BB6
open BB6

/-- The end meeting at this event, if the gap is about to meet the last mark and it is a marker. -/
def meetsOf (g : Nat) : List Mark → List Nat
  | [m] => if m.t = .M ∧ ¬ m.p < g + 3 then [m.p - (g + 3)] else []
  | _ => []

/-- The distances of the end meetings of a round, following `roundZ`. -/
def meetsZ : Nat → List Mark → Nat → List Mark → Nat → List Nat
  | 0, _, _, _, _ => []
  | fuel + 1, msL, g, msR, W =>
    meetsOf g msR ++
    (match gapEvent msL g msR W with
     | .gap msL' g' msR' W' => meetsZ fuel msL' g' msR' W'
     | .pkt msL' x msR' W' =>
       match pktBack msL' x msR' W' with
       | .gap a b c d => meetsZ fuel a b c d
       | _ => []
     | .pktM msL' y msR' W' =>
       match pktLand msL' y msR' W' with
       | .gap a b c d => meetsZ fuel a b c d
       | _ => []
     | _ => [])

/-- End meetings over `n` rounds from a round start. -/
def meetsRounds (fuel : Nat) : Nat → List Mark → Nat → List Nat
  | 0, _, _ => []
  | n + 1, ms, W =>
    meetsZ fuel [] 1 ms W ++
    (match roundZ fuel [] 1 ms W with
     | .newRound ms' W' => meetsRounds fuel n ms' W'
     | _ => [])

end BB6

namespace BB6.Sym
open BB6

section
variable (ts : List YForm) (Γ : Int)

def symMeetsOf (sg : YForm) : List SMark → Option (List YForm)
  | [m] =>
    match m.t with
    | .M =>
      match ltDec m.p (sg.addc 3) ts Γ with
      | some false => some [m.p.sub (sg.addc 3)]
      | some true => some []
      | none => none
    | _ => some []
  | _ => some []

def agLN (y : List Int) : List YForm → List Nat → Prop
  | [], [] => True
  | f :: fs, n :: ns => agN y f n ∧ agLN y fs ns
  | _, _ => False

theorem agLN_append {y : List Int} {fs gs : List YForm} {ns ms : List Nat} (h1 : agLN y fs ns) (h2 : agLN y gs ms) :
    agLN y (fs ++ gs) (ns ++ ms) := by
  induction fs generalizing ns with
  | nil => cases ns with
    | nil => simpa using h2
    | cons _ _ => exact absurd h1 id
  | cons f fs ih => cases ns with
    | nil => exact absurd h1 id
    | cons n ns => exact ⟨h1.1, ih h1.2⟩

theorem symMeetsOf_sound {y : List Int} (hy : inCone ts Γ y) {sg : YForm} {g : Nat} (hg : agN y sg g)
    {sR : List SMark} {msR : List Mark} (hR : agL y sR msR) {ds : List YForm}
    (h : symMeetsOf ts Γ sg sR = some ds) : agLN y ds (meetsOf g msR) := by
  cases sR with
  | nil => cases msR with
    | nil => cases h; trivial
    | cons _ _ => exact absurd hR id
  | cons s sR' =>
    cases msR with
    | nil => exact absurd hR id
    | cons m msR' =>
      cases sR' with
      | cons _ _ =>
        cases msR' with
        | nil => exact absurd hR.2 id
        | cons _ _ => simp only [symMeetsOf] at h; cases h; simp only [meetsOf]; trivial
      | nil =>
        cases msR' with
        | cons _ _ => exact absurd hR.2 id
        | nil =>
          obtain ⟨⟨ht, hp⟩, -⟩ := hR
          cases hst : s.t with
          | M =>
            simp only [symMeetsOf, hst] at h
            have hmt : m.t = .M := by rw [← ht, hst]
            cases hl : ltDec s.p (sg.addc 3) ts Γ with
            | none => rw [hl] at h; cases h
            | some b =>
              rw [hl] at h
              have hb := lt_of_ltDec hy hp (agN_addc hg 3) hl
              cases b with
              | false =>
                cases h
                have hn : ¬ m.p < g + 3 := fun h' => by simpa using hb.mp h'
                simp only [meetsOf, hmt, hn, not_false_eq_true, and_self, if_true]
                refine ⟨?_, trivial⟩
                unfold agN at hp hg ⊢; simp only [eval_sub, eval_addc]; omega
              | true =>
                cases h
                simp only [meetsOf, hmt, hb.mpr rfl, not_true_eq_false, and_false, if_false]; trivial
          | _ =>
            simp only [symMeetsOf, hst] at h; cases h
            have hmt : m.t ≠ .M := by rw [← ht, hst]; decide
            simp only [meetsOf, hmt, false_and, if_false]; trivial

/-- End meetings of a round on symbolic positions. -/
def symMeetsZ : Nat → List SMark → YForm → List SMark → YForm → Option (List YForm)
  | 0, _, _, _, _ => some []
  | fuel + 1, sL, sg, sR, sW =>
    match symMeetsOf ts Γ sg sR with
    | none => none
    | some here =>
      match symGapEvent ts Γ sL sg sR sW with
      | none => none
      | some (.gap sL' sg' sR' sW') => (symMeetsZ fuel sL' sg' sR' sW').map (here ++ ·)
      | some (.pkt sL' sx sR' sW') =>
        match symPktBack ts Γ sL' sx sR' sW' with
        | none => none
        | some (.gap a b c d) => (symMeetsZ fuel a b c d).map (here ++ ·)
        | some _ => some here
      | some (.pktM sL' sx sR' sW') =>
        match symPktLand ts Γ sL' sx sR' sW' with
        | none => none
        | some (.gap a b c d) => (symMeetsZ fuel a b c d).map (here ++ ·)
        | some _ => some here
      | some _ => some here

theorem symMeetsZ_sound {y : List Int} (hy : inCone ts Γ y) (fuel : Nat) :
    ∀ sL msL sg g sR msR sW W ds, agL y sL msL → agN y sg g → agL y sR msR → agN y sW W →
      symMeetsZ ts Γ fuel sL sg sR sW = some ds → agLN y ds (meetsZ fuel msL g msR W) := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ ds _ _ _ _ h; cases h; trivial
  | succ fuel ih =>
    intro sL msL sg g sR msR sW W ds hL hg hR hW h
    simp only [symMeetsZ] at h
    simp only [meetsZ]
    cases hm : symMeetsOf ts Γ sg sR with
    | none => rw [hm] at h; cases h
    | some here =>
      rw [hm] at h
      have hhere := symMeetsOf_sound ts Γ hy hg hR hm
      simp only at h
      cases he : symGapEvent ts Γ sL sg sR sW with
      | none => rw [he] at h; cases h
      | some ev =>
        rw [he] at h
        have hag := symGapEvent_sound ts Γ hy hL hg hR hW he
        generalize gapEvent msL g msR W = cev at hag ⊢
        cases ev with
        | gap sL' sg' sR' sW' =>
          cases cev with
          | gap msL' g' msR' W' =>
            simp only at h
            cases hr : symMeetsZ ts Γ fuel sL' sg' sR' sW' with
            | none => rw [hr] at h; cases h
            | some rest =>
              rw [hr] at h; cases h
              exact agLN_append hhere (ih _ _ _ _ _ _ _ _ _ hag.1 hag.2.1 hag.2.2.1 hag.2.2.2 hr)
          | _ => exact absurd hag id
        | pkt sL' sx sR' sW' =>
          cases cev with
          | pkt msL' x msR' W' =>
            simp only at h
            dsimp only
            cases hb : symPktBack ts Γ sL' sx sR' sW' with
            | none => rw [hb] at h; cases h
            | some pr =>
              rw [hb] at h
              have hpr := symPktBack_sound ts Γ hy sL' msL' sx x sR' msR' sW' W' pr hag.1 hag.2.2.1 hag.2.2.2 hb
              generalize pktBack msL' x msR' W' = cpr at hpr ⊢
              cases pr with
              | gap a b c d =>
                cases cpr with
                | gap a' b' c' d' =>
                  simp only at h
                  cases hr : symMeetsZ ts Γ fuel a b c d with
                  | none => rw [hr] at h; cases h
                  | some rest =>
                    rw [hr] at h; cases h
                    exact agLN_append hhere (ih _ _ _ _ _ _ _ _ _ hpr.1 hpr.2.1 hpr.2.2.1 hpr.2.2.2 hr)
                | _ => exact absurd hpr id
              | newRound _ _ => cases cpr with
                | newRound _ _ => cases h; simpa using hhere
                | _ => exact absurd hpr id
              | halt => cases cpr with
                | halt => cases h; simpa using hhere
                | _ => exact absurd hpr id
              | uncovered => cases cpr with
                | uncovered => cases h; simpa using hhere
                | _ => exact absurd hpr id
          | _ => exact absurd hag id
        | pktM sL' sx sR' sW' =>
          cases cev with
          | pktM msL' x msR' W' =>
            simp only at h
            dsimp only
            cases hb : symPktLand ts Γ sL' sx sR' sW' with
            | none => rw [hb] at h; cases h
            | some pr =>
              rw [hb] at h
              have hpr := symPktLand_sound ts Γ hy sL' msL' sx x sR' msR' sW' W' pr hag.1 hag.2.1 hag.2.2.1 hag.2.2.2 hb
              generalize pktLand msL' x msR' W' = cpr at hpr ⊢
              cases pr with
              | gap a b c d =>
                cases cpr with
                | gap a' b' c' d' =>
                  simp only at h
                  cases hr : symMeetsZ ts Γ fuel a b c d with
                  | none => rw [hr] at h; cases h
                  | some rest =>
                    rw [hr] at h; cases h
                    exact agLN_append hhere (ih _ _ _ _ _ _ _ _ _ hpr.1 hpr.2.1 hpr.2.2.1 hpr.2.2.2 hr)
                | _ => exact absurd hpr id
              | newRound _ _ => cases cpr with
                | newRound _ _ => cases h; simpa using hhere
                | _ => exact absurd hpr id
              | halt => cases cpr with
                | halt => cases h; simpa using hhere
                | _ => exact absurd hpr id
              | uncovered => cases cpr with
                | uncovered => cases h; simpa using hhere
                | _ => exact absurd hpr id
          | _ => exact absurd hag id
        | halt => cases cev with
          | halt => cases h; simpa using hhere
          | _ => exact absurd hag id
        | uncovered => cases cev with
          | uncovered => cases h; simpa using hhere
          | _ => exact absurd hag id

end

section
variable (ts : List YForm) (Γ : Int)

/-- End meetings over `n` rounds, on symbolic positions. -/
def symMeetsRounds (fuel : Nat) : Nat → List SMark → YForm → Option (List YForm)
  | 0, _, _ => some []
  | n + 1, ss, sW =>
    match symMeetsZ ts Γ fuel [] (YForm.const 1) ss sW with
    | none => none
    | some here =>
      match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
      | some (.newRound ss' sW') => (symMeetsRounds fuel n ss' sW').map (here ++ ·)
      | some _ => some here
      | none => none

theorem symMeetsRounds_sound {y : List Int} (hy : inCone ts Γ y) (fuel n : Nat) :
    ∀ ss ms sW W ds, agL y ss ms → agN y sW W → symMeetsRounds ts Γ fuel n ss sW = some ds →
      agLN y ds (meetsRounds fuel n ms W) := by
  induction n with
  | zero => intro _ _ _ _ ds _ _ h; cases h; trivial
  | succ n ih =>
    intro ss ms sW W ds hs hW h
    simp only [symMeetsRounds] at h
    simp only [meetsRounds]
    cases hm : symMeetsZ ts Γ fuel [] (YForm.const 1) ss sW with
    | none => rw [hm] at h; cases h
    | some here =>
      rw [hm] at h
      have hhere := symMeetsZ_sound ts Γ hy fuel [] [] (YForm.const 1) 1 ss ms sW W here trivial (agN_const y 1) hs hW hm
      simp only at h
      cases hr : symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
      | none => rw [hr] at h; cases h
      | some sr =>
        rw [hr] at h
        have hag := symRoundZ_sound ts Γ hy fuel [] [] (YForm.const 1) 1 ss ms sW W sr trivial (agN_const y 1) hs hW hr
        generalize roundZ fuel [] 1 ms W = cr at hag ⊢
        cases sr with
        | newRound ss' sW' =>
          cases cr with
          | newRound ms' W' =>
            simp only at h
            cases hr2 : symMeetsRounds ts Γ fuel n ss' sW' with
            | none => rw [hr2] at h; cases h
            | some rest =>
              rw [hr2] at h; cases h
              exact agLN_append hhere (ih _ _ _ _ _ hag.1 hag.2 hr2)
          | _ => exact absurd hag id
        | gap _ _ _ _ => cases cr with
          | gap _ _ _ _ => cases h; simpa using hhere
          | _ => exact absurd hag id
        | halt => cases cr with
          | halt => cases h; simpa using hhere
          | _ => exact absurd hag id
        | uncovered => cases cr with
          | uncovered => cases h; simpa using hhere
          | _ => exact absurd hag id

/-- Every distance is at least 3 on the cone (no close). -/
def allGe3 (ds : List YForm) : Bool := ds.all (fun d => ltDec d (YForm.const 3) ts Γ == some false)

theorem allGe3_sound {y : List Int} (hy : inCone ts Γ y) :
    ∀ {ds : List YForm} {ns : List Nat}, agLN y ds ns → allGe3 ts Γ ds = true → ∀ n ∈ ns, 3 ≤ n
  | [], [], _, _, n, hn => by simp at hn
  | d :: ds, m :: ns, h, ha, n, hn => by
    simp only [allGe3, List.all_cons, Bool.and_eq_true, beq_iff_eq] at ha
    have hl := lt_of_ltDec hy h.1 (agN_const y 3) ha.1
    simp only [List.mem_cons] at hn
    rcases hn with rfl | hn
    · have : ¬ n < 3 := fun h' => by simpa using hl.mp h'
      omega
    · exact allGe3_sound hy h.2 (by simpa [allGe3] using ha.2) n hn
  | [], _ :: _, h, _, _, _ => absurd h id
  | _ :: _, [], h, _, _, _ => absurd h id

end

/-! ## Trees that also certify "no close" -/

variable (Γ : Int) (fuel : Nat)

/-- As `Tree.ok`, and every end meeting in each leaf's rounds is at distance ≥ 3. -/
def Tree.okNC (k : Nat) : Tree → List SMark → YForm → List YForm → Bool
  | .leaf n, ss, sW, ts =>
    symRightOK ts Γ (YForm.const 4) false sW ss &&
    (match symRoundsZ ts Γ fuel n ss sW with
     | some (.newRound _ _) => true
     | _ => false) &&
    (match symMeetsRounds ts Γ fuel n ss sW with
     | some ds => allGe3 ts Γ ds
     | none => false)
  | .node i t0 t1, ss, sW, ts =>
    decide (i < k) && t0.okNC k (substL ss i 0) (sW.subst i 0) (substT ts i 0) &&
      t1.okNC k (substL ss i 1) (sW.subst i 1) (substT ts i 1)

/-- **A checked no-close tree, for the machine.**  At every point of the root class inside the cone, the machine runs
from the root's round start for the leaf's number of rounds without halting, reaching a round start, and every end
meeting on the way is at distance at least 3: the run does not close. -/
theorem Tree.soundNC (k : Nat) (t : Tree) : ∀ (ss : List SMark) (sW : YForm) (ts : List YForm),
    t.okNC Γ fuel k ss sW ts = true → ∀ (y : List Int), y.length = k → inCone ts Γ y →
    ∀ (ms : List Mark) (Wn : Nat), agL y ss ms → agN y sW Wn →
    ∃ n kk ms' Wn', steps kk (roundStart ms Wn) = some (roundStart ms' Wn') ∧
      roundsZ fuel n ms Wn = .newRound ms' Wn' ∧ ∀ d ∈ meetsRounds fuel n ms Wn, 3 ≤ d := by
  induction t with
  | leaf n =>
    intro ss sW ts h y _ hy ms Wn hs hW
    simp only [Tree.okNC, Bool.and_eq_true] at h
    obtain ⟨⟨hwf, hrun⟩, hmt⟩ := h
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
          have hrwf : roundWF ms Wn := symRightOK_sound ts Γ hy ss _ 4 false sW Wn ms (agN_const y 4) hW hs hwf
          generalize hcr : roundsZ fuel n ms Wn = cr at hag
          cases cr with
          | newRound ms' Wn' =>
            obtain ⟨kk, hk, -⟩ := rounds_run fuel n ms Wn hrwf (by rw [hcr]; intro h; cases h)
            rw [hcr] at hk
            exact ⟨n, kk, ms', Wn', hk, hcr, hge⟩
          | _ => exact absurd hag id
      | _ => simp at hrun
  | node i t0 t1 ih0 ih1 =>
    intro ss sW ts h y hlen hy ms Wn hs hW
    simp only [Tree.okNC, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, h0⟩, h1⟩ := h
    obtain ⟨ε, z, hε, hzl, rfl⟩ := cover_split y i (by omega)
    have hiz : i < z.length := by omega
    rcases hε with rfl | rfl
    · exact ih0 _ _ _ h0 z (by rw [hzl]; exact hlen) (inCone_subst hiz hy) ms Wn (agL_subst hiz hs) (agN_subst hiz hW)
    · exact ih1 _ _ _ h1 z (by rw [hzl]; exact hlen) (inCone_subst hiz hy) ms Wn (agL_subst hiz hs) (agN_subst hiz hW)

end BB6.Sym
