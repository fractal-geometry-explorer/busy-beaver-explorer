import BB6.CleanTree

/-!
# Route trees built by a proved explorer

The route-tree theorems so far were data checked by a proved function: an untrusted program (`ExploreRT.lean`,
`ExploreCT.lean`) built the tree, and the theorem file checked it with `RTree.ok` / `RTree.okW`, evaluated with
`native_decide`.  This file moves the builder into the proof.  `RTree.explore` (two-marker route trees, checked by
`RTree.ok`) and `RTree.exploreW` (clean-tape trees, checked by `RTree.okW`) build the tree from a start class the way
the programs do: run rounds one at a time, stop a path at a clean tape after at least one round, split on the first
digit a round does not decide (a shear first when both coordinates enter it), and cut a path after `d` splits.
`explore_ok` and `exploreW_okW` prove that **every** tree they build passes the check.  So `RTree.sound` and
`RTree.soundW` apply to the explored tree at every depth with nothing evaluated: the cut leaves are wherever the
explorer gives up, and only their measure (`exploreMass`, `exploreMassW`) needs evaluation, which no claim about the
machine depends on.

A path is also cut after `S` steps (rounds and splits; the explorers use 10,000 plus the depth, far beyond the longest
path), where a round halts, is not covered or has an undecided order test, and where no digit decides a round.
-/

namespace BB6.Sym
open BB6

/-- The first residue test of a round that the class does not decide: the form and the modulus (2 or 4). -/
def undecidedResidue (ts : List YForm) (Γ : Int) : Nat → List SMark → YForm → List SMark → YForm →
    Option (YForm × Int)
  | 0, _, _, _, _ => none
  | fuel + 1, sL, sg, sR, sW =>
    let here : Option (YForm × Int) := match sR with
      | m :: _ =>
        if m.t == .M && ltDec m.p (sg.addc 3) ts Γ == some false then
          let d := m.p.sub (sg.addc 3)
          match d.modDec 2 with
          | none => some (d, 2)
          | some 0 => match d.half? with
            | none => some (d, 2)
            | some _ => if (d.modDec 4).isNone then some (d, 4) else none
          | _ => none
        else none
      | [] => none
    match here with
    | some r => some r
    | none =>
      match symGapEvent ts Γ sL sg sR sW with
      | some (.gap a b c d) => undecidedResidue ts Γ fuel a b c d
      | some (.pkt sL' sx sR' sW') =>
        match symPktBack ts Γ sL' sx sR' sW' with
        | some (.gap a b c d) => undecidedResidue ts Γ fuel a b c d
        | _ => none
      | some (.pktM sL' sx sR' sW') =>
        match symPktLand ts Γ sL' sx sR' sW' with
        | some (.gap a b c d) => undecidedResidue ts Γ fuel a b c d
        | _ => none
      | _ => none

/-- How to split so that `f` is decided modulo `m`: a shear (if both coefficients enter the digit), then a split. -/
def chooseSplit (f : YForm) (m : Int) : Option (Option (Nat × Int) × Nat) :=
  let h := if m == 4 then f.c.map (· / 2) else f.c
  let a := h.getD 0 0 % 2
  let b := h.getD 1 0 % 2
  if a != 0 && b != 0 then some (some (0, -1), 0)
  else if a != 0 then some (none, 0)
  else if b != 0 then some (none, 1)
  else none

/-- The split for a round the class does not decide. -/
def splitStep (ts : List YForm) (Γ : Int) (ss : List SMark) (sW : YForm) : Option (Option (Nat × Int) × Nat) :=
  match undecidedResidue ts Γ 2000 [] (YForm.const 1) ss sW with
  | some (f, m) => chooseSplit f m
  | none => none

variable (Γ : Int) (fuel : Nat)

/-! ## Two-marker route trees -/

/-- Build a route tree (`S` steps, `d` splits): stop at a clean tape after at least one round (`moved`). -/
def RTree.explore : Nat → Nat → Bool → List SMark → YForm → List YForm → RTree
  | 0, _, _, _, _, _ => .cut
  | S + 1, d, moved, ss, sW, ts =>
    if (moved && symClean ss sW) = true then .clean else
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => .adv 1 (RTree.explore S d true ss' sW' ts)
    | some _ => .cut
    | none =>
      match d with
      | 0 => .cut
      | d + 1 =>
        match splitStep ts Γ ss sW with
        | none => .cut
        | some (none, i) =>
          if i < 2 then
            .split i (RTree.explore S d moved (substL ss i 0) (sW.subst i 0) (substT ts i 0))
              (RTree.explore S d moved (substL ss i 1) (sW.subst i 1) (substT ts i 1))
          else .cut
        | some (some (j, s), i) =>
          if i < 2 then
            .shear j s (.split i
              (RTree.explore S d moved (substL (shearL ss j s) i 0) ((sW.shear j s).subst i 0)
                (substT (shearT ts j s) i 0))
              (RTree.explore S d moved (substL (shearL ss j s) i 1) ((sW.shear j s).subst i 1)
                (substT (shearT ts j s) i 1)))
          else .cut

/-- **Every explored route tree passes the check.** -/
theorem RTree.explore_ok : ∀ (S d : Nat) (moved : Bool) (ss : List SMark) (sW : YForm) (ts : List YForm),
    (RTree.explore Γ fuel S d moved ss sW ts).ok Γ fuel moved ss sW ts = true := by
  intro S
  induction S with
  | zero => intro d moved ss sW ts; rfl
  | succ S ih =>
    intro d moved ss sW ts
    simp only [RTree.explore]
    split
    · next hc => simpa [RTree.ok] using hc
    · split
      · next ss' sW' hr => simp [RTree.ok, symRoundsZ, hr, ih]
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · next hi => simp [RTree.ok, hi, ih]
            · rfl
          · split
            · next hi => simp [RTree.ok, hi, ih]
            · rfl

/-- The cut measure (numerator over 2^D) and the leaf counts (cut, clean) of `RTree.explore`, without the tree. -/
def exploreMass : Nat → Nat → Nat → Bool → List SMark → YForm → List YForm → Nat × Nat × Nat
  | 0, _, D, _, _, _, _ => (2 ^ D, 1, 0)
  | S + 1, d, D, moved, ss, sW, ts =>
    if (moved && symClean ss sW) = true then (0, 0, 1) else
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => exploreMass S d D true ss' sW' ts
    | some _ => (2 ^ D, 1, 0)
    | none =>
      match d with
      | 0 => (2 ^ D, 1, 0)
      | d + 1 =>
        match splitStep ts Γ ss sW with
        | none => (2 ^ D, 1, 0)
        | some (none, i) =>
          if i < 2 then
            let a := exploreMass S d (D - 1) moved (substL ss i 0) (sW.subst i 0) (substT ts i 0)
            let b := exploreMass S d (D - 1) moved (substL ss i 1) (sW.subst i 1) (substT ts i 1)
            (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)
          else (2 ^ D, 1, 0)
        | some (some (j, s), i) =>
          if i < 2 then
            let a := exploreMass S d (D - 1) moved (substL (shearL ss j s) i 0) ((sW.shear j s).subst i 0)
              (substT (shearT ts j s) i 0)
            let b := exploreMass S d (D - 1) moved (substL (shearL ss j s) i 1) ((sW.shear j s).subst i 1)
              (substT (shearT ts j s) i 1)
            (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)
          else (2 ^ D, 1, 0)

theorem exploreMass_eq : ∀ (S d D : Nat) (moved : Bool) (ss : List SMark) (sW : YForm) (ts : List YForm),
    exploreMass Γ fuel S d D moved ss sW ts =
      ((RTree.explore Γ fuel S d moved ss sW ts).cutMass D, (RTree.explore Γ fuel S d moved ss sW ts).leaves) := by
  intro S
  induction S with
  | zero => intro d D moved ss sW ts; rfl
  | succ S ih =>
    intro d D moved ss sW ts
    simp only [exploreMass, RTree.explore]
    split
    · rfl
    · split
      · simp only [RTree.cutMass, RTree.leaves]; exact ih _ _ _ _ _ _
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · simp only [RTree.cutMass, RTree.leaves, ih]
            · rfl
          · split
            · simp only [RTree.cutMass, RTree.leaves, ih]
            · rfl

/-! ## Clean-tape trees -/

/-- Build a clean-tape tree (`S` steps, `d` splits): stop at a one-marker clean tape after at least one round whose
width is decided to be larger than the start's (`w0`). -/
def RTree.exploreW : Nat → Nat → Bool → List SMark → YForm → YForm → List YForm → RTree
  | 0, _, _, _, _, _, _ => .cut
  | S + 1, d, moved, ss, sW, w0, ts =>
    if (moved && symClean1 ss sW && widerB sW w0 ts Γ) = true then .clean else
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => .adv 1 (RTree.exploreW S d true ss' sW' w0 ts)
    | some _ => .cut
    | none =>
      match d with
      | 0 => .cut
      | d + 1 =>
        match splitStep ts Γ ss sW with
        | none => .cut
        | some (none, i) =>
          if i < 2 then
            .split i (RTree.exploreW S d moved (substL ss i 0) (sW.subst i 0) (w0.subst i 0) (substT ts i 0))
              (RTree.exploreW S d moved (substL ss i 1) (sW.subst i 1) (w0.subst i 1) (substT ts i 1))
          else .cut
        | some (some (j, s), i) =>
          if i < 2 then
            .shear j s (.split i
              (RTree.exploreW S d moved (substL (shearL ss j s) i 0) ((sW.shear j s).subst i 0)
                ((w0.shear j s).subst i 0) (substT (shearT ts j s) i 0))
              (RTree.exploreW S d moved (substL (shearL ss j s) i 1) ((sW.shear j s).subst i 1)
                ((w0.shear j s).subst i 1) (substT (shearT ts j s) i 1)))
          else .cut

/-- **Every explored clean-tape tree passes the check.** -/
theorem RTree.exploreW_okW : ∀ (S d : Nat) (moved : Bool) (ss : List SMark) (sW w0 : YForm) (ts : List YForm),
    (RTree.exploreW Γ fuel S d moved ss sW w0 ts).okW Γ fuel moved ss sW w0 ts = true := by
  intro S
  induction S with
  | zero => intro d moved ss sW w0 ts; rfl
  | succ S ih =>
    intro d moved ss sW w0 ts
    simp only [RTree.exploreW]
    split
    · next hc => simpa [RTree.okW] using hc
    · split
      · next ss' sW' hr => simp [RTree.okW, symRoundsZ, hr, ih]
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · next hi => simp [RTree.okW, hi, ih]
            · rfl
          · split
            · next hi => simp [RTree.okW, hi, ih]
            · rfl

/-- The cut measure and the leaf counts of `RTree.exploreW`, without the tree. -/
def exploreMassW : Nat → Nat → Nat → Bool → List SMark → YForm → YForm → List YForm → Nat × Nat × Nat
  | 0, _, D, _, _, _, _, _ => (2 ^ D, 1, 0)
  | S + 1, d, D, moved, ss, sW, w0, ts =>
    if (moved && symClean1 ss sW && widerB sW w0 ts Γ) = true then (0, 0, 1) else
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => exploreMassW S d D true ss' sW' w0 ts
    | some _ => (2 ^ D, 1, 0)
    | none =>
      match d with
      | 0 => (2 ^ D, 1, 0)
      | d + 1 =>
        match splitStep ts Γ ss sW with
        | none => (2 ^ D, 1, 0)
        | some (none, i) =>
          if i < 2 then
            let a := exploreMassW S d (D - 1) moved (substL ss i 0) (sW.subst i 0) (w0.subst i 0) (substT ts i 0)
            let b := exploreMassW S d (D - 1) moved (substL ss i 1) (sW.subst i 1) (w0.subst i 1) (substT ts i 1)
            (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)
          else (2 ^ D, 1, 0)
        | some (some (j, s), i) =>
          if i < 2 then
            let a := exploreMassW S d (D - 1) moved (substL (shearL ss j s) i 0) ((sW.shear j s).subst i 0)
              ((w0.shear j s).subst i 0) (substT (shearT ts j s) i 0)
            let b := exploreMassW S d (D - 1) moved (substL (shearL ss j s) i 1) ((sW.shear j s).subst i 1)
              ((w0.shear j s).subst i 1) (substT (shearT ts j s) i 1)
            (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)
          else (2 ^ D, 1, 0)

theorem exploreMassW_eq : ∀ (S d D : Nat) (moved : Bool) (ss : List SMark) (sW w0 : YForm) (ts : List YForm),
    exploreMassW Γ fuel S d D moved ss sW w0 ts =
      ((RTree.exploreW Γ fuel S d moved ss sW w0 ts).cutMass D,
        (RTree.exploreW Γ fuel S d moved ss sW w0 ts).leaves) := by
  intro S
  induction S with
  | zero => intro d D moved ss sW w0 ts; rfl
  | succ S ih =>
    intro d D moved ss sW w0 ts
    simp only [exploreMassW, RTree.exploreW]
    split
    · rfl
    · split
      · simp only [RTree.cutMass, RTree.leaves]; exact ih _ _ _ _ _ _ _
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · simp only [RTree.cutMass, RTree.leaves, ih]
            · rfl
          · split
            · simp only [RTree.cutMass, RTree.leaves, ih]
            · rfl

end BB6.Sym
