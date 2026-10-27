import BB6.CleanEntryTree
import BB6.PassTree
open BB6 BB6.Sym

/-! # The loop entries followed in the clean tape's coordinate (untrusted driver: statistics only)

`blank_halt_pass` (`thm/PassEntryHalt.lean`) follows a halting run past a loop entry of the clean-tape tree with the
pass-start trees, whose classes are over all pass starts: four free coordinates (a, b, W and R), of which a cut leaf
holds 3.8% at 20 splits for R ≥ 178.  The pass starts the run reaches from an entry are not spread over those four
coordinates: they are one-coordinate families, the entry's class of W/2.  This walks the clean-tape tree with loop
entries (`cleanTreeGE Γ d`, as `RTree.exploreWE` builds it) and roots the pass-start explorer (`passAct`,
`BB6/PassTree.lean`) at each entry, in the clean tape's own coordinate, with `e` more splits; it follows the run past
each landing of the loop's chain (at most `ch` of them) to a wider clean tape.  It prints the measure of the entries
whose run reaches a wider clean tape that way, and of those it leaves cut, as fractions of the entries' measure, by the
number of landings on the way.  With `none` as the fifth argument it walks the plain clean-tape tree (`cleanTreeG Γ d`)
instead, for comparison.  No proof reads anything it prints.

usage (after `check_end.sh` has built the shared library):
  lean --load-dynlib=cbuild/so/libBB6all.so --run ReachStats.lean 2199023255552 28 12 4 -/

def ctS : List SMark × YForm × List YForm :=
  let W : YForm := ⟨0, [2, 0]⟩
  ([⟨.M, W.addc (-2)⟩], W, [W])

/-- Measures as numerators over 2^(d + e). -/
structure RAcc where
  entries : Nat := 0
  entryMass : Nat := 0
  -- the clean-tape tree's own cut classes
  cutMass : Nat := 0
  -- the entries' classes: followed to a wider clean tape, or cut (at the depth, at a round decided as something other
  -- than a new round start, or otherwise), or still landing when the chain's budget ran out
  cleanM : Nat := 0
  depthM : Nat := 0
  decidedM : Nat := 0
  otherM : Nat := 0
  landM : Nat := 0
  -- followed to a clean tape, and cut, by the number of landings on the way
  lands : Array Nat := Array.replicate 20 0
  cutLands : Array Nat := Array.replicate 20 0
  deriving Inhabited

/-- The cleaves allowed on a path (as `passCleaves`, `thm/PassHalt.lean`). -/
def passCleavesR : Nat := 8

/-- The width, right end and left countdown of a three-wall round start, as forms. -/
def sformsOf (ss : List SMark) (sW : YForm) : Option SForms :=
  match swwwOf ss with
  | some (_, b, c) => some ⟨sW, (sW.sub c).addc (-1), L1Form b c sW⟩
  | none => none

/-- The pass-start explorer from an entry's class (`d` splits and `nb` cleaves left, measure 2^D), restarted at each
landing. -/
partial def chain (Γ : Int) (fuel : Nat) (S d nb D ch nl : Nat) (wf cf : Bool) (n : Nat) (ss : List SMark)
    (sW : YForm) (ts : List YForm) (f : SForms) (acc : RAcc) : RAcc :=
  let cutAt (acc : RAcc) (kind : Nat) : RAcc :=
    let acc := { acc with cutLands := acc.cutLands.modify (min nl 19) (· + 2 ^ D) }
    match kind with
    | 0 => { acc with depthM := acc.depthM + 2 ^ D }
    | 1 => { acc with decidedM := acc.decidedM + 2 ^ D }
    | _ => { acc with otherM := acc.otherM + 2 ^ D }
  match S with
  | 0 => cutAt acc 0
  | S + 1 =>
    match passAct Γ fuel 2 none (nb != 0) wf cf n ss sW ts f with
    | .land =>
      match ch, sformsOf ss sW with
      | ch + 1, some f' => chain Γ fuel S d nb D ch (nl + 1) true true 0 ss sW ts f' acc
      | _, _ => { acc with landM := acc.landM + 2 ^ D }
    | .clean => { acc with cleanM := acc.cleanM + 2 ^ D, lands := acc.lands.modify (min nl 19) (· + 2 ^ D) }
    | .close => cutAt acc 2
    | .cut =>
      let decided := (wf || symRightOK ts Γ (YForm.const 4) false sW ss) &&
        (match symRoundsZ ts Γ fuel 1 ss sW with | some (.newRound _ _) => false | some _ => true | none => false)
      cutAt acc (if decided then 1 else 2)
    | .adv ss' sW' => chain Γ fuel S d nb D ch nl true (cf && meetsGe3 Γ fuel ts ss sW) (n + 1) ss' sW' ts f acc
    | .split i =>
      match d with
      | 0 => cutAt acc 0
      | d + 1 =>
        let acc :=
          chain Γ fuel S d nb (D - 1) ch nl wf cf n (substL ss i 0) (sW.subst i 0) (substT ts i 0) (f.subst i 0) acc
        chain Γ fuel S d nb (D - 1) ch nl wf cf n (substL ss i 1) (sW.subst i 1) (substT ts i 1) (f.subst i 1) acc
    | .skew i j s =>
      chain Γ fuel S d nb D ch nl wf cf n (skewL ss i j s) (sW.skew i j s) (skewT ts i j s) (f.skew i j s) acc
    -- a cleave's slice (one value of a coordinate) has measure 0: only the rest is followed
    | .cleave i c σ _ j1 =>
      chain Γ fuel S d (nb - 1) D ch nl wf cf n ss sW (ts.set j1 ((cleaveBnd i c σ).addc (Γ - 1))) f acc

/-- The clean-tape tree's walk (as `RTree.exploreWE`), with each entry handed to `chain` (`ent`; without it, the plain
tree's walk, as `RTree.exploreW`). -/
partial def walk (Γ : Int) (fuel B e ch : Nat) (ent : Bool) : Nat → Nat → Nat → Bool → List SMark → YForm → YForm →
    List YForm → Nat → RAcc → RAcc
  | 0, _, _, _, _, _, _, _, D, acc => { acc with cutMass := acc.cutMass + 2 ^ (D + e) }
  | S + 1, d, nd, moved, ss, sW, w0, ts, D, acc =>
    if (moved && symClean1 ss sW && widerB sW w0 ts Γ) = true then acc else
    if ent && cleanEntryOK Γ ts ss sW w0 = true then
      match sformsOf ss sW with
      | some f =>
        let acc := { acc with entries := acc.entries + 1, entryMass := acc.entryMass + 2 ^ (D + e) }
        chain Γ fuel (10000 + e) e passCleavesR (D + e) ch 0 true true 0 ss sW ts f acc
      | none => acc
    else
    let cut := fun (acc : RAcc) => { acc with cutMass := acc.cutMass + 2 ^ (D + e) }
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => walk Γ fuel B e ch ent S d nd true ss' sW' w0 ts D acc
    | some _ => cut acc
    | none =>
      match splitStep ts Γ ss sW with
      | none =>
        match nd, coneMin ts Γ with
        | nd + 1, some z =>
          if dropOK Γ fuel z ss sW w0 ts = true then
            walk Γ fuel B e ch ent S d nd moved ss sW w0 [dropCone Γ z] D acc
          else cut acc
        | _, _ => cut acc
      | some (none, i) =>
        match d with
        | 0 => cut acc
        | d + 1 =>
          let acc := walk Γ fuel B e ch ent S d B moved (substL ss i 0) (sW.subst i 0) (w0.subst i 0) (substT ts i 0)
            (D - 1) acc
          walk Γ fuel B e ch ent S d B moved (substL ss i 1) (sW.subst i 1) (w0.subst i 1) (substT ts i 1) (D - 1) acc
      | some (some (j, s), i) =>
        match d with
        | 0 => cut acc
        | d + 1 =>
          let ss2 := shearL ss j s; let sW2 := sW.shear j s; let w02 := w0.shear j s; let ts2 := shearT ts j s
          let acc := walk Γ fuel B e ch ent S d B moved (substL ss2 i 0) (sW2.subst i 0) (w02.subst i 0)
            (substT ts2 i 0) (D - 1) acc
          walk Γ fuel B e ch ent S d B moved (substL ss2 i 1) (sW2.subst i 1) (w02.subst i 1) (substT ts2 i 1) (D - 1)
            acc

def main (args : List String) : IO Unit := do
  let Γ := (args.getD 0 "2199023255552").toNat!
  let d := (args.getD 1 "28").toNat!
  let e := (args.getD 2 "12").toNat!
  let ch := (args.getD 3 "4").toNat!
  let ent := args.getD 4 "entries" != "none"
  let t0 ← IO.monoMsNow
  let a := walk Γ 1000 4 e ch ent (10000 + d) d 4 false ctS.1 ctS.2.1 ctS.2.1 ctS.2.2 d {}
  let t1 ← IO.monoMsNow
  let tot : Float := (2 : Float) ^ (d + e).toFloat
  let fl (x : Nat) : Float := x.toFloat / tot
  let fe (x : Nat) : Float := if a.entryMass = 0 then 0 else x.toFloat / a.entryMass.toFloat
  IO.println s!"Γ = {Γ}, d = {d}, {e} more splits from each entry, at most {ch} landings ({t1 - t0} ms)"
  IO.println s!"  the clean-tape tree's own cut classes: measure {fl a.cutMass}"
  IO.println s!"  loop entries: {a.entries}, measure {fl a.entryMass}"
  let cutE := a.depthM + a.decidedM + a.otherM
  IO.println s!"  of the entries' measure: to a wider clean tape {fe a.cleanM}, cut {fe cutE}"
  IO.println s!"    (at the depth {fe a.depthM}, at a decided round {fe a.decidedM}, otherwise {fe a.otherM}),"
  IO.println s!"    still landing {fe a.landM}"
  IO.println s!"  left open in all: {fl (a.cutMass + a.depthM + a.decidedM + a.otherM + a.landM)}"
  IO.println s!"  to a wider clean tape, by landings on the way: {(a.lands.toList.map fe).take 4}"
  IO.println s!"  cut, by landings on the way: {(a.cutLands.toList.map fe).take 4}"
