import BB6.RouteTree
open BB6 BB6.Sym

/-! # Building the route tree (untrusted driver; every verdict is re-checked by `RTree.ok`)

The start class is the two-marker state G 1, M m, M E − 2 with width E, m = 2 y₀ and E = 1 + 2 y₁; the cone gaps are
m and E − m.  The driver runs rounds; when a round is not decided it finds the first meeting whose distance d is not
decided modulo 2 or 4 and splits the class on that digit (a shear first when both coordinates enter the digit, so
that every split halves the class as in the Python certificate); it stops a path at the first clean tape after at
least one round (`clean`), or with a `cut` once the path has made `maxDepth` splits.

usage: ExploreRT maxDepth Γ out.txt   (writes the serialized tree; prints the leaf counts and the cut measure) -/

def shapeOf (ss : List SMark) : String := "G" ++ String.join (ss.map (fun m => match m.t with
  | .G => "G" | .M => "M" | .W => "W" | .B => "B"))

/-- The first residue test of a round that the class does not decide: the form and the modulus (2 or 4). -/
partial def undecidedResidue (ts : List YForm) (Γ : Int) (sL : List SMark) (sg : YForm) (sR : List SMark) (sW : YForm)
    (fuel : Nat) : Option (YForm × Int) :=
  if fuel = 0 then none else
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
    | some (.gap a b c d) => undecidedResidue ts Γ a b c d (fuel - 1)
    | some (.pkt sL' sx sR' sW') =>
      match symPktBack ts Γ sL' sx sR' sW' with
      | some (.gap a b c d) => undecidedResidue ts Γ a b c d (fuel - 1)
      | _ => none
    | some (.pktM sL' sx sR' sW') =>
      match symPktLand ts Γ sL' sx sR' sW' with
      | some (.gap a b c d) => undecidedResidue ts Γ a b c d (fuel - 1)
      | _ => none
    | _ => none

structure Stats where
  clean : Nat := 0
  cut : Nat := 0
  fail : Nat := 0
  maxRounds : Nat := 0
  failMsgs : List String := []

def ser : RTree → List String → List String
  | .cut, acc => "C" :: acc
  | .clean, acc => "K" :: acc
  | .adv n t, acc => ("A" ++ toString n) :: ser t acc
  | .split i t0 t1, acc => ("S" ++ toString i) :: ser t0 (ser t1 acc)
  | .shear i s t, acc => ("H" ++ toString i ++ "," ++ toString s) :: ser t acc

/-- How to split so that `f` is decided modulo `m`: a shear (if both coefficients enter the digit), then a split. -/
def chooseSplit (f : YForm) (m : Int) : Option (Option (Nat × Int) × Nat) :=
  let h := if m == 4 then f.c.map (· / 2) else f.c
  let a := h.getD 0 0 % 2
  let b := h.getD 1 0 % 2
  if a != 0 && b != 0 then some (some (0, -1), 0)
  else if a != 0 then some (none, 0)
  else if b != 0 then some (none, 1)
  else none

partial def build (Γ : Int) (maxDepth : Nat) (ss : List SMark) (sW : YForm) (ts : List YForm) (moved : Bool)
    (depth : Nat) (st : Stats) (rounds0 : Nat) : RTree × Stats := Id.run do
  let mut cur := ss
  let mut cw := sW
  let mut n := 0
  let mut st := st
  while true do
    if (moved || n > 0) && symClean cur cw then
      st := { st with clean := st.clean + 1, maxRounds := max st.maxRounds (rounds0 + n) }
      return (.adv n .clean, st)
    if rounds0 + n > 5000 then
      st := { st with fail := st.fail + 1, failMsgs := (st.failMsgs ++ ["round guard"]).take 20 }
      return (.adv n .cut, st)
    match symRoundZ ts Γ 1000 [] (YForm.const 1) cur cw with
    | some (.newRound a b) => cur := a; cw := b; n := n + 1
    | some r =>
      let msg := match r with | .halt => "halt" | .uncovered => "uncovered" | _ => "gap"
      st := { st with fail := st.fail + 1, failMsgs := (st.failMsgs ++ [s!"{msg} at round {rounds0 + n + 1} depth {depth} {shapeOf cur}"]).take 20 }
      return (.adv n .cut, st)
    | none =>
      if depth ≥ maxDepth then
        st := { st with cut := st.cut + 1 }
        return (.adv n .cut, st)
      match undecidedResidue ts Γ [] (YForm.const 1) cur cw 2000 with
      | none =>
        st := { st with fail := st.fail + 1, failMsgs := (st.failMsgs ++ [s!"undecided order at round {rounds0 + n + 1} depth {depth} {shapeOf cur}"]).take 20 }
        return (.adv n .cut, st)
      | some (f, m) =>
        match chooseSplit f m with
        | none =>
          st := { st with fail := st.fail + 1, failMsgs := (st.failMsgs ++ ["no split"]).take 20 }
          return (.adv n .cut, st)
        | some (sh, i) =>
          let (cur', cw', ts') := match sh with
            | some (j, s) => (shearL cur j s, cw.shear j s, shearT ts j s)
            | none => (cur, cw, ts)
          let mv := moved || n > 0
          let (t0, st0) := build Γ maxDepth (substL cur' i 0) (cw'.subst i 0) (substT ts' i 0) mv (depth + 1) st (rounds0 + n)
          let (t1, st1) := build Γ maxDepth (substL cur' i 1) (cw'.subst i 1) (substT ts' i 1) mv (depth + 1) st0 (rounds0 + n)
          let sp : RTree := .split i t0 t1
          let node : RTree := match sh with
            | some (j, s) => .shear j s sp
            | none => sp
          return (.adv n node, st1)
  return (.cut, st)

def rtStart : List SMark × YForm × List YForm :=
  let m : YForm := ⟨0, [2, 0]⟩
  let E : YForm := ⟨1, [0, 2]⟩
  ([⟨.M, m⟩, ⟨.M, E.addc (-2)⟩], E, [m, E.sub m])

def main (args : List String) : IO Unit := do
  let maxDepth := (args.getD 0 "20").toNat!
  let Γ : Int := (args.getD 1 "8000000").toInt!
  let out := args.getD 2 "route_tree.txt"
  let (ss, sW, ts) := rtStart
  let (t, st) := build Γ maxDepth ss sW ts false 0 {} 0
  IO.println s!"depth {maxDepth}, Γ = {Γ}: leaves clean {st.clean}, cut {st.cut}, failures {st.fail}; most rounds on a path {st.maxRounds}"
  for msg in st.failMsgs do IO.println s!"  {msg}"
  let cm := t.cutMass maxDepth
  IO.println s!"cut measure {cm} / 2^{maxDepth} = {cm.toFloat / (2 ^ maxDepth : Nat).toFloat}"
  IO.println s!"depth {t.depth}, leaves {t.leaves}"
  let ok := t.ok Γ 1000 false ss sW ts
  IO.println s!"RTree.ok (proved check, run natively here): {ok}"
  IO.FS.writeFile out (String.intercalate " " (ser t []))
