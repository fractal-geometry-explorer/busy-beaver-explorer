import PassHalt
import BB6.PassTree
open BB6 BB6.Sym

/-! # The pass-start trees' leaves by kind (untrusted, for looking)

usage: `lean --load-dynlib=cbuild/so/libBB6all.so --run PassStats.lean d R ...` (after `./check_end.sh`; each `R` a
right end below 178, `sym` for the tree of every R ≥ 178, or `all` for every even R from 2 to 176).  For the pass-start
tree `d` splits deep (`PTree.explore` with `passCleaves` = 8 cleaves on a path, as in `thm/PassHalt.lean`), prints the
measure of its leaves by kind, as fractions of the start class: landings, clean tapes, close leaves, and the cut
leaves by why they are cut: the depth ran out (`depth`), the round is decided as something other than a new round
start, a halt or a close the model does not cover, with the left countdown outside the closing class (`decided`), or
the round is undecided and neither a residue nor a cleave decides it (`other`).  The slices of the cleaves have
measure 0; their leaves are counted (`slice leaves`, of which `cut`). -/

structure PStats where
  dep : Nat := 0
  dec : Nat := 0
  oth : Nat := 0
  land : Nat := 0
  clean : Nat := 0
  close : Nat := 0
  cleaves : Nat := 0
  sliceLeaves : Nat := 0
  sliceCuts : Nat := 0

def PStats.add (a b : PStats) : PStats :=
  ⟨a.dep + b.dep, a.dec + b.dec, a.oth + b.oth, a.land + b.land, a.clean + b.clean, a.close + b.close,
    a.cleaves + b.cleaves, a.sliceLeaves + b.sliceLeaves, a.sliceCuts + b.sliceCuts⟩

/-- A leaf of measure 2^D (kind 0 depth, 1 decided, 2 other, 3 landing, 4 clean, 5 close), or a slice's leaf. -/
def PStats.leaf (inSlice : Bool) (D kind : Nat) : PStats :=
  if inSlice then
    let c : Nat := if kind ≤ 2 then 1 else 0
    { sliceLeaves := 1, sliceCuts := c }
  else match kind with
    | 0 => { dep := 2 ^ D }
    | 1 => { dec := 2 ^ D }
    | 2 => { oth := 2 ^ D }
    | 3 => { land := 2 ^ D }
    | 4 => { clean := 2 ^ D }
    | _ => { close := 2 ^ D }

/-- The leaves of `PTree.explore` (numerators over 2^D), step by step as it builds them. -/
def passStats (k : Nat) (cls : Option (Int × Int)) (inSlice : Bool) :
    Nat → Nat → Nat → Nat → Bool → Bool → Nat → List SMark → YForm → List YForm → SForms → PStats
  | 0, _, D, _, _, _, _, _, _, _, _ => .leaf inSlice D 0
  | S + 1, d, D, nb, wf, cf, n, ss, sW, ts, f =>
    match passAct 448 1000 k cls (nb != 0) wf cf n ss sW ts f with
    | .land => .leaf inSlice D 3
    | .clean => .leaf inSlice D 4
    | .close => .leaf inSlice D 5
    | .cut =>
      let decided := (wf || symRightOK ts 448 (YForm.const 4) false sW ss) &&
        (match symRoundsZ ts 448 1000 1 ss sW with | some (.newRound _ _) => false | some _ => true | none => false)
      .leaf inSlice D (if decided then 1 else 2)
    | .adv ss' sW' => passStats k cls inSlice S d D nb true (cf && meetsGe3 448 1000 ts ss sW) (n + 1) ss' sW' ts f
    | .split i =>
      match d with
      | 0 => .leaf inSlice D 0
      | d + 1 =>
        (passStats k cls inSlice S d (D - 1) nb wf cf n (substL ss i 0) (sW.subst i 0) (substT ts i 0)
          (f.subst i 0)).add
        (passStats k cls inSlice S d (D - 1) nb wf cf n (substL ss i 1) (sW.subst i 1) (substT ts i 1)
          (f.subst i 1))
    | .skew i j s =>
      passStats k cls inSlice S d D nb wf cf n (skewL ss i j s) (sW.skew i j s) (skewT ts i j s) (f.skew i j s)
    | .cleave i c σ j0 j1 =>
      let a := passStats k cls true S d D (nb - 1) wf cf n (pinL ss i c) (sW.pin i c) ((pinT ts i c).eraseIdx j0)
        (f.pin i c)
      let b := passStats k cls inSlice S d D (nb - 1) wf cf n ss sW (ts.set j1 ((cleaveBnd i c σ).addc (448 - 1))) f
      let r := a.add b
      { r with cleaves := r.cleaves + 1 }

def runOne (d : Nat) (which : String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := if which == "sym" then
      passStats 4 none false (10000 + d) d d passCleaves false true 0 symStart.1 symStart.2.1 symStart.2.2
        symStartE.2
    else
      let R := which.toNat!
      passStats 3 (closeClass R) false (10000 + d) d d passCleaves false true 0 (startR R).1 (startR R).2.1
        (startR R).2.2 (startE R).2
  let t1 ← IO.monoMsNow
  let fl (x : Nat) : Float := x.toFloat / (2 : Float) ^ d.toFloat
  IO.println s!"{which} d={d}: cut {fl (r.dep + r.dec + r.oth)} (depth {fl r.dep}, decided {fl r.dec}, other {fl r.oth}), landing {fl r.land}, clean {fl r.clean}, close {fl r.close}; cleaves {r.cleaves}, slice leaves {r.sliceLeaves} (cut {r.sliceCuts}) ({t1 - t0} ms)"

def main (args : List String) : IO Unit := do
  let d := (args.getD 0 "12").toNat!
  let rest := args.drop 1
  let ws := if rest == ["all"] then (List.range 88).map (fun i => toString (2 * (i + 1))) else rest
  for w in ws do
    runOne d w
    (← IO.getStdout).flush
