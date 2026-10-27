import EndgameStart
import BB6.PassTree
open BB6 BB6.Sym

/-! # The pass-start trees' leaves by kind (untrusted, for looking)

usage: `lean --load-dynlib=cbuild/so/libBB6all.so --run PassStats.lean d R ...` (after `./check_end.sh`; each `R` a
right end below 178, `sym` for the tree of every R ≥ 178, or `all` for every even R from 2 to 176).  For the pass-start
tree `d` splits deep (`PTree.explore`, as in `thm/PassHalt.lean`), prints the measure of its leaves by kind, as
fractions of the start class: landings, clean tapes, close leaves, and the cut leaves by why they are cut: the depth
ran out (`depth`), the round is decided as something other than a new round start, a halt or a close the model does
not cover, with the left countdown outside the closing class (`decided`), or the round is undecided and its first
undecided residue is not found (`other`). -/

/-- The leaves' measure (numerators over 2^D): cut at depth, cut at a decided round, cut otherwise, landing, clean,
close. -/
def passStats (k : Nat) (cls : Option (Int × Int)) :
    Nat → Nat → Nat → Bool → Bool → Nat → List SMark → YForm → List YForm → SForms →
      Nat × Nat × Nat × Nat × Nat × Nat
  | 0, _, D, _, _, _, _, _, _, _ => (0, 0, 2 ^ D, 0, 0, 0)
  | S + 1, d, D, wf, cf, n, ss, sW, ts, f =>
    match passAct 448 1000 k cls wf cf n ss sW ts f with
    | .land => (0, 0, 0, 2 ^ D, 0, 0)
    | .clean => (0, 0, 0, 0, 2 ^ D, 0)
    | .close => (0, 0, 0, 0, 0, 2 ^ D)
    | .cut =>
      let decided := (wf || symRightOK ts 448 (YForm.const 4) false sW ss) &&
        (match symRoundsZ ts 448 1000 1 ss sW with | some (.newRound _ _) => false | some _ => true | none => false)
      if decided then (0, 2 ^ D, 0, 0, 0, 0) else (0, 0, 2 ^ D, 0, 0, 0)
    | .adv ss' sW' => passStats k cls S d D true (cf && meetsGe3 448 1000 ts ss sW) (n + 1) ss' sW' ts f
    | .split i =>
      match d with
      | 0 => (2 ^ D, 0, 0, 0, 0, 0)
      | d + 1 =>
        let a := passStats k cls S d (D - 1) wf cf n (substL ss i 0) (sW.subst i 0) (substT ts i 0) (f.subst i 0)
        let b := passStats k cls S d (D - 1) wf cf n (substL ss i 1) (sW.subst i 1) (substT ts i 1) (f.subst i 1)
        (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2.1 + b.2.2.2.1, a.2.2.2.2.1 + b.2.2.2.2.1,
          a.2.2.2.2.2 + b.2.2.2.2.2)
    | .skew i j => passStats k cls S d D wf cf n (skewL ss i j 1) (sW.skew i j 1) (skewT ts i j 1) (f.skew i j 1)

def runOne (d : Nat) (which : String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := if which == "sym" then
      passStats 4 none (10000 + d) d d false true 0 symStart.1 symStart.2.1 symStart.2.2 symStartE.2
    else
      let R := which.toNat!
      passStats 3 (closeClass R) (10000 + d) d d false true 0 (startR R).1 (startR R).2.1 (startR R).2.2 (startE R).2
  let (dep, dec, oth, land, clean, close) := r
  let t1 ← IO.monoMsNow
  let fl (x : Nat) : Float := x.toFloat / (2 : Float) ^ d.toFloat
  IO.println s!"{which} d={d}: cut {fl (dep + dec + oth)} (depth {fl dep}, decided {fl dec}, other {fl oth}), landing {fl land}, clean {fl clean}, close {fl close} ({t1 - t0} ms)"

def main (args : List String) : IO Unit := do
  let d := (args.getD 0 "12").toNat!
  let rest := args.drop 1
  let ws := if rest == ["all"] then (List.range 88).map (fun i => toString (2 * (i + 1))) else rest
  for w in ws do
    runOne d w
    (← IO.getStdout).flush
