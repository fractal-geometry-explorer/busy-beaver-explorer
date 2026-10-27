import EndgameStart
import BB6.PassTree
import Std.Data.HashMap
open BB6 BB6.Sym

/-! # Shapes on the cut paths of the pass-start trees (untrusted driver: statistics only)

Walks the pass-start trees step by step as `PTree.explore` builds them (as `../lean/PassStats.lean` does, with
`passCleaves` cleaves on a path) and, for every cut leaf, records the round-start shape at the cut (the mark types
after the gap), whether the path met an extra-wall pass start (four walls, `G W W W W`), whether it met any round
shape of the extra-wall loop or its way in (`G W W W W`, `G B W W`, `G M M W W`, `G M W W W`, `G M B W`), and the most
walls in one round start on the path.  Measures are fractions of the start class; the slices of the cleaves have
measure 0 and their cut leaves are only counted.  No proof reads anything it prints.

usage (after `check.sh`, with `thm/EndgameStart.lean` compiled to `out/`, from `../lean`):
  lean --load-dynlib=cbuild/so/libBB6.so --run ../lock/PassShapes.lean d R ...
each `R` a right end below 178, or `sym` for the tree of every R ≥ 178. -/

/-- The cleaves on a path, as in `../lean/thm/PassHalt.lean` (which this driver does not import, to spare building the
loop's kernel-checked trees). -/
def passCleaves : Nat := 8

def tchar : MarkT → Char
  | .G => 'G' | .M => 'M' | .W => 'W' | .B => 'B'

def shapeOf (ss : List SMark) : String := String.ofList (ss.map (fun m => tchar m.t))

def nW (ss : List SMark) : Nat := (ss.filter (fun m => m.t == .W)).length

/-- The round shapes of the extra-wall loop (P and Q) and of its way in. -/
def isEW (ss : List SMark) : Bool :=
  let sh := shapeOf ss
  sh == "WWWW" || sh == "BWW" || sh == "MMWW" || sh == "MWWW" || sh == "MBW"

/-- What a path has met: four walls, any extra-wall shape, the most walls in one round start. -/
structure PF where
  four : Bool := false
  ew : Bool := false
  mw : Nat := 0

structure PAcc where
  shapes : Std.HashMap String (Nat × Nat) := {}
  maxW : Array Nat := Array.replicate 20 0
  cuts : Nat := 0
  mass : Nat := 0
  dec : Nat := 0
  four : Nat := 0
  fourMass : Nat := 0
  ewMass : Nat := 0
  sliceCuts : Nat := 0
  sliceFour : Nat := 0

def bump (m : Std.HashMap String (Nat × Nat)) (k : String) (D : Nat) : Std.HashMap String (Nat × Nat) :=
  let (a, b) := m.getD k (0, 0)
  m.insert k (a + 1, b + 2 ^ D)

def cutAt (inSlice : Bool) (ss : List SMark) (D : Nat) (pf : PF) (decided : Bool) (acc : PAcc) : PAcc :=
  if inSlice then
    { acc with sliceCuts := acc.sliceCuts + 1, sliceFour := acc.sliceFour + (if pf.four then 1 else 0) }
  else
    { acc with shapes := bump acc.shapes (shapeOf ss ++ (if decided then " (decided)" else "")) D,
               cuts := acc.cuts + 1, mass := acc.mass + 2 ^ D,
               maxW := acc.maxW.modify (min pf.mw 19) (· + 2 ^ D),
               four := acc.four + (if pf.four then 1 else 0), fourMass := acc.fourMass + (if pf.four then 2 ^ D else 0),
               ewMass := acc.ewMass + (if pf.ew then 2 ^ D else 0),
               dec := acc.dec + (if decided then 2 ^ D else 0) }

partial def walk (k : Nat) (cls : Option (Int × Int)) (inSlice : Bool) :
    Nat → Nat → Nat → Nat → Bool → Bool → Nat → List SMark → YForm → List YForm → SForms → PF → PAcc → PAcc
  | 0, _, D, _, _, _, _, ss, _, _, _, pf, acc => cutAt inSlice ss D pf false acc
  | S + 1, d, D, nb, wf, cf, n, ss, sW, ts, f, pf, acc =>
    let pf := { four := pf.four || (ss.length == 4 && nW ss == 4), ew := pf.ew || isEW ss, mw := max pf.mw (nW ss) }
    match passAct 448 1000 k cls (nb != 0) wf cf n ss sW ts f with
    | .land => acc
    | .clean => acc
    | .close => acc
    | .cut =>
      let decided := (wf || symRightOK ts 448 (YForm.const 4) false sW ss) &&
        (match symRoundsZ ts 448 1000 1 ss sW with | some (.newRound _ _) => false | some _ => true | none => false)
      cutAt inSlice ss D pf decided acc
    | .adv ss' sW' => walk k cls inSlice S d D nb true (cf && meetsGe3 448 1000 ts ss sW) (n + 1) ss' sW' ts f pf acc
    | .split i =>
      match d with
      | 0 => cutAt inSlice ss D pf false acc
      | d + 1 =>
        let acc := walk k cls inSlice S d (D - 1) nb wf cf n (substL ss i 0) (sW.subst i 0) (substT ts i 0)
          (f.subst i 0) pf acc
        walk k cls inSlice S d (D - 1) nb wf cf n (substL ss i 1) (sW.subst i 1) (substT ts i 1) (f.subst i 1) pf acc
    | .skew i j s =>
      walk k cls inSlice S d D nb wf cf n (skewL ss i j s) (sW.skew i j s) (skewT ts i j s) (f.skew i j s) pf acc
    | .cleave i c σ j0 j1 =>
      let acc := walk k cls true S d D (nb - 1) wf cf n (pinL ss i c) (sW.pin i c) ((pinT ts i c).eraseIdx j0)
        (f.pin i c) pf acc
      walk k cls inSlice S d D (nb - 1) wf cf n ss sW (ts.set j1 ((cleaveBnd i c σ).addc (448 - 1))) f pf acc

def runOne (d : Nat) (which : String) : IO Unit := do
  let a := if which == "sym" then
      walk 4 none false (10000 + d) d d passCleaves false true 0 symStart.1 symStart.2.1 symStart.2.2 symStartE.2 {} {}
    else
      let R := which.toNat!
      walk 3 (closeClass R) false (10000 + d) d d passCleaves false true 0 (startR R).1 (startR R).2.1 (startR R).2.2
        (startE R).2 {} {}
  let fl (x : Nat) : Float := x.toFloat / (2 : Float) ^ d.toFloat
  IO.println s!"{which} d={d}: cut leaves {a.cuts}, measure {fl a.mass} (decided {fl a.dec}); met four walls: {a.four} leaves, measure {fl a.fourMass}; met any extra-wall shape: measure {fl a.ewMass}; slice cut leaves {a.sliceCuts} (four walls: {a.sliceFour})"
  IO.println s!"  most walls in one round start on the path, by measure: {(List.range 20).map (fun i => (i, fl a.maxW[i]!)) |>.filter (fun x => x.2 > 0)}"
  let l : Array (String × Nat × Nat) := a.shapes.toList.toArray.qsort (fun x y => x.2.2 > y.2.2)
  for (s, c, m) in (l.toList.take 12) do
    IO.println s!"    G {s}: {c} (measure {fl m})"

def main (args : List String) : IO Unit := do
  let d := (args.getD 0 "12").toNat!
  for w in args.drop 1 do
    runOne d w
    (← IO.getStdout).flush
