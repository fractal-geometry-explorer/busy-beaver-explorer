import BB6.CleanEntryTree
import Std.Data.HashMap
open BB6 BB6.Sym

/-! # Shapes on the cut paths of the clean-tape tree with loop entries (untrusted driver: statistics only)

Walks the clean-tape tree with loop entries (`cleanTreeGE Γ d`, `../lean/thm/CleanEntryTheorem.lean`) exactly as
`../lean/EntryStats.lean` does, and for every cut leaf records the round-start shape at the cut (the mark types after
the gap), whether the path met a round shape of the extra-wall loop or its way in (`G W W W W`, `G B W W`,
`G M M W W`, `G M W W W`, `G M B W`; the first one met is tallied), the most walls in one round start on the path (four
only at `G W W W W`, the extra-wall pass start), and the number of rounds on the path.  No proof reads anything it
prints.

usage (after `check_route.sh --fast` has built the shared library, from `../lean`):
  lean --load-dynlib=cbuild/so/libBB6.so --run ../lock/ShapeStats.lean 2199023255552 36 -/

def ctS : List SMark × YForm × List YForm :=
  let W : YForm := ⟨0, [2, 0]⟩
  ([⟨.M, W.addc (-2)⟩], W, [W])

def tchar : MarkT → Char
  | .G => 'G' | .M => 'M' | .W => 'W' | .B => 'B'

def shapeOf (ss : List SMark) : String := String.ofList (ss.map (fun m => tchar m.t))

def nW (ss : List SMark) : Nat := (ss.filter (fun m => m.t == .W)).length

structure SAcc where
  shapes : Std.HashMap String (Nat × Nat) := {}
  pathEW : Std.HashMap String (Nat × Nat) := {}
  maxW : Array Nat := Array.replicate 20 0
  maxWm : Array Nat := Array.replicate 20 0
  ew : Nat := 0
  ewMass : Nat := 0
  cuts : Nat := 0
  mass : Nat := 0
  rounds : Array Nat := Array.replicate 64 0

def bump (m : Std.HashMap String (Nat × Nat)) (k : String) (D : Nat) : Std.HashMap String (Nat × Nat) :=
  let (a, b) := m.getD k (0, 0)
  m.insert k (a + 1, b + 2 ^ D)

/-- path flags: (met G W W W W, most walls, rounds, first extra-wall shape seen) -/
structure PF where
  ew : Bool := false
  mw : Nat := 0
  r : Nat := 0
  first : String := ""

def cutAt (ss : List SMark) (D : Nat) (pf : PF) (acc : SAcc) : SAcc :=
  let s := shapeOf ss
  { acc with shapes := bump acc.shapes s D, cuts := acc.cuts + 1, mass := acc.mass + 2 ^ D,
             maxW := acc.maxW.modify (min pf.mw 19) (· + 1), maxWm := acc.maxWm.modify (min pf.mw 19) (· + 2 ^ D),
             ew := acc.ew + (if pf.ew then 1 else 0), ewMass := acc.ewMass + (if pf.ew then 2 ^ D else 0),
             rounds := acc.rounds.modify (min (pf.r / 16) 63) (· + 1),
             pathEW := if pf.ew then bump acc.pathEW pf.first D else acc.pathEW }

def note (ss : List SMark) (pf : PF) : PF :=
  let w := nW ss
  let sh := shapeOf ss
  let isEW := sh == "WWWW" || sh == "BWW" || sh == "MMWW" || sh == "MWWW" || sh == "MBW"
  { pf with mw := max pf.mw w, ew := pf.ew || isEW, first := if pf.ew || !isEW then pf.first else sh }

partial def walk (Γ : Int) (fuel B : Nat) : Nat → Nat → Nat → Bool → List SMark → YForm → YForm → List YForm → Nat →
    PF → SAcc → SAcc
  | 0, _, _, _, ss, _, _, _, D, pf, acc => cutAt ss D pf acc
  | S + 1, d, nd, moved, ss, sW, w0, ts, D, pf, acc =>
    if (moved && symClean1 ss sW && widerB sW w0 ts Γ) = true then acc else
    if cleanEntryOK Γ ts ss sW w0 = true then acc else
    let pf := note ss pf
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => walk Γ fuel B S d nd true ss' sW' w0 ts D { pf with r := pf.r + 1 } acc
    | some _ => cutAt ss D pf acc
    | none =>
      match splitStep ts Γ ss sW with
      | none =>
        match nd, coneMin ts Γ with
        | nd + 1, some z =>
          if dropOK Γ fuel z ss sW w0 ts = true then
            walk Γ fuel B S d nd moved ss sW w0 [dropCone Γ z] D pf acc
          else cutAt ss D pf acc
        | _, _ => cutAt ss D pf acc
      | some (none, i) =>
        match d with
        | 0 => cutAt ss D pf acc
        | d + 1 =>
          let acc := walk Γ fuel B S d B moved (substL ss i 0) (sW.subst i 0) (w0.subst i 0) (substT ts i 0) (D - 1)
            pf acc
          walk Γ fuel B S d B moved (substL ss i 1) (sW.subst i 1) (w0.subst i 1) (substT ts i 1) (D - 1) pf acc
      | some (some (j, s), i) =>
        match d with
        | 0 => cutAt ss D pf acc
        | d + 1 =>
          let ss2 := shearL ss j s; let sW2 := sW.shear j s; let w02 := w0.shear j s; let ts2 := shearT ts j s
          let acc := walk Γ fuel B S d B moved (substL ss2 i 0) (sW2.subst i 0) (w02.subst i 0) (substT ts2 i 0) (D - 1)
            pf acc
          walk Γ fuel B S d B moved (substL ss2 i 1) (sW2.subst i 1) (w02.subst i 1) (substT ts2 i 1) (D - 1) pf acc

def main (args : List String) : IO Unit := do
  let Γ := (args.getD 0 "2199023255552").toNat!
  let d := (args.getD 1 "28").toNat!
  let a := walk Γ 1000 4 (10000 + d) d 4 false ctS.1 ctS.2.1 ctS.2.1 ctS.2.2 d {} {}
  IO.println s!"Γ = {Γ}, d = {d}: cut leaves {a.cuts} (measure {a.mass}/2^{d})"
  IO.println s!"  paths that met an extra-wall shape (G W W W W, G B W W, G M M W W, G M W W W, G M B W): {a.ew} (measure {a.ewMass}/2^{d})"
  IO.println s!"    by the first one met: {a.pathEW.toList}"
  IO.println s!"  most walls in one round start on the path (walls, cut leaves, measure over 2^{d}): {(List.range 20).map (fun i => (i, a.maxW[i]!, a.maxWm[i]!)) |>.filter (fun x => x.2.1 > 0)}"
  IO.println s!"  rounds on the path, in bins of 16 (first of the bin, cut leaves): {(List.range 64).map (fun i => (i*16, a.rounds[i]!)) |>.filter (fun x => x.2 > 0)}"
  let l : Array (String × Nat × Nat) := (a.shapes.toList.toArray.qsort (fun x y => x.2.1 > y.2.1))
  IO.println s!"  shapes at the cut: {l.size}"
  for (s, c, m) in (l.toList.take 40) do
    IO.println s!"    G {s}: {c} (measure {m}/2^{d})"
