import BB6.CleanEntryTree
import BB6.EntryTree
import BB6.RouteEntry
import Std.Data.HashMap
open BB6 BB6.Sym

/-! # What the cut paths of the route tree and the clean-tape tree are made of (untrusted driver: statistics only)

`route Γ d` walks the route tree with loop entries (`routeTreeE Γ d`, `../lean/thm/RouteEntryTheorem.lean`) step by
step as `RTree.exploreE` builds it; `clean Γ d` walks the clean-tape tree with loop entries (`cleanTreeGE Γ d`) as
`../lean/EntryStats.lean` does.  For every cut leaf it records the shape at the cut, the number of rounds, the most
marks in one round start, and the number of returns to a two-marker state (`G M M`, both markers free) on the path;
for the first `k` cut leaves (and a sample of later ones) it prints the whole path: each round start's shape and the
positions of its marks as exact affine functions of the start's numbers (α·m + β·E + γ in the route tree, α·W + γ in
the clean-tape tree; `posStr`).  No proof reads anything it prints.

usage (from `../lean`, after `check_route.sh --fast`):
  lean --load-dynlib=cbuild/so/libBB6.so --run ../lock/PathSamples.lean route 67108864 30 8
  lean --load-dynlib=cbuild/so/libBB6.so --run ../lock/PathSamples.lean clean 2199023255552 30 8 -/

def tchar : MarkT → Char
  | .G => 'G' | .M => 'M' | .W => 'W' | .B => 'B'

def shapeOf (ss : List SMark) : String := String.ofList (ss.map (fun m => tchar m.t))

/-- A rational number, reduced, as a string. -/
def ratStr (n : Int) (d : Int) : String :=
  if d == 0 then "?" else
    let g := (Int.gcd n d : Int)
    let n := n / g
    let d := d / g
    let (n, d) := if d < 0 then (-n, -d) else (n, d)
    if d == 1 then toString n else s!"{n}/{d}"

def coef (f : YForm) (i : Nat) : Int := f.c.getD i 0

/-- A position as an exact affine function of the start's coordinates: for the route tree p = α·m + β·E + γ (the
start's marker m and width E, carried as forms `o = [m0, E0]` in the current coordinates), for the clean-tape tree
p = α·W + γ (`o = [W0]`). -/
def posStr (o : List YForm) (p : YForm) : String :=
  match o with
  | [m0, e0] =>
    let a0 := coef m0 0; let a1 := coef m0 1; let b0 := coef e0 0; let b1 := coef e0 1
    let p0 := coef p 0; let p1 := coef p 1
    let det := a0 * b1 - a1 * b0
    -- α = (p0 b1 − p1 b0)/det, β = (a0 p1 − a1 p0)/det, γ = p.k − α m0.k − β e0.k
    let an := p0 * b1 - p1 * b0
    let bn := a0 * p1 - a1 * p0
    let gn := p.k * det - an * m0.k - bn * e0.k
    s!"({ratStr an det})m+({ratStr bn det})E+{ratStr gn det}"
  | [w0] =>
    let a := coef w0 0
    let pn := coef p 0
    let gn := p.k * a - pn * w0.k
    s!"({ratStr pn a})W+{ratStr gn a}"
  | _ => "?"

def describe (o : List YForm) (ss : List SMark) (sW : YForm) : String :=
  shapeOf ss ++ " [" ++ ", ".intercalate (ss.map (fun m => posStr o m.p)) ++ "; W=" ++ posStr o sW ++ "]"

structure PAcc where
  shapes : Std.HashMap String (Nat × Nat) := {}
  rounds : Array Nat := Array.replicate 64 0
  maxMarks : Array Nat := Array.replicate 32 0
  returns : Array Nat := Array.replicate 64 0
  cuts : Nat := 0
  mass : Nat := 0
  printed : Nat := 0
  seen : Nat := 0
  lines : Array String := #[]

def bump (m : Std.HashMap String (Nat × Nat)) (k : String) (D : Nat) : Std.HashMap String (Nat × Nat) :=
  let (a, b) := m.getD k (0, 0)
  m.insert k (a + 1, b + 2 ^ D)

/-- Path record: the round starts described so far (newest first), rounds, most marks, two-marker returns. -/
structure PF where
  path : List String := []
  r : Nat := 0
  mm : Nat := 0
  ret : Nat := 0

/-- Note a round start on the path (once: a split re-visits the same round start in narrower coordinates, which
describes it the same way in the start's coordinates). -/
def note (o : List YForm) (ss : List SMark) (sW : YForm) (moved : Bool) (pf : PF) : PF :=
  let isGMM := ss.length == 2 && ss.all (·.t == .M)
  let s := s!"{pf.r}: " ++ describe o ss sW
  if pf.path.head? == some s then pf else
  { path := s :: pf.path, r := pf.r, mm := max pf.mm ss.length,
    ret := pf.ret + (if moved && isGMM then 1 else 0) }

def cutAt (k every : Nat) (ss : List SMark) (D : Nat) (pf : PF) (acc : PAcc) : PAcc :=
  let acc := { acc with shapes := bump acc.shapes (shapeOf ss) D, cuts := acc.cuts + 1, mass := acc.mass + 2 ^ D,
                        rounds := acc.rounds.modify (min (pf.r / 8) 63) (· + 1),
                        maxMarks := acc.maxMarks.modify (min pf.mm 31) (· + 1),
                        returns := acc.returns.modify (min pf.ret 63) (· + 1), seen := acc.seen + 1 }
  if acc.printed < k && (acc.seen % every == 1 || every == 1) then
    let body := "\n    ".intercalate pf.path.reverse
    { acc with printed := acc.printed + 1,
               lines := acc.lines.push s!"cut leaf {acc.seen} (measure 2^{D}): {pf.r} rounds, {pf.ret} returns to G M M, cut at G {shapeOf ss}:\n    {body}" }
  else acc

/-- The route tree with loop entries (`RTree.exploreE Γ 1000 (entryOK Γ)`), walked; `o` carries the start's marker and
width in the current coordinates. -/
partial def walkR (Γ : Int) (k every : Nat) : Nat → Nat → Bool → List SMark → YForm → List YForm → List YForm → Nat →
    PF → PAcc → PAcc
  | 0, _, _, ss, _, _, _, D, pf, acc => cutAt k every ss D pf acc
  | S + 1, d, moved, ss, sW, ts, o, D, pf, acc =>
    if (moved && symClean ss sW) = true then acc else
    if entryOK Γ ts ss sW = true then acc else
    let pf := note o ss sW moved pf
    match symRoundZ ts Γ 1000 [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => walkR Γ k every S d true ss' sW' ts o D { pf with r := pf.r + 1 } acc
    | some _ => cutAt k every ss D pf acc
    | none =>
      match d with
      | 0 => cutAt k every ss D pf acc
      | d + 1 =>
        match splitStep ts Γ ss sW with
        | none => cutAt k every ss D pf acc
        | some (none, i) =>
          if i < 2 then
            let acc := walkR Γ k every S d moved (substL ss i 0) (sW.subst i 0) (substT ts i 0) (substT o i 0) (D - 1)
              pf acc
            walkR Γ k every S d moved (substL ss i 1) (sW.subst i 1) (substT ts i 1) (substT o i 1) (D - 1) pf acc
          else cutAt k every ss D pf acc
        | some (some (j, s), i) =>
          if i < 2 then
            let ss2 := shearL ss j s; let sW2 := sW.shear j s; let ts2 := shearT ts j s; let o2 := shearT o j s
            let acc := walkR Γ k every S d moved (substL ss2 i 0) (sW2.subst i 0) (substT ts2 i 0) (substT o2 i 0)
              (D - 1) pf acc
            walkR Γ k every S d moved (substL ss2 i 1) (sW2.subst i 1) (substT ts2 i 1) (substT o2 i 1) (D - 1) pf acc
          else cutAt k every ss D pf acc

def rtStart : List SMark × YForm × List YForm × List YForm :=
  let m : YForm := ⟨0, [2, 0]⟩
  let E : YForm := ⟨1, [0, 2]⟩
  ([⟨.M, m⟩, ⟨.M, E.addc (-2)⟩], E, [m, E.sub m], [m, E])

def ctS : List SMark × YForm × List YForm :=
  let W : YForm := ⟨0, [2, 0]⟩
  ([⟨.M, W.addc (-2)⟩], W, [W])

/-- The clean-tape tree with loop entries, walked as `EntryStats.lean` walks it; `o` carries the start's width. -/
partial def walkC (Γ : Int) (fuel B k every : Nat) : Nat → Nat → Nat → Bool → List SMark → YForm → YForm →
    List YForm → List YForm → Nat → PF → PAcc → PAcc
  | 0, _, _, _, ss, _, _, _, _, D, pf, acc => cutAt k every ss D pf acc
  | S + 1, d, nd, moved, ss, sW, w0, ts, o, D, pf, acc =>
    if (moved && symClean1 ss sW && widerB sW w0 ts Γ) = true then acc else
    if cleanEntryOK Γ ts ss sW w0 = true then acc else
    let pf := note o ss sW moved pf
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') =>
      walkC Γ fuel B k every S d nd true ss' sW' w0 ts o D { pf with r := pf.r + 1 } acc
    | some _ => cutAt k every ss D pf acc
    | none =>
      match splitStep ts Γ ss sW with
      | none =>
        match nd, coneMin ts Γ with
        | nd + 1, some z =>
          if dropOK Γ fuel z ss sW w0 ts = true then
            walkC Γ fuel B k every S d nd moved ss sW w0 [dropCone Γ z] o D pf acc
          else cutAt k every ss D pf acc
        | _, _ => cutAt k every ss D pf acc
      | some (none, i) =>
        match d with
        | 0 => cutAt k every ss D pf acc
        | d + 1 =>
          let acc := walkC Γ fuel B k every S d B moved (substL ss i 0) (sW.subst i 0) (w0.subst i 0) (substT ts i 0)
            (substT o i 0) (D - 1) pf acc
          walkC Γ fuel B k every S d B moved (substL ss i 1) (sW.subst i 1) (w0.subst i 1) (substT ts i 1)
            (substT o i 1) (D - 1) pf acc
      | some (some (j, s), i) =>
        match d with
        | 0 => cutAt k every ss D pf acc
        | d + 1 =>
          let ss2 := shearL ss j s; let sW2 := sW.shear j s; let w02 := w0.shear j s; let ts2 := shearT ts j s
          let o2 := shearT o j s
          let acc := walkC Γ fuel B k every S d B moved (substL ss2 i 0) (sW2.subst i 0) (w02.subst i 0)
            (substT ts2 i 0) (substT o2 i 0) (D - 1) pf acc
          walkC Γ fuel B k every S d B moved (substL ss2 i 1) (sW2.subst i 1) (w02.subst i 1) (substT ts2 i 1)
            (substT o2 i 1) (D - 1) pf acc

def main (args : List String) : IO Unit := do
  let kind := args.getD 0 "route"
  let Γ := (args.getD 1 "67108864").toNat!
  let d := (args.getD 2 "24").toNat!
  let k := (args.getD 3 "8").toNat!
  let every := (args.getD 4 "1").toNat!
  let a := if kind == "route" then
      walkR Γ k every (10000 + d) d false rtStart.1 rtStart.2.1 rtStart.2.2.1 rtStart.2.2.2 d {} {}
    else
      walkC Γ 1000 4 k every (10000 + d) d 4 false ctS.1 ctS.2.1 ctS.2.1 ctS.2.2 [ctS.2.1] d {} {}
  IO.println s!"{kind}, Γ = {Γ}, d = {d}: cut leaves {a.cuts} (measure {a.mass}/2^{d})"
  IO.println s!"  rounds on the path, in bins of 8 (first of the bin, cut leaves): {(List.range 64).map (fun i => (i*8, a.rounds[i]!)) |>.filter (fun x => x.2 > 0)}"
  IO.println s!"  most marks in one round start (marks, cut leaves): {(List.range 32).map (fun i => (i, a.maxMarks[i]!)) |>.filter (fun x => x.2 > 0)}"
  IO.println s!"  returns to G M M on the path (returns, cut leaves): {(List.range 64).map (fun i => (i, a.returns[i]!)) |>.filter (fun x => x.2 > 0)}"
  let l : Array (String × Nat × Nat) := a.shapes.toList.toArray.qsort (fun x y => x.2.1 > y.2.1)
  IO.println s!"  shapes at the cut: {l.size}"
  for (s, c, m) in (l.toList.take 15) do
    IO.println s!"    G {s}: {c} (measure {m}/2^{d})"
  for line in a.lines do IO.println line
