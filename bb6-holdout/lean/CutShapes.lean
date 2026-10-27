import CleanEntryTheorem
import BB6.MassPar
import Std.Data.HashMap
open BB6 BB6.Sym

/-! # What the clean-tape tree's cut paths look like (untrusted driver: statistics only)

Walks `cleanTreeGE Γ d` as `RTree.exploreWE` builds it (the top `e₀` = 8 split levels by `massPrefix`, the subtrees
below them as parallel tasks) and, at every cut leaf, records: the shape of the last round start (`GMM` is a
two-marker state: the gap, a marker, the end marker), how many rounds ago the path last passed a two-marker state, how
many two-marker states it passed, and whether the path ends in a periodic stretch of shapes (the last shapes repeat
with a period p ≤ 8 for at least two periods), sorted by the repeated word.  No proof reads anything it prints.

usage: lean --load-dynlib=cbuild/so/libBB6all.so --run CutShapes.lean 2199023255552 36 -/

def shapeOf (ss : List SMark) : String :=
  "G" ++ String.join (ss.map fun m => match m.t with | .G => "G" | .M => "M" | .W => "W" | .B => "B")

structure CAcc where
  final : Std.HashMap String Nat := {}
  periodic : Std.HashMap String Nat := {}
  sinceGMM : Array Nat := Array.replicate 41 0
  nGMM : Array Nat := Array.replicate 61 0
  cuts : Nat := 0

def bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat := m.insert k (m.getD k 0 + 1)

def CAcc.merge (a b : CAcc) : CAcc :=
  { final := b.final.fold bump' a.final, periodic := b.periodic.fold bump' a.periodic,
    sinceGMM := (a.sinceGMM.zip b.sinceGMM).map (fun (x, y) => x + y),
    nGMM := (a.nGMM.zip b.nGMM).map (fun (x, y) => x + y), cuts := a.cuts + b.cuts }
where bump' (m : Std.HashMap String Nat) (k : String) (v : Nat) := m.insert k (m.getD k 0 + v)

/-- The smallest rotation of a word, so that a cycle is named the same wherever the path enters it. -/
def normWord (w : List String) : String :=
  let rots := (List.range w.length).map fun i => " ".intercalate (w.drop i ++ w.take i)
  rots.foldl (fun a b => if b < a then b else a) (" ".intercalate w)

/-- The periodic stretch at the end of a history (newest first): the smallest period p ≤ 8 whose last 2p shapes
repeat. -/
def periodicTail (h : List String) : Option String :=
  (List.range 8).findSome? fun i =>
    let p := i + 1
    if h.length ≥ 2 * p && (List.range p).all (fun j => h[j]! == h[j + p]!) then
      some (normWord (h.take p).reverse) else none

def record (h : List String) (since g : Nat) (acc : CAcc) : CAcc :=
  { acc with final := bump acc.final (h.headD "?"),
             periodic := match periodicTail h with | some w => bump acc.periodic w | none => acc.periodic,
             sinceGMM := acc.sinceGMM.modify (min since 40) (· + 1),
             nGMM := acc.nGMM.modify (min g 60) (· + 1), cuts := acc.cuts + 1 }

partial def walk (Γ : Int) (fuel B : Nat) : Nat → Nat → Nat → Bool → List SMark → YForm → YForm → List YForm →
    List String → Nat → Nat → CAcc → CAcc
  | 0, _, _, _, ss, _, _, _, h, since, g, acc => record ((shapeOf ss :: h).take 24) since g acc
  | S + 1, d, nd, moved, ss, sW, w0, ts, h, since, g, acc =>
    if (moved && symClean1 ss sW && widerB sW w0 ts Γ) = true then acc else
    if cleanEntryOK Γ ts ss sW w0 = true then acc else
    let sh := shapeOf ss
    let record := fun (acc : CAcc) =>
      record ((sh :: h).take 24) (if sh == "GMM" then 0 else since) (if sh == "GMM" then g + 1 else g) acc
    match symRoundZ ts Γ fuel [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') =>
      walk Γ fuel B S d nd true ss' sW' w0 ts ((sh :: h).take 24) (if sh == "GMM" then 1 else since + 1)
        (if sh == "GMM" then g + 1 else g) acc
    | some _ => record acc
    | none =>
      match splitStep ts Γ ss sW with
      | none =>
        match nd, coneMin ts Γ with
        | nd + 1, some z =>
          if dropOK Γ fuel z ss sW w0 ts = true then
            walk Γ fuel B S d nd moved ss sW w0 [dropCone Γ z] h since g acc
          else record acc
        | _, _ => record acc
      | some (none, i) =>
        match d with
        | 0 => record acc
        | d + 1 =>
          let acc := walk Γ fuel B S d B moved (substL ss i 0) (sW.subst i 0) (w0.subst i 0) (substT ts i 0) h since g
            acc
          walk Γ fuel B S d B moved (substL ss i 1) (sW.subst i 1) (w0.subst i 1) (substT ts i 1) h since g acc
      | some (some (j, s), i) =>
        match d with
        | 0 => record acc
        | d + 1 =>
          let ss2 := shearL ss j s; let sW2 := sW.shear j s; let w02 := w0.shear j s; let ts2 := shearT ts j s
          let acc := walk Γ fuel B S d B moved (substL ss2 i 0) (sW2.subst i 0) (w02.subst i 0) (substT ts2 i 0) h since
            g acc
          walk Γ fuel B S d B moved (substL ss2 i 1) (sW2.subst i 1) (w02.subst i 1) (substT ts2 i 1) h since g acc

def top (m : Std.HashMap String Nat) (n : Nat) : List (String × Nat) :=
  (m.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take n

def main (args : List String) : IO Unit := do
  let Γ := (args.getD 0 "2199023255552").toNat!
  let d := (args.getD 1 "28").toNat!
  let e₀ := 8
  -- the top e₀ split levels; the rounds before them are counted again from each node, which only matters for the
  -- statistics of paths shorter than the prefix (none: the first split comes before the first two-marker state ends)
  let p := massPrefix Γ 1000 (cleanEntryOK Γ) cleanDrops (10000 + d) e₀ cleanDrops d false ctStart.1 ctStart.2.1
    ctStart.2.1 ctStart.2.2
  let tasks := p.2.map fun n => Task.spawn fun _ =>
    walk Γ 1000 cleanDrops n.S (d - e₀) n.nd n.moved n.ss n.sW n.w0 n.ts [] 0 0 {}
  let a := tasks.foldl (fun acc t => acc.merge t.get) ({} : CAcc)
  IO.println s!"Γ = {Γ}, d = {d}: cut leaves {a.cuts} (and {p.1.cuts} above split level {e₀})"
  IO.println "shape of the last round start:"
  for (k, c) in top a.final 12 do IO.println s!"  {k}: {c}"
  let hist := fun (a : Array Nat) => (a.toList.zipIdx.filter (·.1 > 0)).map fun (c, i) => (i, c)
  IO.println s!"rounds since the last two-marker state: {hist a.sinceGMM}"
  IO.println s!"two-marker states passed below split level {e₀}: {hist a.nGMM}"
  let np := a.periodic.fold (fun s _ v => s + v) 0
  IO.println s!"paths ending in a periodic stretch (period ≤ 8, two periods or more): {np}"
  for (k, c) in top a.periodic 12 do IO.println s!"  {c}: {k}"
