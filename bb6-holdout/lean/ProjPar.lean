import CleanEntryTheorem
import BB6.MassPar
open BB6 BB6.Sym

/-! # Do deeper trees close the open classes? (untrusted driver: statistics only)

Follows `cleanTreeGE Γ (b + r)` (the clean-tape tree with loop entries, as `RTree.exploreWE` builds it) to the nodes
reached after `b` splits, and for each of them asks two questions with `exploreMassWE`: is it cut in the tree of depth
`b` (it needs one more split, so it is one of the cut classes at b digits), and does its subtree still have a cut leaf
in the tree of depth b + r?  The top 8 split levels are followed by `massPrefix`, the nodes below them as parallel
tasks.  No proof reads anything it prints.

usage: lean --load-dynlib=cbuild/so/libBB6all.so --run ProjPar.lean 36 4 [Γ] -/

/-- For the nodes `e` more splits below `n`: how many there are, how many are cut with no split left, and how many of
those still have a cut leaf with `r` splits left. -/
partial def lvl (Γ : Nat) (r : Nat) : Nat → MNode → Nat × Nat × Nat
  | 0, n =>
    let t0 := MNode.mass Γ 1000 (cleanEntryOK Γ) cleanDrops 0 n
    if t0.cuts = 0 then (1, 0, 0) else
    let t := MNode.mass Γ 1000 (cleanEntryOK Γ) cleanDrops r n
    (1, 1, if t.cuts > 0 then 1 else 0)
  | e + 1, n =>
    let p := massPrefix Γ 1000 (cleanEntryOK Γ) cleanDrops n.S 1 n.nd n.D n.moved n.ss n.sW n.w0 n.ts
    p.2.foldl (fun (a : Nat × Nat × Nat) m => let b := lvl Γ r e m; (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2))
      (0, 0, 0)

def main (args : List String) : IO Unit := do
  let base := (args.getD 0 "36").toNat!
  let r := (args.getD 1 "4").toNat!
  let Γ := (args.getD 2 "2199023255552").toNat!
  let e₀ := 8
  let d := base + r
  let p := massPrefix Γ 1000 (cleanEntryOK Γ) cleanDrops (10000 + d) e₀ cleanDrops d false ctStart.1 ctStart.2.1
    ctStart.2.1 ctStart.2.2
  let tasks := p.2.map fun n => Task.spawn fun _ => lvl Γ r (base - e₀) n
  let res := tasks.foldl (fun (a : Nat × Nat × Nat) t => let b := t.get; (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2))
    (0, 0, 0)
  IO.println s!"Γ = {Γ}: nodes after {base} splits {res.1}, of which cut at depth {base}: {res.2.1}; of those, still \
    with a cut leaf at depth {d}: {res.2.2}"
