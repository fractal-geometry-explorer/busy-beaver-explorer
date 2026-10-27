import CleanEntryTheorem
import BB6.MassPar
open BB6 BB6.Sym

/-! # How many cut leaves lie below each cut class (untrusted driver: statistics only)

For every node of `cleanTreeGE Γ (b + r)` after `b` splits that is cut in the tree of depth `b`, counts the cut leaves
of its subtree with `r` more splits, and prints the histogram of these counts.  A class whose count stays 1 as r grows
is a single path (a spine); a count that grows with r is a branching subtree.

usage: lean --load-dynlib=cbuild/so/libBB6all.so --run SpineStats.lean 24 12 [Γ] -/

partial def lvl (Γ : Nat) (r : Nat) : Nat → MNode → List Nat
  | 0, n =>
    let t0 := MNode.mass Γ 1000 (cleanEntryOK Γ) cleanDrops 0 n
    if t0.cuts = 0 then [] else
    let t := MNode.mass Γ 1000 (cleanEntryOK Γ) cleanDrops r n
    [t.cuts]
  | e + 1, n =>
    let p := massPrefix Γ 1000 (cleanEntryOK Γ) cleanDrops n.S 1 n.nd n.D n.moved n.ss n.sW n.w0 n.ts
    p.2.foldl (fun a m => a ++ lvl Γ r e m) []

def bucket (c : Nat) : Nat := if c ≤ 4 then c else Nat.log2 (c - 1) + 3

def main (args : List String) : IO Unit := do
  let base := (args.getD 0 "24").toNat!
  let r := (args.getD 1 "12").toNat!
  let Γ := (args.getD 2 "2199023255552").toNat!
  let e₀ := 8
  let d := base + r
  let p := massPrefix Γ 1000 (cleanEntryOK Γ) cleanDrops (10000 + d) e₀ cleanDrops d false ctStart.1 ctStart.2.1
    ctStart.2.1 ctStart.2.2
  let tasks := p.2.map fun n => Task.spawn fun _ => lvl Γ r (base - e₀) n
  let res := tasks.foldl (fun (a : Array Nat) t => t.get.foldl (fun a c => a.modify (bucket c) (· + 1)) a)
    (Array.replicate 64 0)
  let total := res.foldl (· + ·) 0
  IO.println s!"Γ = {Γ}: cut classes at depth {base}: {total}; cut leaves below each at depth {d}:"
  for i in [0:64] do
    if res[i]! > 0 then
      let lbl := if i ≤ 4 then s!"{i}" else s!"{2 ^ (i - 3) + 1}..{2 ^ (i - 2)}"
      IO.println s!"  {lbl}: {res[i]!}"
