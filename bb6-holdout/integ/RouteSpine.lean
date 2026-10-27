import RouteEntryTheorem
open BB6 BB6.Sym

/-! # How many cut leaves lie below each cut class of the route tree (untrusted driver: statistics only)

The route tree with loop entries (`routeTreeE Γ d`) follows a two-marker state G 1, M m, M E − 2 with m and E free to
the next clean tape (one or two markers, so the next two-marker state too) or a loop entry that cannot close: one
segment of the two-marker reduction.  For every node after `b` splits that is cut with no split left, counts the cut
leaves of its subtree with `r` more splits.

usage: lean --load-dynlib=cbuild/so/libBB6all.so --run RouteSpine.lean 67108864 16 8 -/

structure RN where
  S : Nat
  moved : Bool
  ss : List SMark
  sW : YForm
  ts : List YForm

/-- Follow the exploration of `routeTreeE` through `e` splits; return the tally of the leaves met and the nodes. -/
partial def pre (Γ : Int) : Nat → Nat → Bool → List SMark → YForm → List YForm → List RN
  | S, 0, moved, ss, sW, ts => [⟨S, moved, ss, sW, ts⟩]
  | 0, _ + 1, _, _, _, _ => []
  | S + 1, e + 1, moved, ss, sW, ts =>
    if (moved && symClean ss sW) = true then [] else
    if entryOK Γ ts ss sW = true then [] else
    match symRoundZ ts Γ 1000 [] (YForm.const 1) ss sW with
    | some (.newRound ss' sW') => pre Γ S (e + 1) true ss' sW' ts
    | some _ => [⟨S + 1, moved, ss, sW, ts⟩]   -- a leaf that is cut at any depth (kept as a node)
    | none =>
      match splitStep ts Γ ss sW with
      | none => [⟨S + 1, moved, ss, sW, ts⟩]
      | some (none, i) =>
        pre Γ S e moved (substL ss i 0) (sW.subst i 0) (substT ts i 0) ++
          pre Γ S e moved (substL ss i 1) (sW.subst i 1) (substT ts i 1)
      | some (some (j, s), i) =>
        pre Γ S e moved (substL (shearL ss j s) i 0) ((sW.shear j s).subst i 0) (substT (shearT ts j s) i 0) ++
          pre Γ S e moved (substL (shearL ss j s) i 1) ((sW.shear j s).subst i 1) (substT (shearT ts j s) i 1)

def RN.mass (Γ : Int) (d : Nat) (n : RN) : ETally := exploreMassE Γ 1000 (entryOK Γ) n.S d 0 n.moved n.ss n.sW n.ts

def bucket (c : Nat) : Nat := if c ≤ 4 then c else Nat.log2 (c - 1) + 3

def main (args : List String) : IO Unit := do
  let Γ := (args.getD 0 "67108864").toNat!
  let base := (args.getD 1 "16").toNat!
  let r := (args.getD 2 "8").toNat!
  let top := pre Γ (10000 + base + r) 8 false rtStart.1 rtStart.2.1 rtStart.2.2
  let tasks := top.map fun n => Task.spawn fun _ =>
    (pre Γ n.S (base - 8) n.moved n.ss n.sW n.ts).filterMap fun m =>
      if (m.mass Γ 0).cuts = 0 then none else some (m.mass Γ r).cuts
  let res := tasks.foldl (fun (a : Array Nat) t => t.get.foldl (fun a c => a.modify (bucket c) (· + 1)) a)
    (Array.replicate 64 0)
  let total := res.foldl (· + ·) 0
  IO.println s!"route tree, Γ = {Γ}: cut classes after {base} splits: {total}; cut leaves below each {r} splits deeper:"
  for i in [0:64] do
    if res[i]! > 0 then
      let lbl := if i ≤ 4 then s!"{i}" else s!"{2 ^ (i - 3) + 1}..{2 ^ (i - 2)}"
      IO.println s!"  {lbl}: {res[i]!}"
