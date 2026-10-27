import CleanTheorem
import RouteTheorem
open BB6 BB6.Sym

/-! # Running the explorer (untrusted driver: statistics and tree files only)

The theorems use the proved explorer of `BB6/RouteExplore.lean` directly (`cleanTree d` in `thm/CleanTheorem.lean`,
`routeTree Γ d` in `thm/RouteTheorem.lean`); no file this driver writes is read by any proof.  It builds the same tree
and prints what it looks like: the leaf counts, the cut measure, the longest path in rounds, and the cut leaves above
the full depth (where a round could not be decided by a residue split, for example an undecided order test), and it
can write the tree, one token per node: `C` cut, `K` clean, `A`n n rounds, `S`i split on coordinate i, `H`i`,`s
shear.

usage (after `check_end.sh` has built the shared library and the theorem files):
  lean --load-dynlib=cbuild/so/libBB6all.so --run RouteStats.lean clean 4294967296 36 [tree.txt]
  lean --load-dynlib=cbuild/so/libBB6all.so --run RouteStats.lean route 8000000 36 [tree.txt]
(`clean` Γ d is `cleanTreeG Γ d`: Γ = 2³² is `cleanTree d`, Γ = 2⁴¹ the tree of `thm/EndToEndDirect.lean`.) -/

/-- Merge runs of rounds: `adv 1 (adv 1 t)` becomes `adv 2 t`. -/
def merge : RTree → RTree
  | .adv n t => match merge t with
    | .adv m u => .adv (n + m) u
    | u => .adv n u
  | .split i t0 t1 => .split i (merge t0) (merge t1)
  | .shear i s t => .shear i s (merge t)
  | t => t

/-- The cut leaves above depth `D`: (depth, rounds on the path), and the most rounds on any path. -/
def scan (D : Nat) : RTree → Nat → Nat → List (Nat × Nat) × Nat
  | .cut, d, r => (if d < D then [(d, r)] else [], r)
  | .clean, _, r => ([], r)
  | .adv n t, d, r => scan D t d (r + n)
  | .split _ t0 t1, d, r =>
    let (a, ra) := scan D t0 (d + 1) r
    let (b, rb) := scan D t1 (d + 1) r
    (a ++ b, max ra rb)
  | .shear _ _ t, d, r => scan D t d r

def ser : RTree → Array String → Array String
  | .cut, acc => acc.push "C"
  | .clean, acc => acc.push "K"
  | .adv n t, acc => ser t (acc.push ("A" ++ toString n))
  | .split i t0 t1, acc => ser t1 (ser t0 (acc.push ("S" ++ toString i)))
  | .shear i s t, acc => ser t (acc.push ("H" ++ toString i ++ "," ++ toString s))

def main (args : List String) : IO Unit := do
  let kind := args.getD 0 "clean"
  let Γ := (args.getD 1 "4294967296").toNat!
  let d := (args.getD 2 "24").toNat!
  let t := merge (if kind == "route" then routeTree Γ d else cleanTreeG Γ d)
  let (ncut, nclean) := t.leaves
  let mass := t.cutMass d
  IO.println s!"{kind} tree, depth {d}, Γ = {Γ}: leaves cut {ncut}, clean {nclean}"
  IO.println s!"cut measure {mass} / 2^{d} = {mass.toFloat / (2 ^ d : Nat).toFloat}"
  let (early, rmax) := scan d t 0 0
  IO.println s!"most rounds on a path {rmax}; cut leaves above depth {d}: {early.length}"
  for (dd, r) in early.take 20 do IO.println s!"  cut at depth {dd} after {r} rounds"
  if let some (out : String) := args[3]? then
    IO.FS.writeFile out (" ".intercalate (ser t #[]).toList)
    IO.println s!"wrote {out}"
