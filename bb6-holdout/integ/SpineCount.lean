import CleanEntryTheorem
import BB6.MassPar
open BB6 BB6.Sym

/-! # Below every open clean-tape class, the deeper tree keeps branching

`cleanTreeGE Γ d` (`../lean/thm/CleanEntryTheorem.lean`) is the clean-tape tree with loop entries; `MNode`,
`massPrefix` and `MNode.mass` (`../lean/BB6/MassPar.lean`) follow its exploration through a number of splits and
tally what lies below a node.  `spineCounts Γ b r` lists, for every node after `b` splits that needs another split
(a cut class of the tree of depth `b`), the number of cut leaves of its subtree with `r` more splits: the cut classes
of the tree of depth `b + r` inside that class.

If a class held only one 2-adic value of W/2 that no depth settles (an isolated limit point, such as the fixed point
of a loop, which a never-zero countdown would exclude for integers), its count would stay at 1 or 2 as `r` grows.
The theorems below say otherwise: apart from 2 of the 9,129 classes cut at 24 digits (which close by 36 digits), every
one has at least 42 cut classes 12 digits deeper; of the 1,706 classes cut at 20 digits, all but one have at least 238
16 digits deeper; of the 46,101 cut at 28 digits, all but 9 have at least 5 8 digits deeper.  So every open class
branches about as the whole tree does, and its 2-adic values that no depth settles form a Cantor set, not a point
(`INTEGRALITY.md`).

The numbers are evaluated by `native_decide`, as the measures in `../lean/thm/CleanEntryMass*.lean` are; no theorem
about the machine uses them.

usage (from `../lean`, after `check_end.sh` has built `out/` and the shared library):
  lean --load-dynlib=cbuild/so/libBB6all.so ../integ/SpineCount.lean -/

/-- For every node `e` more splits below `n` that needs another split, the number of cut leaves below it with `r`
splits. -/
def spineCounts (Γ r : Nat) : Nat → MNode → List Nat
  | 0, n =>
    if (MNode.mass Γ 1000 (cleanEntryOK Γ) cleanDrops 0 n).cuts = 0 then []
    else [(MNode.mass Γ 1000 (cleanEntryOK Γ) cleanDrops r n).cuts]
  | e + 1, n =>
    let p := massPrefix Γ 1000 (cleanEntryOK Γ) cleanDrops n.S 1 n.nd n.D n.moved n.ss n.sW n.w0 n.ts
    (p.2.map (spineCounts Γ r e)).flatten

/-- The cut leaves met above the split level `e` (none: every cut leaf of these trees is at full depth). -/
def earlyCuts (Γ : Nat) : Nat → MNode → Nat
  | 0, _ => 0
  | e + 1, n =>
    let p := massPrefix Γ 1000 (cleanEntryOK Γ) cleanDrops n.S 1 n.nd n.D n.moved n.ss n.sW n.w0 n.ts
    p.1.cuts + (p.2.map (earlyCuts Γ e)).sum

/-- The root of `cleanTreeGE Γ (b + r)` as an `MNode`. -/
def spineRoot (d : Nat) : MNode := ⟨10000 + d, cleanDrops, d, false, ctStart.1, ctStart.2.1, ctStart.2.1, ctStart.2.2⟩

/-- Count, how many are 0, smallest nonzero count, largest count. -/
def spineSummary (l : List Nat) : Nat × Nat × Nat × Nat :=
  (l.length, l.count 0, (l.filter (· ≠ 0)).foldl min (l.foldl max 0), l.foldl max 0)

/-- **The classes cut at 24 digits, 12 digits deeper.** `cleanTreeGE 2⁴¹ 24` has 9,129 cut classes (and no cut leaf
above depth 24); below 2 of them the tree of depth 36 has no cut leaf, below every other one it has between 42 and
304. -/
theorem spine_24_12 :
    (earlyCuts directWidth 24 (spineRoot 36),
      spineSummary (spineCounts directWidth 12 24 (spineRoot 36))) = (0, 9129, 2, 42, 304) := by
  native_decide

/-- **The classes cut at 20 digits, 16 digits deeper.** `cleanTreeGE 2⁴¹ 20` has 1,706 cut classes (and no cut leaf
above depth 20); below one of them the tree of depth 36 has no cut leaf, below every other one it has between 238 and
1,593. -/
theorem spine_20_16 :
    (earlyCuts directWidth 20 (spineRoot 36),
      spineSummary (spineCounts directWidth 16 20 (spineRoot 36))) = (0, 1706, 1, 238, 1593) := by
  native_decide

/-- **The classes cut at 28 digits, 8 digits deeper.** `cleanTreeGE 2⁴¹ 28` has 46,101 cut classes (and no cut leaf
above depth 28); below 9 of them the tree of depth 36 has no cut leaf, below every other one it has between 5 and
77. -/
theorem spine_28_8 :
    (earlyCuts directWidth 28 (spineRoot 36),
      spineSummary (spineCounts directWidth 8 28 (spineRoot 36))) = (0, 46101, 9, 5, 77) := by
  native_decide
