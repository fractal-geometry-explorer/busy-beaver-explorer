import Run7

/-!
# Few large blocks do not help: orbit-shaped lists that reach a first block of 1

The idea tested here (`notes/LAB_NOTES.md`, 1 November, "Bound the number of large blocks"): along the orbit, beyond
three or four blocks the extra blocks are a tail of small ones, so a bound on the number of *large* blocks, with ψ,
might rule out the halving runs of `Run7.lean`, whose lists `w7`, `w7b` have all seven blocks of comparable size.

It does not. A list keeps its ψ when `2^M · v` is added with `ψ v = 0`, and for `M = 8` the passes keep their stop
blocks along these runs. With `v = [0, 993, 3400, 3300, 1000, 128, 32]` (first block first, ψ v = 0) the lists of
`Run7.lean` take the orbit's shape, a bulk of about `[1, 3.4, 3.3, 1]` with a small tail:

    wL  = [31, 254304, 870464, 844832, 256088, 32930, 8427]          (ones 2,267,076)
    wLb = [255, 255488, 872704, 847232, 261464, 43362, 14699]        (ones 2,295,204)

Both have ψ = −57, 4 | ones, `Good`, and a first block 2^R − 1 that is only halved until a pass stops at a first block
of 1 (`wL_one`, `wLb_one`, the only way the machine halts, `halts_only_by_one`). At every pass start on the way,
at most 5 blocks are at least ones/32 and at most 5 at least ones/16 (`wL_large`, `wLb_large`): the orbit itself
reaches 5 at both thresholds (pass 269,207 and pass 1,525,466, computed). So a bound on the number of large blocks
that the orbit satisfies, together with ψ, `Good`, 4 | ones and `front_twice`, does not exclude the event.

What these lists do not share with the orbit is the size of the first block: 31 is 1.4·10⁻⁵ of the ones, where the
orbit keeps its first block above 0.7% of the ones after pass 50 (computed, `py/front.py`). Kernel only.
-/

namespace BB6d

/-- The number of blocks of `zs` that are at least `1/2^c` of its ones. -/
def large (c : Nat) (zs : List Nat) : Nat := (zs.filter (fun x => zs.sum ≤ 2 ^ c * x)).length

/-- The first block (`getLast?`, lists are nearest first), the block count and the large blocks at ones/16 and
ones/32, at each of the first `n` pass starts from `zs`. -/
def profile (n : Nat) (zs : List Nat) : List (Nat × Nat × Nat × Nat) :=
  (List.range n).map fun i =>
    match run i zs with
    | .ok ys => (ys.getLast?.getD 0, ys.length, large 4 ys, large 5 ys)
    | _ => (0, 0, 0, 0)

/-- `[31, 254304, 870464, 844832, 256088, 32930, 8427]` (first block first): `w7` plus `2^8 · v`. -/
def wL : List Nat := [8427, 32930, 256088, 844832, 870464, 254304, 31]

theorem wL_from_w7 : wL = List.zipWith (fun a b => a + 2 ^ 8 * b) w7 [32, 128, 1000, 3300, 3400, 993, 0] := by
  decide
theorem wL_psi : psi wL = -57 := by decide
theorem wL_sum : wL.sum % 4 = 0 := by decide
theorem wL_good : Good wL := by
  simp only [wL, Good]; decide
theorem wL_first : wL.getLast? = some (2 ^ 5 - 1) := by decide

/-- Nine passes: the first block runs 31, 15, 7, 3, 1 on 7 and 8 blocks, with at most 5 large blocks. -/
theorem wL_large : profile 9 wL =
    [(31, 7, 4, 4), (15, 8, 4, 5), (15, 7, 4, 5), (7, 8, 4, 5), (7, 7, 4, 5), (3, 8, 5, 5), (3, 7, 4, 4),
     (1, 8, 4, 5), (1, 7, 3, 4)] := by decide

/-- The ninth pass stops at a first block of 1. -/
theorem wL_one : run 9 wL = .one := by decide

/-- `[255, 255488, 872704, 847232, 261464, 43362, 14699]` (first block first): `w7b` plus `2^8 · v`. -/
def wLb : List Nat := [14699, 43362, 261464, 847232, 872704, 255488, 255]

theorem wLb_from_w7b : wLb = List.zipWith (fun a b => a + 2 ^ 8 * b) w7b [32, 128, 1000, 3300, 3400, 993, 0] := by
  decide
theorem wLb_psi : psi wLb = -57 := by decide
theorem wLb_sum : wLb.sum % 4 = 0 := by decide
theorem wLb_good : Good wLb := by
  simp only [wLb, Good]; decide

/-- Nineteen passes: the first block 255 is only halved, the count falls from 7 to 3, at most 5 large blocks. -/
theorem wLb_large : profile 19 wLb =
    [(255, 7, 4, 4), (127, 8, 4, 5), (127, 7, 4, 5), (63, 8, 4, 5), (63, 7, 4, 5), (31, 8, 5, 5), (31, 7, 4, 4),
     (15, 8, 4, 5), (15, 7, 3, 4), (7, 8, 3, 4), (7, 7, 3, 3), (3, 8, 4, 4), (3, 7, 3, 3), (3, 6, 3, 3),
     (3, 5, 2, 2), (1, 6, 3, 3), (1, 5, 3, 3), (1, 4, 3, 3), (1, 3, 2, 2)] := by decide

/-- The nineteenth pass stops at a first block of 1. -/
theorem wLb_one : run 19 wLb = .one := by decide

end BB6d
