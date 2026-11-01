import Seven
import Front

/-!
# With seven blocks, ψ does not bound the halvings of the first block

The first block changes only at a few kinds of pass (a stop at the second block, a stop at the third block of a
longer list, an even last block on two or three blocks). Between two such passes it is only halved, by front stops,
and a stop at a first block of 1 at the end of R halvings needs the first block to have been 2^R − 1 (the Mersenne
lemma, `notes/LAB_NOTES.md`). On lists of at most 6 blocks, ψ (`psi_next`, PR "the ψ rule") together with
`front_twice` bounds R by a finite graph. This file shows that the same bound fails as soon as a run of such passes
starts on 7 blocks, for a list that also satisfies every other known invariant of the orbit:

    w7 = [31, 96, 64, 32, 88, 162, 235]      (first block first; Lean's lists are nearest first)

has ψ = −57 (inside the range the 7-block excursion of `Seven.lean` shows, ψ = −56), 4 | ones, every block after
the first at least 2 (`Good`), y₂ ≥ y₁ + 2, and first block 31 = 2^5 − 1. Its next 8 passes alternate a front stop
(7 → 8 blocks) and a pass that leaves the first block alone (8 → 7 blocks), so the first block runs 31, 15, 7, 3, 1,
and the ninth pass is a front stop at a block of 1 (`run 9 w7 = .one`), the only way the machine can halt
(`halts_only_by_one`). Kernel only.

The route in (k, ψ) is the cycle of the (k, ψ, f) graph on 7 and 8 blocks, (7, −57) → (8, 121) → (7, −67) → … → (7, −57),
which repeats for ever in the graph, so the graph gives no bound at all on R once 7 blocks occur at a change.
-/

namespace BB6d

/-- The alternating sum, nearest block first: the same fold as `psi` in `Psi.lean`. -/
def alt : List Nat → Int
  | [] => 0
  | y :: ys => (y : Int) - 2 * alt ys

/-- `[31, 96, 64, 32, 88, 162, 235]`, nearest block first. -/
def w7 : List Nat := [235, 162, 88, 32, 64, 96, 31]

theorem w7_alt : alt w7 = -57 := by decide
theorem w7_sum : w7.sum % 4 = 0 := by decide
theorem w7_first : w7.getLast? = some (2 ^ 5 - 1) := by decide
theorem w7_second : w7[5]! ≥ w7[6]! + 2 := by decide
theorem w7_good : Good w7 := by
  simp only [w7, Good]; decide

/-- The first block and the block count after each of the first 9 passes: the first block is only halved. -/
def trace7 : List (Option Nat × Nat) :=
  (List.range 9).map fun n =>
    match run n w7 with
    | .ok zs => (zs.getLast?, zs.length)
    | _ => (none, 0)

theorem w7_trace : trace7 =
    [(some 31, 7), (some 15, 8), (some 15, 7), (some 7, 8), (some 7, 7), (some 3, 8), (some 3, 7), (some 1, 8),
     (some 1, 7)] := by decide

/-- The ninth pass stops at a first block of 1. -/
theorem w7_one : run 9 w7 = .one := by decide

/-- A longer run, 8 front stops: `[255, 1280, 2304, 2432, 5464, 10594, 6507]`, nearest block first. Same ψ, same
cycle of the (k, ψ) graph, first block 255 = 2^8 − 1. -/
def w7b : List Nat := [6507, 10594, 5464, 2432, 2304, 1280, 255]

theorem w7b_alt : alt w7b = -57 := by decide
theorem w7b_sum : w7b.sum % 4 = 0 := by decide
theorem w7b_good : Good w7b := by
  simp only [w7b, Good]; decide
theorem w7b_one : run 15 w7b = .one := by decide

/-- Its first blocks: 255, 127, 63, …, 1, only halved. -/
theorem w7b_firsts : (List.range 15).map (fun n =>
    match run n w7b with
    | .ok zs => zs.getLast?.getD 0
    | _ => 0) = [255, 127, 127, 63, 63, 31, 31, 15, 15, 7, 7, 3, 3, 1, 1] := by decide

end BB6d

namespace BB6d

/-- **A front stop adds one to `y₂ / (y₁ + 1)`.** On a front stop of at least three blocks, the first block `f`
becomes `(f − 1)/2` and the second `e` becomes `(f + 1)/2 + e/2`, so `y₂' / (y₁' + 1) = y₂ / (y₁ + 1) + 1` exactly.
(Nearest first: `zs = b :: (es ++ [e, f])`.) -/
theorem front_second (b e f : Nat) (es : List Nat) (hb : b % 2 = 1) (hes : ∀ x ∈ es, x % 2 = 0 ∧ 0 < x)
    (he : e % 2 = 0) (he0 : 0 < e) (hf : f % 2 = 1) (hf1 : f ≠ 1) :
    ∃ xs, next (b :: (es ++ [e, f])) = .ok (xs ++ [(f + 1) / 2 + e / 2, (f - 1) / 2]) := by
  have hpe : ∀ x ∈ es ++ [e], x % 2 = 0 ∧ 0 < x := by
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hes x hx
    · exact ⟨he, he0⟩
  have hl : es ++ [e, f] = (es ++ [e]) ++ [f] := by simp
  rw [next, if_neg (by omega), hl, sweep_evens f hf (es ++ [e]) _ hpe, if_neg hf1]
  simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append]
  refine ⟨zag (e / 2 - 1) [] ((es.map (fun x => x / 2 - 1)).reverse ++ [(b + 3) / 2]), ?_⟩
  show Next.ok (zag (e / 2 - 1) [((f - 1) / 2 + (e / 2 - 1) + 2), (f - 1) / 2] _) = _
  rw [zag_app]
  have : (f - 1) / 2 + (e / 2 - 1) + 2 = (f + 1) / 2 + e / 2 := by omega
  rw [this]

end BB6d
